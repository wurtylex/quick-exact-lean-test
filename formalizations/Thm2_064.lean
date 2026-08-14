import Mathlib

namespace Agent064

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We work with vectors `ℝ^n` encoded as `Fin n → ℝ`.

## Modelling choices

* An affine transformation `ℝ^a → ℝ^b` is given by a matrix `A : Matrix (Fin b) (Fin a) ℝ`
  and a bias vector `c : Fin b → ℝ`, computing `x ↦ A x + c`.
* A ReLU network with `k` hidden layers and input dimension `n` is encoded as a list `L` of
  `k + 1` such affine layers (matching the `k + 1` affine transformations
  `T^(1), ..., T^(k+1)` in the paper), where ReLU is applied componentwise after every layer
  *except* the last one. The layers carry their own declared input/output dimensions; a
  network is only considered to *represent* `f` if these dimensions actually chain together
  correctly starting from `n` and ending at `1` (see `isRepresented` / `evalLayers` below).
  We use the "exactly `k` hidden layers" reading of `ReLU_{n,k}`: since layer widths are
  otherwise unconstrained, a network with fewer hidden layers can always be padded to one
  with more (e.g. via an extra identity-simulating layer `y = ReLU(y) - ReLU(-y)`), so this
  reading coincides with "at most `k`" and is the more literal reading of "representable with
  `k` hidden layers".
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of affine
  functions such that every point has an open neighbourhood on which `f` coincides with one
  member of the family. This is a genuine local-piecewise-affinity condition, not a
  max-of-affine normal form and not "representable by some network".
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded using `Real.logb 3` and `Nat.ceil` (`⌈·⌉₊`).
-/

/-- ReLU on `ℝ`. -/
def reluR (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluV {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => reluR (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, i.e. `x ↦ A x + c`. -/
structure Affine (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def Affine.eval {a b : ℕ} (T : Affine a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, T.A i j * x j) + T.c i

/-- A single layer of a ReLU network: an affine map together with its declared input and
output dimensions. -/
structure Layer where
  inDim : ℕ
  outDim : ℕ
  map : Affine inDim outDim

/-- Evaluate a list of layers as the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ... ∘ ReLU ∘ T^(1)`, i.e. ReLU is applied after every layer except
the last one in the list. The input/output vectors are dimension-tagged (`Σ'`-packaged) so
that the definition is total; if a layer's declared input dimension does not match the
actual incoming dimension, evaluation returns a dummy `0`-dimensional value (this can never
match a genuine `1`-dimensional output, so it never causes a network with mismatched
dimensions to spuriously "represent" a function). -/
def evalLayers : List Layer → (Σ' a : ℕ, Fin a → ℝ) → (Σ' b : ℕ, Fin b → ℝ)
  | [], v => v
  | (T :: []), ⟨a', x⟩ =>
      if h : a' = T.inDim then
        ⟨T.outDim, T.map.eval (h ▸ x)⟩
      else
        ⟨0, fun i => i.elim0⟩
  | (T :: T2 :: rest), ⟨a', x⟩ =>
      if h : a' = T.inDim then
        evalLayers (T2 :: rest) ⟨T.outDim, reluV (T.map.eval (h ▸ x))⟩
      else
        ⟨0, fun i => i.elim0⟩

/-- `f : ℝ^n → ℝ` is computed (represented) by a ReLU network with exactly `k` hidden
layers, i.e. there is a list of `k + 1` affine layers whose alternating ReLU-composition,
started from the actual input dimension `n`, computes `f` and ends in dimension `1`. -/
def isRepresented (n k : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ L : List Layer, L.length = k + 1 ∧
    ∀ x : Fin n → ℝ, evalLayers L ⟨n, x⟩ = (⟨1, fun _ => f x⟩ : Σ' b : ℕ, Fin b → ℝ)

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
exactly `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) := {f | isRepresented n k f}

/-- `f` is affine on `ℝ^n` with coefficients `a` and intercept `b`. -/
def IsAffineWith (n : ℕ) (a : Fin n → ℝ) (b : ℝ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ y, f y = (∑ j, a j * y j) + b

/-- `CPWL n`: the continuous, piecewise-linear functions `ℝ^n → ℝ`. We require continuity
together with the existence of a *finite* family of affine functions such that every point
of `ℝ^n` has an open neighbourhood on which `f` agrees with one member of the family. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (a : Fin m → (Fin n → ℝ)) (b : Fin m → ℝ),
      ∀ x : Fin n → ℝ, ∃ i : Fin m, ∃ U : Set (Fin n → ℝ),
        IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, f y = (∑ j, a i j * y j) + b i}

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from Theorem 2, with `n - 1` taken as a natural
number (valid since `n ≥ 3` in the theorem, so `n - 1 ≥ 2`). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n - 1 : ℕ) : ℝ)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent064

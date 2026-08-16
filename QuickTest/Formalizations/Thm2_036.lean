import Mathlib

namespace Agent036

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):

  For n ≥ 3,  CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}.

## Modelling choices

* `ℝ^n` is encoded as `Fin n → ℝ`.
* An affine map `ℝ^a → ℝ^b` is a matrix `A : Matrix (Fin b) (Fin a) ℝ` together with a
  bias vector `c : Fin b → ℝ`, evaluated as `x ↦ A.mulVec x + c`.
* A ReLU network with `k` hidden layers computing `f : ℝ^n → ℝ` is defined recursively
  (`NetOutput`): with `0` hidden layers it is a single affine map `ℝ^n → ℝ`; with `k+1`
  hidden layers it is an affine map `ℝ^n → ℝ^m` followed by a componentwise ReLU, feeding
  into a function computed by a `k`-hidden-layer network on `ℝ^m`. This literally unwinds
  the alternating composition `T^(k+1) ∘ ReLU ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper.
* `ReLUn n k` is the set of functions representable with **at most** `k` hidden layers
  (i.e. `∃ j ≤ k`, exactly `j` hidden layers suffice). This is the reading that makes
  Theorem 2 true: since one can always pad a network with extra layers implementing the
  identity (e.g. `x ↦ relu(x) - relu(-x)`), the "exactly k" and "at most k" classes
  coincide for `k ≥ 1`, but "at most k" is the natural monotone notion intended by the
  inclusion `ReLU_{n,k} ⊆ ReLU_{n,k+1}` implicit in the paper's depth hierarchy.
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of affine
  functions `ℝ^n → ℝ` such that every point of `ℝ^n` has a neighbourhood on which `f`
  coincides with one member of the family. This is a genuine local piecewise-linearity
  condition (not "representable by a ReLU network", and not a max-of-affines normal
  form).
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded with the real logarithm `Real.logb 3`
  and `Nat.ceil`.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given by a matrix and a bias vector. -/
structure Affine (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation: `x ↦ A x + c`. -/
def Affine.eval {a b : ℕ} (T : Affine a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `NetOutput n k f` means `f : ℝ^n → ℝ` is computed by a ReLU network with exactly `k`
hidden layers, i.e. `f = T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` for some affine maps
`T^(1), …, T^(k+1)` of matching dimensions. Defined by recursion on `k`: with `0` hidden
layers the network is just a single affine map, and with `k+1` hidden layers we peel off
the first affine map `T^(1) : ℝ^n → ℝ^m`, apply ReLU, and feed the result into a
`k`-hidden-layer network on `ℝ^m`. -/
def NetOutput : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : Affine n 1, ∀ x, f x = T.eval x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : Affine n m) (g : (Fin m → ℝ) → ℝ),
        NetOutput m k g ∧ ∀ x, f x = g (reluVec (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
**at most** `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ j, j ≤ k ∧ NetOutput n j f}

/-- The space of continuous piecewise linear functions `ℝ^n → ℝ`: `f` is continuous, and
there is a finite family of affine functions such that every point has a neighbourhood on
which `f` agrees with one member of the family. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (g : Fin m → ((Fin n → ℝ) → ℝ)),
      (∀ i, ∃ T : Affine n 1, ∀ x, g i x = T.eval x 0) ∧
      ∀ x : Fin n → ℝ, ∃ i, ∃ U ∈ nhds x, ∀ y ∈ U, f y = g i y}

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from the paper, as a natural number. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent036

import Mathlib

namespace Agent092

/-!
# Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity: Subdividing the Simplex")

We formalize:  for `n ≥ 3`,  `CPWL n = ReLUn n (⌈log_3 (n-1)⌉ + 1)`.

## Modelling choices

* `ℝ^n` is encoded as `Fin n → ℝ`.
* An affine map `ℝ^a → ℝ^b` is a pair `(A, c)` with `A : Matrix (Fin b) (Fin a) ℝ` and
  `c : Fin b → ℝ`, evaluated as `x ↦ A.mulVec x + c`.
* A "ReLU network with exactly `k` hidden layers" from `ℝ^a` to `ℝ` is encoded as an
  inductive chain `NetworkChain a k`: either a single affine map `a → 1` (0 hidden
  layers), or an affine map `a → b` followed by `ReLU` and a chain of length `k` from
  `b` (giving `k + 1` hidden layers). This literally mirrors the alternating
  composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper.
* `ReLUn n k` is the set of functions representable by *some* `NetworkChain n k`, i.e.
  representable with **exactly** `k` hidden layers (the literal reading of the paper's
  "the subset of CPWL_n representable with k hidden layers").
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of affine
  functions `ℝ^n → ℝ` such that every point has a neighborhood on which `f` coincides
  with one member of the family. This is a genuine local-piecewise-affine condition,
  not a max-of-affine normal form and not "representable by a ReLU network".
* The depth bound `⌈log_3 (n-1)⌉ + 1` is encoded with `Real.logb 3` and `Nat.ceil`.
-/

/-- The scalar ReLU function. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given by a matrix and a translation vector. -/
def AffineMap (a b : ℕ) : Type := Matrix (Fin b) (Fin a) ℝ × (Fin b → ℝ)

/-- Evaluate an affine transformation. -/
def affineEval {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.1.mulVec x + T.2

/-- An affine *function* `ℝ^n → ℝ` (an affine map into `ℝ^1`, read off at the unique
coordinate). -/
def AffineFunc (n : ℕ) : Type := AffineMap n 1

/-- Evaluate an affine function. -/
def AffineFunc.eval {n : ℕ} (g : AffineFunc n) (x : Fin n → ℝ) : ℝ :=
  affineEval g x 0

/-- `NetworkChain a k` encodes the data of a ReLU network computing a function
`ℝ^a → ℝ` with exactly `k` hidden layers, i.e. the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations
`T^(1), …, T^(k+1)` with componentwise `ReLU` in between. -/
inductive NetworkChain : ℕ → ℕ → Type where
  /-- Zero hidden layers: a single affine map `a → 1`. -/
  | last {a : ℕ} (T : AffineMap a 1) : NetworkChain a 0
  /-- One more hidden layer: an affine map `a → b`, then `ReLU`, then a chain of
  length `k` on `ℝ^b`. -/
  | cons {a b k : ℕ} (T : AffineMap a b) (rest : NetworkChain b k) : NetworkChain a (k + 1)

/-- The function `ℝ^a → ℝ` computed by a `NetworkChain`. -/
def NetworkChain.eval : {a k : ℕ} → NetworkChain a k → (Fin a → ℝ) → ℝ
  | _, _, .last T, x => affineEval T x 0
  | _, _, .cons T rest, x => rest.eval (reluVec (affineEval T x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
**exactly** `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ c : NetworkChain n k, f = c.eval}

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: `f` is
continuous, and there is a finite family of affine functions such that `f` agrees with
one of them on a neighborhood of every point. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (g : Fin m → AffineFunc n), ∀ x : Fin n → ℝ, ∃ i : Fin m,
      ∀ᶠ y in nhds x, f y = (g i).eval y}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from the theorem, for `n ≥ 3` (so `n - 1 ≥ 2`
as a real number). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent092

import Mathlib

namespace Agent070

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex").

Modelling choices:
* Vectors `ℝ^n` are encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is encoded concretely as a pair `(A, c)` of a
  matrix and a bias vector, evaluating to `x ↦ A *ᵥ x + c`.
* A ReLU network with `k` hidden layers computing `f : (Fin n → ℝ) → ℝ` is encoded via
  the inductive relation `NetworkComputes n k f`, which directly mirrors the alternating
  composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper: the base case
  `k = 0` is a single affine map `n → 1` (no ReLU, one affine transformation, matching
  "depth 1 / 0 hidden layers"), and the inductive step peels off the first affine map
  `T^(1) : n → m`, applies `ReLU` componentwise, and feeds the result into a network with
  one fewer hidden layer.
* `ReLUn n k` is taken to be the functions representable with **at most** `k` hidden
  layers (`∃ j ≤ k`), not *exactly* `k`. This is the reading under which `ReLUn n k` is
  monotone in `k` (a hierarchy) and under which Theorem 2's equality
  `CPWL n = ReLUn n (depthBound n)` can hold as an equality of sets: with the "exactly k"
  reading, functions representable with fewer than `depthBound n` layers (e.g. any affine
  function, representable with `0` hidden layers) would be wrongly excluded from the
  right-hand side.
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of affine
  functions such that every point of `ℝ^n` has a neighbourhood on which `f` coincides
  with one member of the family (a genuine local piecewise-linearity / polyhedral-pieces
  condition, not a max-of-affine normal form and not "representable by some network").
* The depth bound `⌈log_3 (n - 1)⌉ + 1` is encoded using the real logarithm
  `Real.logb 3` together with `Nat.ceil`, applied to the real number `(n : ℝ) - 1`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias
vector. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation: `x ↦ A x + c`. -/
def AffineMap.eval {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (T.A.mulVec x) i + T.c i

/-- `NetworkComputes n k f` says that `f : ℝ^n → ℝ` is computed by a ReLU network with
`k` hidden layers, i.e. by an alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations with
componentwise `ReLU` in between, the last transformation landing in `ℝ^1`.

The base case `k = 0` is a single affine transformation `ℝ^n → ℝ^1` with no `ReLU`
applied (a network with `0` hidden layers / depth `1`). The successor case peels off the
first affine transformation `T^(1) : ℝ^n → ℝ^m`, applies `ReLU` componentwise, and
requires the rest of the network (on the remaining `j` hidden layers) to compute the
resulting function of the `ReLU`'d intermediate vector. -/
inductive NetworkComputes : (n : ℕ) → (k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | base (n : ℕ) (T : AffineMap n 1) :
      NetworkComputes n 0 (fun x => T.eval x 0)
  | step (n m j : ℕ) (T : AffineMap n m) (g : (Fin m → ℝ) → ℝ)
      (hg : NetworkComputes m j g) :
      NetworkComputes n (j + 1) (fun x => g (reluVec (T.eval x)))

/-- `ReLUn n k`: the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ j, j ≤ k ∧ NetworkComputes n j f }

/-- An affine (degree-`≤ 1` polynomial) function `ℝ^n → ℝ`. -/
def IsAffine {n : ℕ} (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x : Fin n → ℝ, g x = (∑ i, a i * x i) + b

/-- `CPWL n`: the set of continuous, piecewise-linear functions `ℝ^n → ℝ`, i.e.
continuous functions `f` for which there is a *finite* family of affine functions such
that every point `x` has a neighbourhood on which `f` agrees with one member of the
family. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (g : Fin m → ((Fin n → ℝ) → ℝ)),
          (∀ i, IsAffine (g i)) ∧
          ∀ x : Fin n → ℝ, ∃ i, ∀ᶠ y in nhds x, f y = g i y }

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so `n - 1 ≥ 2`). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3 (n - 1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent070

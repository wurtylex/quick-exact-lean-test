import Mathlib

namespace Agent048

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We model `ℝ^n` as `Fin n → ℝ`. An affine transformation `ℝ^a → ℝ^b` is given
concretely by a matrix and a bias vector, `x ↦ A * x + c`. A ReLU network with
`k` hidden layers computing `f : ℝ^n → ℝ` is modelled by the recursive relation
`Computes k n f`, built by peeling off the first affine map and the ReLU that
follows it. `ReLUn n k` is the set of functions computable with *at most* `k`
hidden layers (the standard convention for these depth-separation results,
matching monotonicity `ReLUn n k ⊆ ReLUn n (k+1)`). `CPWL n` is defined as:
continuous, and locally (in a neighbourhood of every point) equal to one of
finitely many affine functions -- a genuine piecewise-linear condition, not
phrased via ReLU networks or via a max-of-affine normal form.
-/

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a
bias vector: `x ↦ A * x + c`. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluate an affine transformation at a point. -/
noncomputable def AffineMap.eval {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) :
    Fin b → ℝ :=
  fun i => (∑ j, T.A i j * x j) + T.c i

/-- The ReLU function `max 0 ·` on `ℝ`, applied componentwise to a vector. -/
noncomputable def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => max 0 (x i)

/-- `Computes k n f` means `f : ℝ^n → ℝ` is computed by a ReLU network with
exactly `k` hidden layers, i.e. by an alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations
with componentwise ReLU applications in between. The base case `k = 0` is a
single affine map with no ReLU (depth `1`, `0` hidden layers); the recursive
case peels off the first affine map `T^(1) : ℝ^n → ℝ^m` and the following
ReLU, leaving a network with `k` hidden layers computing `g : ℝ^m → ℝ`. -/
def Computes : (k : ℕ) → (n : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | 0, n, f => ∃ T : AffineMap n 1, ∀ x, f x = T.eval x 0
  | (k + 1), n, f =>
      ∃ (m : ℕ) (T : AffineMap n m) (g : (Fin m → ℝ) → ℝ),
        Computes k m g ∧ ∀ x, f x = g (reluVec (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU
network with *at most* `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, Computes k' n f }

/-- A function `ℝ^n → ℝ` is affine if it has the form `x ↦ a ⬝ x + b`. -/
def IsAffineFun {n : ℕ} (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x, g x = (∑ i, a i * x i) + b

/-- `CPWL n` is the space of continuous, piecewise linear functions
`ℝ^n → ℝ`: `f` is continuous, and there is a finite family of affine
functions `g 1, ..., g m` such that every point `x` has a neighbourhood on
which `f` coincides with (at least) one of the `g i`. This is a genuine
polyhedral-subdivision-style piecewise-linearity condition, independent of
any ReLU-network representation and independent of any max-of-affine normal
form. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ),
          (∀ i, IsAffineFun (g i)) ∧
          ∀ x : Fin n → ℝ, ∃ i, ∀ᶠ y in nhds x, f y = g i y }

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, for `n ≥ 3`
(so `n - 1 ≥ 2 > 0`, and the real logarithm base `3` is well-defined and
positive here). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent048

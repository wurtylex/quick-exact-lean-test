import Mathlib

namespace Agent002

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

Modelling choices (see summary at the end of the task for more detail):
* Vectors `ℝ^n` are encoded as `Fin n → ℝ` (a finite Pi type), which already carries the
  Mathlib Pi (sup) metric/topology instances needed for continuity and locality below.
* Affine maps `ℝ^a → ℝ^b` are given concretely as a matrix `A` plus a bias vector `c`,
  `x ↦ A.mulVec x + c`.
* A ReLU network with `k` hidden layers is modelled by the recursively-defined predicate
  `ComputesWithHiddenLayers n k f`, unwinding exactly the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper, with **exactly** `k` ReLU
  layers (this is the literal reading of the paper's definition; padding with an extra
  layer computing the identity via `ReLU(x) - ReLU(-x) = x` shows `ReLUn n k ⊆ ReLUn n (k+1)`
  so the "exactly k" and "at most k" readings agree on which sets appear as `ReLUn n K`
  for `K` large enough, but "exactly k" is what the source text literally defines).
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of affine
  functions such that every point of `ℝ^n` has a neighbourhood on which `f` coincides with
  one member of the family (this is the "finite family of affine functions that `f`
  locally agrees with" option suggested by the task spec).
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined via the real logarithm `Real.logb 3` and
  `Nat.ceil`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on vectors `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ :=
  fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias vector. -/
structure Affine (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation: `x ↦ A x + c`. -/
def Affine.eval {a b : ℕ} (T : Affine a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/--
`ComputesWithHiddenLayers n k f` holds when `f : ℝ^n → ℝ` is computed by *some* ReLU
network with input dimension `n` and exactly `k` hidden layers, i.e. `f` is the alternating
composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`
of `k + 1` affine transformations `T^(1), …, T^(k+1)` (with componentwise ReLU applied after
each of the first `k` of them), where the final transformation lands in `ℝ^1`.

We define this by recursion on `k`: a `0`-hidden-layer network is a single affine map to
`ℝ^1`; a `(k+1)`-hidden-layer network peels off the first affine map `T^(1) : ℝ^n → ℝ^m`
(for some hidden width `m`), applies ReLU, and feeds the result into a `k`-hidden-layer
network `g : ℝ^m → ℝ`.
-/
def ComputesWithHiddenLayers : (n : ℕ) → (k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : Affine n 1, f = fun x => T.eval x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : Affine n m) (g : (Fin m → ℝ) → ℝ),
        ComputesWithHiddenLayers m k g ∧ f = g ∘ reluVec ∘ T.eval

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
exactly `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ComputesWithHiddenLayers n k f}

/--
`f : ℝ^n → ℝ` is continuous piecewise linear (CPWL) if it is continuous and there is a
*finite* family of affine functions `ℝ^n → ℝ` such that every point `x` has a neighbourhood
on which `f` coincides with one member of the family.
-/
def IsCPWL (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  Continuous f ∧
    ∃ (m : ℕ) (g : Fin m → Affine n 1),
      ∀ x : Fin n → ℝ, ∃ i : Fin m, ∃ ε > 0,
        ∀ y : Fin n → ℝ, dist y x < ε → f y = (g i).eval y 0

/-- `CPWL n` is the set of continuous piecewise linear functions `ℝ^n → ℝ`. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | IsCPWL n f}

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from the paper's Theorem 2. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent002

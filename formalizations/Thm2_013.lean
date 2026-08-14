import Mathlib

namespace Agent013

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):  for `n ≥ 3`,  `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`.

## Modelling choices

* Vectors `ℝ^n` are encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is encoded concretely as a matrix `A` together
  with a bias vector `c`, evaluated as `x ↦ A.mulVec x + c`.
* A ReLU network with `k` hidden layers is represented by exactly `k + 1` affine
  transformations, alternately composed with the (componentwise) ReLU function, matching
  the paper's convention that "depth k+1" = "k hidden layers". This is encoded by the
  recursively-defined predicate `IsReLURep n k f`.
* `ReLUn n k` is the set of functions representable with **at most** `k` hidden layers
  (rather than *exactly* `k`): this is the reading under which Theorem 2 is true, since a
  network with fewer hidden layers can always be padded (e.g. via the identity
  `x = ReLU(x) - ReLU(-x)`) into one with more hidden layers computing the same function,
  so `ReLU_{n,k} ⊆ ReLU_{n,k+1}` and the "exactly" and "at most" readings only differ by
  this monotonicity, with the "at most" reading being the standard and provable one.
* `CPWL n` is defined genuinely as: continuous, and locally agreeing at every point with
  one of finitely many affine functions (a genuine finite local-affine-pieces condition,
  not a max-of-affine normal form and not "representable by some ReLU network").
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded via `Real.logb 3` and `Nat.ceil`.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^n`. -/
def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias vector. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation: `x ↦ A x + c`. -/
def AffineMap.eval {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/--
`IsReLURep n k f` means `f : ℝ^n → ℝ` is computed by a ReLU network with `k` hidden
layers, i.e. by the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`
of `k + 1` affine transformations `T^(1), …, T^(k+1)` with componentwise ReLU.
Defined by recursion on `k`, peeling off the first affine transformation `T^(1)` (into
some hidden width `m`) and the first ReLU at each step.
-/
def IsReLURep : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : AffineMap n 1, f = fun x => (T.eval x) 0
  | n, k + 1, f =>
      ∃ (m : ℕ) (T : AffineMap n m) (g : (Fin m → ℝ) → ℝ),
        IsReLURep m k g ∧ f = fun x => g (reluVec (T.eval x))

/--
`ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with **at
most** `k` hidden layers (see the modelling-choice note above for why "at most" rather
than "exactly").
-/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, IsReLURep n k' f }

/--
A function `ℝ^n → ℝ` is piecewise linear if there is a finite family of affine functions
such that every point has a neighbourhood on which `f` agrees with one member of the
family. This is a genuine finite local-affine-pieces condition (not a max-of-affine
normal form).
-/
def IsPWL {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (r : ℕ) (g : Fin r → AffineMap n 1),
    ∀ x : Fin n → ℝ, ∃ i : Fin r, ∃ ε > 0, ∀ y : Fin n → ℝ, dist y x < ε → f y = (g i).eval y 0

/-- The space of continuous piecewise linear functions `ℝ^n → ℝ`. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧ IsPWL f }

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from the paper, for `n ≥ 3` (so `n - 1 ≥ 2`). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent013

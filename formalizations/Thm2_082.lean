import Mathlib

namespace Agent082

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We work with `ℝ^n` encoded as `Fin n → ℝ`.

## Modelling choices (see summary at call site)

* `ReLUn n k` is defined as functions representable by a ReLU network with **at most** `k`
  hidden layers (`∃ k' ≤ k, NetComputes n k' f`), not *exactly* `k`. This is the standard
  reading in the literature: since one can always pad a network with extra layers that act
  as the identity (e.g. via `x ↦ relu x - relu (-x)` recombinations), the class of
  representable functions is monotone increasing in the number of hidden layers, and
  Theorem 2 is naturally stated about the smallest depth that suffices for *all* of
  `CPWL_n`, which forces monotonicity for the equality to be meaningful.
* `NetComputes n k f` is defined by recursion on `k`, peeling off the *first* affine map and
  ReLU at each step, directly mirroring the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper.
* Affine transformations `ℝ^a → ℝ^b` are modelled concretely as a matrix-vector pair
  `(A, c)` with `A : Matrix (Fin b) (Fin a) ℝ`, `c : Fin b → ℝ`, acting by
  `x ↦ A.mulVec x + c`.
* `CPWL n` is defined as: `f` is continuous **and** there is a finite family of affine
  functions such that `f` locally agrees with (at least) one of them in a neighbourhood of
  every point. This is a genuine piecewise-linearity condition (a finite family of affine
  "pieces" covering `ℝ^n` via local agreement), not a max-of-affine normal form and not
  "representable by some ReLU network".
* The depth bound `⌈log_3 (n-1)⌉ + 1` is encoded using `Real.logb 3` and `Nat.ceil`.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (v : Fin m → ℝ) : Fin m → ℝ := fun i => relu (v i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely as `x ↦ A * x + c`. -/
structure AffineMap' (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def AffineMap'.eval {a b : ℕ} (T : AffineMap' a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/--
`NetComputes n k f` means `f : ℝ^n → ℝ` is computed by a ReLU network with exactly `k`
hidden layers, i.e. `f` is the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations with
componentwise ReLU applications, for some choice of hidden layer widths.

Defined by recursion on `k`, peeling off the first affine map `T^(1) : ℝ^n → ℝ^m` and the
following ReLU at each step; the base case `k = 0` is a single affine map `ℝ^n → ℝ`
(no ReLUs, i.e. `T^(1)` alone).
-/
def NetComputes : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : AffineMap' n 1, ∀ x, f x = T.eval x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : AffineMap' n m) (g : (Fin m → ℝ) → ℝ),
        NetComputes m k g ∧ ∀ x, f x = g (reluVec (T.eval x))

/--
`ReLUn n k`, the set of functions `ℝ^n → ℝ` representable by a ReLU network with **at most**
`k` hidden layers.
-/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, NetComputes n k' f }

/-- An affine function `ℝ^n → ℝ`, i.e. `x ↦ ⟨a, x⟩ + b`. -/
def IsAffineFun {n : ℕ} (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x, g x = (∑ i, a i * x i) + b

/--
`CPWL n`, the set of continuous piecewise linear functions `ℝ^n → ℝ`: `f` is continuous, and
there is a finite family of affine functions such that every point has a neighbourhood on
which `f` agrees with (at least) one member of the family.
-/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
      ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ),
        (∀ j, IsAffineFun (g j)) ∧
        ∀ x : Fin n → ℝ, ∃ j, ∃ U ∈ nhds x, ∀ y ∈ U, f y = g j y }

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent082

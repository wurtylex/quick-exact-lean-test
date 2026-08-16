import Mathlib

namespace Agent077

/- ================================================================
   Vector encoding: we use `Fin n → ℝ` for ℝ^n throughout.
   ================================================================ -/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m = Fin m → ℝ`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/- ================================================================
   Affine transformations `ℝ^a → ℝ^b`, given concretely by a matrix
   and a bias vector: `x ↦ A * x + c`.
   ================================================================ -/

/-- An affine transformation `ℝ^a → ℝ^b`, given by a matrix `A` and a bias `c`. -/
structure Affine (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def Affine.eval {a b : ℕ} (T : Affine a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/- ================================================================
   ReLU networks.

   A ReLU network with `k` hidden layers computes
     T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)
   i.e. `k` hidden layers means `k + 1` affine transformations in total,
   with a ReLU applied after each of the first `k` of them, and none
   after the last (output) transformation, matching the paper's
   definition of a ReLU network of "depth k+1".

   We define `Computes n k f` by recursion on `k`, peeling off the
   first affine map (and its following ReLU) at each step; the base
   case `k = 0` is a single affine map with no ReLU at all (matching
   depth `0 + 1 = 1`).
   ================================================================ -/

/-- `Computes n k f` means `f : ℝ^n → ℝ` is computed by a ReLU network with
`k` hidden layers, i.e. by `k + 1` affine transformations, alternating with
ReLU applied after each of the first `k` of them. -/
def Computes : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : Affine n 1, ∀ x, f x = T.eval x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T1 : Affine n m) (g : (Fin m → ℝ) → ℝ),
        Computes m k g ∧ ∀ x, f x = g (reluVec (T1.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU
network with **at most** `k` hidden layers. (We use "at most" rather than
"exactly": a network with `k'` hidden layers can always be padded, by
inserting trivial affine identity layers, to a network with any `k ≥ k'`
hidden layers computing the same function, so "at most k" is the reading
under which `ReLU_{n,k}` forms an increasing family in `k` and Theorem 2,
identifying `CPWL_n` with a single specific depth, can hold as a genuine
set equality.) -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, Computes n k' f}

/- ================================================================
   CPWL functions.

   `f : ℝ^n → ℝ` is CPWL if it is continuous and there is a *finite*
   family of affine functions such that every point of `ℝ^n` has a
   neighborhood on which `f` coincides with one member of the family.
   This is a genuine finite-piecewise-affine condition (a finite atlas
   of local affine pieces), not a "max of affine functions" normal form
   and not a "representable by some ReLU network" definition.
   ================================================================ -/

/-- An affine function `ℝ^a → ℝ`, given concretely by its linear part and bias. -/
def IsAffineMap {a : ℕ} (g : (Fin a → ℝ) → ℝ) : Prop :=
  ∃ (w : Fin a → ℝ) (b : ℝ), ∀ x, g x = (∑ i, w i * x i) + b

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`:
those that are continuous and locally agree with one of finitely many affine
functions around every point. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
        ∃ (m : ℕ) (g : Fin m → ((Fin n → ℝ) → ℝ)),
          (∀ i, IsAffineMap (g i)) ∧
          ∀ x : Fin n → ℝ, ∃ i, ∃ ε > 0, ∀ y, dist y x < ε → f y = g i y}

/- ================================================================
   The depth bound ⌈log₃(n - 1)⌉ + 1, using the real logarithm and
   `Nat.ceil`.
   ================================================================ -/

/-- The depth bound `⌈log₃(n - 1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so that
`(n : ℝ) - 1 ≥ 2 > 0` and the real logarithm behaves as expected). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/- ================================================================
   Theorem 2.
   ================================================================ -/

theorem theorem2 : ∀ n : ℕ, n ≥ 3 → CPWL n = ReLUn n (depthBound n) := sorry

end Agent077

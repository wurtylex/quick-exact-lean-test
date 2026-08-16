import Mathlib

namespace Agent076

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We encode `ℝ^n` as `Fin n → ℝ`.  A ReLU network with `k` hidden layers is modelled
*recursively*: a network with `0` hidden layers is a single affine map `ℝ^n → ℝ`
(the last affine transformation `T^(k+1)`); a network with `k+1` hidden layers first
applies an affine map `T : ℝ^n → ℝ^m` to some (existentially chosen) hidden width `m`,
then componentwise ReLU, and then feeds the result into a network with `k` hidden
layers.  This directly mirrors the alternating composition

    T^(k+1) ∘ ReLU ∘ T^(k) ∘ ... ∘ ReLU ∘ T^(1)

from the paper, without needing to fix the hidden widths `n_1, ..., n_k` in advance:
they are existentially quantified at each layer, matching "some ReLU network with
k hidden layers" rather than a network of a fixed prescribed shape.

We read `ReLU_{n,k}` as "representable with **at most** `k` hidden layers" (the
standard convention: adding layers can never hurt, since ReLU networks can implement
the identity on an extra hidden layer via `x = ReLU(x) - ReLU(-x)`; this is also the
reading under which Theorem 2, an *equality* of sets, is the correct statement).
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ :=
  fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely as `x ↦ A *ᵥ x + c`
for a matrix `A` and a translation vector `c`. -/
def IsAffineMap {a b : ℕ} (T : (Fin a → ℝ) → (Fin b → ℝ)) : Prop :=
  ∃ (A : Matrix (Fin b) (Fin a) ℝ) (c : Fin b → ℝ), ∀ x, T x = A.mulVec x + c

/-- A scalar-valued affine function `ℝ^n → ℝ`, i.e. `x ↦ c + Σᵢ aᵢ xᵢ`. -/
def IsAffineScalar {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (c : ℝ), ∀ x, f x = c + ∑ i, a i * x i

/-- `f : ℝ^n → ℝ` is computed by *some* ReLU network with exactly `k` hidden layers:
recursively, `k = 0` means `f` itself is the final affine map `T^(k+1)`, and
`k = k' + 1` means `f` is obtained by first applying an affine map into some hidden
width `m`, then ReLU, then a network with `k'` hidden layers. -/
def ComputesWithHiddenLayers : ℕ → (n : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | 0, n, f => IsAffineScalar (n := n) f
  | (k' + 1), n, f =>
      ∃ (m : ℕ) (T : (Fin n → ℝ) → (Fin m → ℝ)) (g : (Fin m → ℝ) → ℝ),
        IsAffineMap T ∧ ComputesWithHiddenLayers k' m g ∧ ∀ x, f x = g (reluVec (T x))

/-- `ReLUn n k` : the CPWL functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, ComputesWithHiddenLayers k' n f}

/-- `f : ℝ^n → ℝ` is continuous piecewise linear: it is continuous, and there is a
*finite* family of affine functions such that `f` agrees with (at least) one of them
on a neighborhood of every point. This is a genuine local piecewise-linearity
condition (a finite polyhedral-type subdivision witness), not a "max of affine"
normal form and not a restatement of ReLU-representability. -/
def IsCPWL (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  Continuous f ∧
    ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ),
      (∀ i, IsAffineScalar (n := n) (g i)) ∧
      ∀ x : Fin n → ℝ, ∃ i : Fin m, f =ᶠ[nhds x] g i

/-- `CPWL n` : the set of continuous piecewise linear functions `ℝ^n → ℝ`. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | IsCPWL n f}

/-- The depth bound `⌈log_3 (n − 1)⌉ + 1` from the paper, as a natural number,
using the real logarithm `Real.logb 3` and `Nat.ceil`. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n−1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent076

import Mathlib

namespace Agent094

open scoped BigOperators

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias
vector: `x ↦ A x + c`. -/
def affineApply {a b : ℕ} (A : Matrix (Fin b) (Fin a) ℝ) (c : Fin b → ℝ)
    (x : Fin a → ℝ) : Fin b → ℝ :=
  A.mulVec x + c

/-- A function `ℝ^n → ℝ` is affine if it can be written as `x ↦ c + ⟨a, x⟩` for some
weight vector `a` and bias `c`. -/
def IsAffine (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (c : ℝ), f = fun x => c + ∑ i, a i * x i

/-- `f : ℝ^n → ℝ` is computed by a ReLU network with **exactly** `k` hidden layers.
This formalizes the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper, defined recursively on
`k`: with `0` hidden layers, `f` is just a single affine transformation `T^(1)`
(the case `k = 0`, depth `1`); with `k + 1` hidden layers, `f` is obtained by first
applying an affine transformation `T^(1) : ℝ^n → ℝ^m` into some intermediate width
`m`, then a componentwise ReLU, and then a network with `k` hidden layers on the
result. -/
def ComputedWithHiddenLayers : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => IsAffine n f
  | n, (k + 1), f =>
      ∃ (m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ) (g : (Fin m → ℝ) → ℝ),
        ComputedWithHiddenLayers m k g ∧ f = fun x => g (reluVec (affineApply A c x))

/-- `ReLUn n k`: the set of functions `ℝ^n → ℝ` representable by a ReLU network with
**at most** `k` hidden layers.

Modelling choice: we use "at most `k`" rather than "exactly `k`". Any affine
transformation can implement the identity map after applying ReLU (via the
"doubling trick" `x ↦ (x, -x) ↦ (relu x, relu(-x)) ↦ relu x - relu(-x) = x`, itself
an extra hidden layer), so a function computable with `k` hidden layers is always
also computable with `k + 1` hidden layers; the "exactly `k`" and "at most `k`"
readings therefore describe the same nested family of sets, and "at most" is the
standard convention in the expressivity literature (and the one under which
`ReLU_{n,k} ⊆ ReLU_{n,k+1}` holds, matching the intended reading of Theorem 2 as an
equality of sets of functions attainable *within* a hidden-layer budget). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, ComputedWithHiddenLayers n k' f}

/-- `CPWL n`: the continuous, piecewise-linear functions `ℝ^n → ℝ`. We require `f` to
be continuous, together with a *single finite family* of affine "pieces" `g 0, …,
g (m-1)` such that `f` agrees with one of these pieces on a neighborhood of every
point of `ℝ^n` (a genuine finite polyhedral-type piecewise-affine condition, not a
"representable by a ReLU network" or max-of-affine reformulation). -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ),
      (∀ i, IsAffine n (g i)) ∧
      ∀ x : Fin n → ℝ, ∃ i, ∃ U ∈ nhds x, Set.EqOn f (g i) U}

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from Theorem 2, as a natural number, computed
via the real logarithm `Real.logb 3` and `Nat.ceil`. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉+1}`, i.e. the CPWL
functions on `ℝ^n` are exactly those representable by a ReLU network with at most
`⌈log_3(n-1)⌉ + 1` hidden layers. -/
theorem theorem2 : ∀ n : ℕ, n ≥ 3 → CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent094

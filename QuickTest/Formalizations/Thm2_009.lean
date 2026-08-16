import Mathlib

namespace Agent009

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):

  For n ≥ 3,  CPWL_n = ReLU_{n, ⌈log_3 (n-1)⌉ + 1}.

## Modelling choices

* `ℝ^n` is encoded as `Fin n → ℝ`.
* An affine map `ℝ^a → ℝ^b` is encoded concretely as `x ↦ A * x + c` for a matrix
  `A : Matrix (Fin b) (Fin a) ℝ` and a bias vector `c : Fin b → ℝ`. An affine
  *functional* `ℝ^n → ℝ` is the special case `b = 1`, spelled out directly with a
  weight vector and a scalar bias.
* A ReLU network computing `f : ℝ^n → ℝ` with exactly `k` hidden layers is defined
  recursively: with `0` hidden layers, `f` itself must be affine; with `k+1` hidden
  layers, `f` factors as `g ∘ relu ∘ T` where `T : ℝ^n → ℝ^m` is affine (the first
  layer, into some hidden width `m`) and `g : ℝ^m → ℝ` is computed by a network with
  `k` hidden layers.
* `ReLUn n k` is taken to be functions representable with **at most** `k` hidden
  layers (not exactly `k`): a network with `k'` ≤ `k` hidden layers can always be
  padded to exactly `k` hidden layers by inserting extra affine "identity" layers
  (composed with `relu`, using two coordinates per padded dimension via
  `x ↦ relu(x) - relu(-x) = x`), so the two readings would in fact define the same
  sets; we use the "at most k" phrasing since it is definitionally the more natural
  one for which `ReLUn n` is monotone in `k`, matching the set-equality statement of
  the theorem.
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of affine
  functionals `g : Fin m → (ℝ^n → ℝ)` such that every point `x` has a neighbourhood on
  which `f` agrees with some `g i` (this is a genuine finite polyhedral-subdivision
  style piecewise-linearity condition, not a global max-of-affine formula and not
  "representable by some ReLU network").
* The depth bound `⌈log_3 (n-1)⌉ + 1` is encoded using the real logarithm
  `Real.logb 3` together with `Nat.ceil`.
-/

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => max 0 (x i)

/-- `T : ℝ^a → ℝ^b` is an affine map, i.e. `T x = A * x + c` for some matrix `A` and
bias vector `c`. -/
def IsAffineMap (a b : ℕ) (T : (Fin a → ℝ) → (Fin b → ℝ)) : Prop :=
  ∃ (A : Matrix (Fin b) (Fin a) ℝ) (c : Fin b → ℝ),
    ∀ x : Fin a → ℝ, ∀ i, T x i = (∑ j, A i j * x j) + c i

/-- `f : ℝ^n → ℝ` is an affine functional, i.e. `f x = ⟪a, x⟫ + c` for some weight
vector `a` and scalar bias `c`. -/
def IsAffineFunctional (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (c : ℝ), ∀ x : Fin n → ℝ, f x = (∑ j, a j * x j) + c

/-- `f : ℝ^n → ℝ` is computed by a ReLU network with exactly `k` hidden layers:
recursively, `0` hidden layers means `f` is itself affine, and `k+1` hidden layers
means `f = g ∘ relu ∘ T` where `T` is an affine "first layer" into some hidden
width `m`, and `g` is computed by a network with `k` hidden layers on that hidden
width. This directly reflects the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper. -/
def ComputesWithHiddenLayers : (k : ℕ) → (n : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | 0, n, f => IsAffineFunctional n f
  | (k + 1), n, f =>
      ∃ (m : ℕ) (T : (Fin n → ℝ) → (Fin m → ℝ)) (g : (Fin m → ℝ) → ℝ),
        IsAffineMap n m T ∧
        ComputesWithHiddenLayers k m g ∧
        (∀ x : Fin n → ℝ, f x = g (reluVec (T x)))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network
with *at most* `k` hidden layers (see the module docstring for why this reading is
used rather than "exactly `k`"). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, ComputesWithHiddenLayers k' n f }

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: those
that are continuous and, on a neighbourhood of every point, agree with one of
finitely many globally-fixed affine functionals. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ),
          (∀ i, IsAffineFunctional n (g i)) ∧
          (∀ x : Fin n → ℝ, ∃ i, ∀ᶠ y in nhds x, f y = g i y) }

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from the theorem statement. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 (↑(n - 1) : ℝ)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3 (n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent009

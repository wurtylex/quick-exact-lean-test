import Mathlib

namespace Agent006

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):  for `n ≥ 3`,  `CPWL n = ReLUn n (⌈log_3 (n-1)⌉ + 1)`.

## Modelling choices

* Vectors `ℝ^n` are encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is encoded concretely as a matrix `A` together
  with a bias vector `c`, evaluated as `x ↦ A.mulVec x + c`.
* A ReLU network with `k` hidden layers computing `f : ℝ^n → ℝ` is defined by recursion
  on `k`: with `0` hidden layers it is a single affine map `ℝ^n → ℝ^1`; with `k+1` hidden
  layers it is an affine map `ℝ^n → ℝ^m` into some hidden width `m`, followed by a
  component-wise ReLU, followed by a network with `k` hidden layers on the output.
  This mirrors the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper.
* `ReLUn n k` is taken to be functions representable with **at most** `k` hidden layers
  (not exactly `k`).  This is the reading under which Theorem 2 is true: extra hidden
  layers can only help (one can always pad a shallower network out to more layers), so
  `ReLUn n k` is monotone increasing in `k`, and the content of Theorem 2 is that
  `⌈log_3(n-1)⌉ + 1` hidden layers already suffice to reach all of `CPWL n` (and no fewer
  would, by Theorem 1's lower bound machinery) — an "exactly `k`" reading would make the
  two sides genuinely different sets for essentially every `k`, and the displayed equality
  would be false/ill-posed.
* `CPWL n` is defined directly (not via ReLU networks!) as: `f` is continuous, and there is
  a *finite* family of affine scalar functions on `ℝ^n` such that `f` locally agrees with
  (at least) one member of the family in a neighbourhood of every point. This is a genuine
  piecewise-linearity condition, not a max-of-affine normal form and not "representable by
  some network".
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined using the real logarithm `Real.logb 3` and
  `Nat.ceil`, applied to `(n : ℝ) - 1`.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias vector. -/
structure AffineTransform (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation: `x ↦ A x + c`. -/
def affineApply {a b : ℕ} (T : AffineTransform a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- An affine *scalar* function `ℝ^n → ℝ`, given by a coefficient vector and a constant. -/
structure AffineFunc (n : ℕ) where
  coeffs : Fin n → ℝ
  const : ℝ

/-- Evaluation of a scalar affine function: `x ↦ ⟨coeffs, x⟩ + const`. -/
def AffineFunc.eval {n : ℕ} (g : AffineFunc n) (x : Fin n → ℝ) : ℝ :=
  (∑ i, g.coeffs i * x i) + g.const

/-- `ComputesHidden n k f` holds iff `f : ℝ^n → ℝ` is computed by a ReLU network with
exactly `k` hidden layers, i.e. by the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations
`T^(1), …, T^(k+1)` with componentwise ReLU applications in between. Defined by recursion
on `k`: the base case `k = 0` is a single affine map into `ℝ^1`; the successor case peels
off the first affine map `T^(1) : ℝ^n → ℝ^m` and one ReLU, leaving a `k`-hidden-layer
network on the resulting `ℝ^m`. -/
def ComputesHidden : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : AffineTransform n 1, ∀ x, f x = affineApply T x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : AffineTransform n m) (g : (Fin m → ℝ) → ℝ),
        ComputesHidden m k g ∧ ∀ x, f x = g (reluVec (affineApply T x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
**at most** `k` hidden layers (see the modelling-choice discussion above for why "at most"
rather than "exactly `k`" is the reading that makes Theorem 2 true). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, ComputesHidden n k' f}

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: those that
are continuous and locally agree, near every point, with some member of a single *finite*
family of affine scalar functions. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
       ∃ (m : ℕ) (g : Fin m → AffineFunc n),
         ∀ x : Fin n → ℝ, ∃ i : Fin m, ∀ᶠ y in nhds x, f y = (g i).eval y}

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so `n - 1 ≥ 2`). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL n = ReLUn n (⌈log_3(n-1)⌉ + 1)`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent006

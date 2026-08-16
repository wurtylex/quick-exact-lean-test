import Mathlib

namespace Agent044

/-!
# Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity: Subdividing the Simplex")

For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`.

## Modelling choices

* `ℝ^n` is encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is encoded concretely as a matrix `A` together with a
  bias vector `c`, evaluated as `x ↦ A.mulVec x + c`.
* A ReLU network with exactly `k` hidden layers computing `f : ℝ^n → ℝ` is defined by recursion
  on `k`: with `0` hidden layers, `f` is exactly one affine map `ℝ^n → ℝ^1`; with `k+1` hidden
  layers, `f` factors as `g ∘ ReLU ∘ T` where `T : ℝ^n → ℝ^m` is affine (`m > 0` neurons in the
  first hidden layer) and `g : ℝ^m → ℝ` is computed by a network with `k` hidden layers. This
  directly mirrors the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper, peeling off `T^(1)` at each step.
* `ReLUn n k` is taken to be the functions representable with **at most** `k` hidden layers
  (i.e. `∃ k' ≤ k`), not *exactly* `k`. This is the standard reading and the one that makes
  Theorem 2 true: e.g. every affine function lies in `ReLUn n k` for every `k`, not just `k = 0`.
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of affine functions
  such that around every point `x` there is a neighbourhood on which `f` agrees with one member
  of the family. This is a genuine local-affine-pieces condition, independent of ReLU networks.
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded using the real logarithm `Real.logb 3` and
  `Nat.ceil`, applied to the real number `(n : ℝ) - 1`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise (vectorized) application of `relu`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias vector. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an `AffineMap` as `x ↦ A * x + c`. -/
def AffineMap.eval {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `NetComputes n k f` means `f : ℝ^n → ℝ` is computed by a ReLU network with **exactly** `k`
hidden layers, i.e. `f` is the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations, defined by
recursion on `k` (peeling off the innermost affine map `T^(1)` and the hidden layer it feeds). -/
def NetComputes : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : AffineMap n 1, ∀ x, f x = T.eval x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (_ : 0 < m) (T : AffineMap n m) (g : (Fin m → ℝ) → ℝ),
        NetComputes m k g ∧ ∀ x, f x = g (reluVec (T.eval x))

/-- `ReLUn n k`, the set of functions `ℝ^n → ℝ` representable by a ReLU network with **at most**
`k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, NetComputes n k' f }

/-- `CPWL n`, the set of continuous piecewise-linear functions `ℝ^n → ℝ`: `f` is continuous, and
there is a finite family of affine functions (linear part `A i`, bias `b i`) such that every
point of `ℝ^n` has a neighbourhood on which `f` coincides with one member of the family. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (N : ℕ) (A : Fin N → (Fin n → ℝ)) (b : Fin N → ℝ),
          ∀ x : Fin n → ℝ, ∃ i : Fin N, ∀ᶠ y in nhds x, f y = (∑ j, A i j * y j) + b i }

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from Theorem 2, for `n ≥ 3`. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent044

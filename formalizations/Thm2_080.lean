import Mathlib

namespace Agent080

/-!
# Theorem 2 of arXiv:2505.14338 (Bakaev–Brunck–Hertrich–Stade–Yehudayoff)

We formalize the *statement* of Theorem 2:

  For n ≥ 3,  CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}.

## Modelling choices

* Vectors `ℝ^m` are encoded as `Fin m → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is encoded concretely and explicitly as a matrix
  `A : Fin b → Fin a → ℝ` together with a bias vector `c : Fin b → ℝ`, evaluated as
  `x ↦ A * x + c` (written out with `Finset.sum`), see `AffineMap` / `AffineMap.eval`.
* `relu` is `max 0 ·` on `ℝ`, and `reluVec` applies it componentwise.
* A ReLU network with `k` hidden layers computing `f : ℝ^n → ℝ` is modelled by the
  recursively-peeled proposition `IsReLUComputable n k f`: peeling off the first affine
  map `T^{(1)} : ℝ^n → ℝ^m` and the first ReLU leaves a function `g` on `ℝ^m` that is
  itself computable with `k - 1` hidden layers; the base case `k = 0` is a single affine
  map `ℝ^n → ℝ^1` (i.e. `T^{(k+1)}` with no ReLU applied after it), matching the
  alternating composition `T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}` from the paper.
  We take `ReLU_{n,k}` to mean functions representable with **exactly** `k` hidden
  layers (the literal reading of "representable with k hidden layers" in Section 1 of the
  paper), rather than "at most k".
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of affine
  functions `ℝ^n → ℝ` such that every point `x` has a neighbourhood on which `f` agrees
  with one of these affine functions (a genuine local-piecewise-linearity condition, not
  a max-of-affine normal form and not "representable by a ReLU network").
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined via the real logarithm `Real.logb 3` and
  `Nat.ceil`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix `A` (as a function
`Fin b → Fin a → ℝ`) and a bias vector `c : Fin b → ℝ`, computing `x ↦ A * x + c`. -/
structure AffineMap (a b : ℕ) where
  A : Fin b → Fin a → ℝ
  c : Fin b → ℝ

/-- Evaluation of an `AffineMap` at a point. -/
def AffineMap.eval {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun j => (∑ i, T.A j i * x i) + T.c j

/-- `IsReLUComputable n k f` says that `f : ℝ^n → ℝ` is computed by a ReLU network with
exactly `k` hidden layers, i.e. `f = T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}` for
some affine maps `T^{(1)}, …, T^{(k+1)}` of matching (but otherwise arbitrary) intermediate
widths. We peel off the first affine map and the first ReLU at each recursive step. -/
def IsReLUComputable : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : AffineMap n 1, f = fun x => T.eval x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : AffineMap n m) (g : (Fin m → ℝ) → ℝ),
        IsReLUComputable m k g ∧ f = fun x => g (reluVec (T.eval x))

/-- `ReLUn n k`, the set of functions `ℝ^n → ℝ` representable by a ReLU network with
exactly `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) := {f | IsReLUComputable n k f}

/-- An affine function `ℝ^n → ℝ`, expressed via an `AffineMap n 1`. -/
def IsAffineFun (n : ℕ) (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ T : AffineMap n 1, g = fun x => T.eval x 0

/-- `CPWL n`, the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: `f` is
continuous, and there is a finite family of affine functions such that every point has a
neighbourhood on which `f` coincides with one of them. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (ι : Type) (_ : Fintype ι) (g : ι → (Fin n → ℝ) → ℝ),
      (∀ i, IsAffineFun n (g i)) ∧ ∀ x : Fin n → ℝ, ∃ i, f =ᶠ[nhds x] g i}

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so `n - 1 ≥ 2 > 0`). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent080

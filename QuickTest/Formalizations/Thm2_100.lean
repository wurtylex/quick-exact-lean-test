import Mathlib

namespace Agent100

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

"Better Neural Network Expressivity: Subdividing the Simplex"
(Bakaev, Brunck, Hertrich, Stade, Yehudayoff).

**Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3 (n-1)⌉ + 1}`.

## Modelling choices

* Vectors `ℝ^n` are encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is encoded concretely as a pair `(A, bias)` with
  `A : Matrix (Fin b) (Fin a) ℝ` and `bias : Fin b → ℝ`, acting as `x ↦ A.mulVec x + bias`.
* A ReLU network with `k` *hidden layers* (depth `k + 1`) computing `f : ℝ^n → ℝ` is defined
  recursively: with `0` hidden layers it is a single affine map `ℝ^n → ℝ^1`; with `k+1`
  hidden layers it is an affine map `ℝ^n → ℝ^m` into some hidden width `m`, followed by
  componentwise ReLU, followed by a network with `k` hidden layers on `ℝ^m`. This exactly
  mirrors the alternating composition
  `T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}` from the paper.
* `ReLUn n k` is the set of functions representable with *exactly* `k` hidden layers (the
  literal reading of `ReLU_{n,k}`). This choice is consistent with the theorem: one can pad
  a `k`-hidden-layer network into a `(k+1)`-hidden-layer network computing the same function
  (e.g. by carrying each coordinate `x_i` through an extra layer as `relu(x_i) - relu(-x_i)`),
  so the classes are monotone in `k` and the "exactly `k`" and "at most `k`" readings agree
  on which functions are representable within `k` layers.
* `CPWL n` is defined genuinely: `f` is continuous and there is a *finite* family of affine
  functions `g : Fin m → (ℝ^n → ℝ)` such that around every point `x`, `f` locally agrees with
  one of the `g i` (i.e. `f =ᶠ[𝓝 x] g i`). This is a real piecewise-affine/local-polyhedral
  condition, not a disguised "representable by a ReLU network" or "max of affine functions"
  statement.
* The depth bound `⌈log_3 (n - 1)⌉ + 1` is encoded using the real logarithm `Real.logb 3`
  together with `Nat.ceil`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^n`. -/
def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias vector. -/
structure AffineTransform (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  bias : Fin b → ℝ

/-- The function `ℝ^a → ℝ^b` computed by an affine transformation: `x ↦ A x + bias`. -/
def AffineTransform.toFun {a b : ℕ} (T : AffineTransform a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.bias

/--
`IsReLURepresentable n k f` means `f : ℝ^n → ℝ` is computed by a ReLU network with `k` hidden
layers, i.e. by the alternating composition
`T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}`
of `k + 1` affine transformations `T^{(1)}, …, T^{(k+1)}` with `ReLU` applied componentwise
after each of the first `k` of them.

Defined by recursion on `k`: with `0` hidden layers, `f` is itself an affine map into `ℝ^1`;
with `k + 1` hidden layers, `f` factors as `g ∘ ReLU ∘ T` where `T : ℝ^n → ℝ^m` is affine
(the first layer) and `g : ℝ^m → ℝ` is representable with `k` hidden layers.
-/
def IsReLURepresentable : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : AffineTransform n 1, ∀ x, f x = T.toFun x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : AffineTransform n m) (g : (Fin m → ℝ) → ℝ),
        IsReLURepresentable m k g ∧ ∀ x, f x = g (reluVec (T.toFun x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
exactly `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) := {f | IsReLURepresentable n k f}

/-- An affine (as opposed to merely linear) real-valued function `ℝ^n → ℝ`. -/
def IsAffineFun (n : ℕ) (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ T : AffineTransform n 1, ∀ x, g x = T.toFun x 0

/--
`CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: those `f` that are
continuous and admit a *finite* family of affine functions `g 0, …, g (m-1)` such that around
every point `x` of `ℝ^n`, `f` coincides with some `g i` on a neighbourhood of `x`. This is a
genuine local-polyhedral piecewise-affine condition, independent of any ReLU-network
representation and not simply a "max of finitely many affine functions" normal form.
-/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ),
      (∀ i, IsAffineFun n (g i)) ∧ ∀ x, ∃ i, f =ᶠ[nhds x] g i}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, for `n ≥ 3` (in general `n ≥ 2`
suffices for the logarithm to be well-behaved). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3 (n - 1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent100

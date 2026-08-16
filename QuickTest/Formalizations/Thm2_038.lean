import Mathlib

namespace Agent038

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

`CPWL n = ReLU_{n, ⌈log_3 (n-1)⌉ + 1}` for `n ≥ 3`.

## Modelling choices

* Vectors `ℝ^n` are modelled as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is modelled concretely as a bundled
  pair of a "weight function" `W : Fin b → Fin a → ℝ` and a bias
  `c : Fin b → ℝ`, applied as `x ↦ (fun i => ∑ j, W i j * x j + c i)`.
  This avoids pulling in `Matrix`/`Matrix.mulVec` machinery while being
  definitionally the same content.
* A ReLU network with `k` hidden layers computing `f : ℝ^n → ℝ` is defined
  *recursively* on `k`, directly mirroring the alternating composition
  `T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}` from the paper:
  - `k = 0`: `f` is computed by a single affine transformation `ℝ^n → ℝ^1`
    (no hidden layer, no ReLU applied at all — this is `T^{(1)}` alone).
  - `k + 1`: there is a hidden width `m`, an affine map `T : ℝ^n → ℝ^m`, and
    a function `g : ℝ^m → ℝ` computable with `k` hidden layers, such that
    `f = g ∘ ReLU ∘ T`.
  `ReLUn n k` is the set of functions computable with *exactly* `k` hidden
  layers in this recursive sense. (Note: because one can always simulate the
  identity on `ℝ` using two extra ReLU neurons via `x = ReLU x - ReLU (-x)`,
  the "exactly `k`" and "at most `k`" readings coincide for all `k ≥ 1`, so
  this choice is not actually a restriction; we simply find the "exactly
  `k`" recursive definition the most literal transcription of the paper's
  alternating-composition definition.)
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family
  of affine functionals `ℝ^n → ℝ` such that every point of `ℝ^n` has a
  neighborhood on which `f` coincides with one member of the family. This is
  a genuine local piecewise-linearity condition (a finite atlas of affine
  pieces), not a restatement of ReLU-representability and not the
  max-of-affine normal form.
* The depth bound is `⌈log_3 (n - 1)⌉ + 1`, encoded literally via
  `Real.logb 3` and `Nat.ceil` (`⌈·⌉₊`).
-/

/-- A componentwise ReLU. -/
def reluScalar (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `reluScalar` to a vector in `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ :=
  fun i => reluScalar (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a weight
function and a bias vector. -/
structure Affine (a b : ℕ) where
  /-- The "matrix" of coefficients: `W i j` is the coefficient of input
  coordinate `j` in output coordinate `i`. -/
  W : Fin b → Fin a → ℝ
  /-- The bias vector. -/
  c : Fin b → ℝ

/-- Evaluate an affine transformation at a point. -/
def Affine.apply {a b : ℕ} (T : Affine a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (Finset.univ.sum fun j => T.W i j * x j) + T.c i

/-- `ComputesHidden k n f` means `f : ℝ^n → ℝ` is computed by a ReLU network
with exactly `k` hidden layers, i.e. `f` arises as the alternating
composition `T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}` of `k + 1`
affine transformations with `k` interspersed componentwise ReLUs. -/
def ComputesHidden : ℕ → (n : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | 0, n, f => ∃ T : Affine n 1, f = fun x => T.apply x 0
  | (k + 1), n, f =>
      ∃ (m : ℕ) (T : Affine n m) (g : (Fin m → ℝ) → ℝ),
        ComputesHidden k m g ∧ f = fun x => g (reluVec (T.apply x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU
network with exactly `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ComputesHidden k n f}

/-- An affine functional `ℝ^n → ℝ`, as a `Prop` predicate: `a` is affine iff
it has the form `x ↦ ⟨c, x⟩ + b` for some coefficients `c` and constant `b`. -/
def IsAffineFunctional (n : ℕ) (a : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (coef : Fin n → ℝ) (b : ℝ), ∀ x, a x = (Finset.univ.sum fun i => coef i * x i) + b

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`:
those that are continuous and admit a *finite* family of affine functionals
such that every point has a neighborhood on which `f` agrees with one member
of the family. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
      ∃ (r : ℕ) (a : Fin r → (Fin n → ℝ) → ℝ),
        (∀ i, IsAffineFunctional n (a i)) ∧
        ∀ x : Fin n → ℝ, ∃ (i : Fin r) (ε : ℝ), ε > 0 ∧
          ∀ y : Fin n → ℝ, dist y x < ε → f y = a i y}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, encoded via the
real logarithm `Real.logb 3` and `Nat.ceil`. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3 (n - 1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent038

import Mathlib

namespace Agent099

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

Modelling choices (see summary at the call site / final report):

* Vectors `ℝ^n` are encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is given concretely by a matrix of
  coefficients `A : Fin b → Fin a → ℝ` and a bias vector, evaluated as
  `x ↦ A x + bias`.
* A ReLU network with `k` hidden layers is represented by the inductive
  family `ReLUNet n k` below, which literally encodes the alternating
  composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper,
  with all intermediate widths existentially quantified.
* `ReLUn n k` is the set of functions representable with **at most** `k`
  hidden layers (i.e. with some `k' ≤ k`). This is the standard reading
  that makes `ReLUn n k` monotone in `k`, matching the informal use of
  "depth budget" in the statement of Theorem 2.
* `CPWL n` is defined as: continuous, and locally (in a neighbourhood of
  every point) equal to one of finitely many globally-fixed affine
  functions. This is a genuine piecewise-affine condition, not a
  "representable by ReLU network" or "max of affine" definition.
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded using the real logarithm
  `Real.logb 3` composed with `Nat.ceil`.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ :=
  fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely as `x ↦ A x + bias`. -/
structure AffMap (a b : ℕ) where
  A    : Fin b → Fin a → ℝ
  bias : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def AffMap.eval {a b : ℕ} (T : AffMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, T.A i j * x j) + T.bias i

/--
A ReLU network with input dimension `n` and `k` hidden layers, encoded as
`k + 1` affine transformations `T^(1), …, T^(k+1)` with the intermediate
widths existentially quantified:

* `last T` is the base case of a network with `0` hidden layers: a single
  affine transformation `T^(1) : ℝ^n → ℝ` (the output layer, output
  dimension `1`), with no ReLU applied.
* `cons m T rest` prepends an affine transformation `T : ℝ^n → ℝ^m`
  followed by a componentwise ReLU, then continues with the network `rest`
  (which has `k` further hidden layers), giving `k + 1` hidden layers in
  total.
-/
inductive ReLUNet : ℕ → ℕ → Type where
  | last {n : ℕ} (T : AffMap n 1) : ReLUNet n 0
  | cons {n k : ℕ} (m : ℕ) (T : AffMap n m) (rest : ReLUNet m k) : ReLUNet n (k + 1)

/-- The real-valued function computed by a ReLU network. -/
def ReLUNet.eval : {n k : ℕ} → ReLUNet n k → (Fin n → ℝ) → ℝ
  | _, _, .last T, x => T.eval x 0
  | _, _, .cons _ T rest, x => rest.eval (reluVec (T.eval x))

/--
`ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU
network with **at most** `k` hidden layers (some `k' ≤ k`).
-/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, ∃ net : ReLUNet n k', ∀ x, net.eval x = f x }

/-- A function `ℝ^n → ℝ` is affine if it has the form `x ↦ ∑ a_i x_i + b`. -/
def IsAffineFn (n : ℕ) (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x, g x = (∑ i, a i * x i) + b

/--
`CPWL n` is the space of continuous piecewise-linear (affine) functions
`ℝ^n → ℝ`: functions that are continuous, and such that there is a finite
family of affine functions with which `f` locally agrees at every point
(i.e. every point has a neighbourhood on which `f` coincides with one of
the finitely many affine pieces).
-/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
      ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ),
        (∀ i, IsAffineFn n (g i)) ∧
        ∀ x : Fin n → ℝ, ∃ i, ∀ᶠ y in nhds x, f y = g i y }

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from Theorem 2. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/--
**Theorem 2.** For `n ≥ 3`, the space of continuous piecewise-linear
functions on `ℝ^n` equals the space of functions representable by a ReLU
network with `⌈log_3(n-1)⌉ + 1` hidden layers.
-/
theorem theorem2 : ∀ n : ℕ, 3 ≤ n → CPWL n = ReLUn n (depthBound n) := sorry

end Agent099

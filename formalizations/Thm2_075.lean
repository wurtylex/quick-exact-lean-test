import Mathlib

namespace Agent075

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

"Better Neural Network Expressivity: Subdividing the Simplex"
(Bakaev, Brunck, Hertrich, Stade, Yehudayoff)

Theorem 2. For n ≥ 3, CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}.

## Modelling choices

* Vectors `ℝ^n` are encoded as `Fin n → ℝ`.
* Affine transformations `ℝ^a → ℝ^b` are encoded concretely and explicitly as a weight
  matrix `Fin b → Fin a → ℝ` together with a bias vector `Fin b → ℝ`, applied as
  `x ↦ A * x + c`.
* A ReLU network with exactly `k` hidden layers and input dimension `a` is encoded as an
  inductive type `ReLUNet a k`: either a single final affine map `a → 1` (the case `k = 0`,
  i.e. depth 1, no hidden layers), or an affine map `a → b` followed by `ReLU`, followed by
  a network with `k` hidden layers and input dimension `b` (the case `k + 1` hidden
  layers). This directly mirrors the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ... ∘ ReLU ∘ T^(1)` from the paper, with the intermediate
  widths existentially quantified inside the inductive constructor.
* `ReLUn n k` is read as *exactly* `k` hidden layers (not "at most"): a function is in
  `ReLUn n k` iff it is computed by *some* `ReLUNet n k`, and `k` is baked into the type of
  `ReLUNet`. This is the literal reading of `ReLU_{n,k}` in the paper. It does not lose
  generality relative to an "at most k" reading: any network with fewer hidden layers can be
  padded out to exactly `k` hidden layers by inserting extra affine "identity" layers of the
  form `x ↦ ReLU(x) - ReLU(-x)` type tricks realized via two extra ReLU layers, so the two
  readings describe the same sets of functions; we simply commit to the exact-`k` reading
  since it is the more literal transcription of the paper's notation.
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of affine
  functions `g_1, ..., g_m : ℝ^n → ℝ` such that every point `x` has a neighborhood on which
  `f` coincides with (at least) one of the `g_i`. This is a genuine local
  piecewise-linearity condition (finitely many affine "pieces", covering neighborhoods of
  every point) and is *not* defined as "representable by a ReLU network" nor as a max/min of
  affine functions, so Theorem 2 is a nontrivial statement about this definition.
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded using the real logarithm `Real.logb 3` and
  `Nat.ceil` (`⌈·⌉₊`), which for `n ≥ 3` (so `n - 1 ≥ 2 > 0`) coincides with the intended
  ceiling of the real number `log_3(n-1)`.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector in `ℝ^n` (encoded as `Fin n → ℝ`). -/
def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a weight matrix and a bias
vector: `x ↦ A * x + c`. -/
structure AffineTransform (a b : ℕ) where
  weight : Fin b → Fin a → ℝ
  bias : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def AffineTransform.eval {a b : ℕ} (T : AffineTransform a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun j => (∑ i, T.weight j i * x i) + T.bias j

/-- A ReLU network with input dimension `a` and *exactly* `k` hidden layers, computing a
real-valued (output dimension 1) function. `ReLUNet a 0` is a single affine map `a → 1`
(depth 1, zero hidden layers). `ReLUNet a (k+1)` is an affine map `a → b` (for some
intermediate width `b`), followed implicitly by a `ReLU`, followed by a network with `k`
hidden layers on input dimension `b`. This directly mirrors
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ... ∘ ReLU ∘ T^(1)`. -/
inductive ReLUNet : ℕ → ℕ → Type where
  | last {a : ℕ} (T : AffineTransform a 1) : ReLUNet a 0
  | cons {a b k : ℕ} (T : AffineTransform a b) (rest : ReLUNet b k) : ReLUNet a (k + 1)

/-- The function `ℝ^a → ℝ` computed by a ReLU network. -/
def ReLUNet.eval : {a k : ℕ} → ReLUNet a k → (Fin a → ℝ) → ℝ
  | _, _, .last T, x => T.eval x 0
  | _, _, .cons T rest, x => rest.eval (reluVec (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
input dimension `n` and *exactly* `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ net : ReLUNet n k, ∀ x, f x = net.eval x }

/-- A function `ℝ^n → ℝ` is affine if it has the form `x ↦ ⟨w, x⟩ + b`. -/
def IsAffineFn {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (w : Fin n → ℝ) (b : ℝ), ∀ x, f x = (∑ i, w i * x i) + b

/-- `CPWL n` is the set of continuous piecewise-linear functions `ℝ^n → ℝ`: those that are
continuous and locally agree, on a neighborhood of every point, with one of finitely many
affine functions. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ),
          (∀ i, IsAffineFn (g i)) ∧
          ∀ x : Fin n → ℝ, ∃ i, ∃ U ∈ nhds x, Set.EqOn f (g i) U }

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from Theorem 2. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent075

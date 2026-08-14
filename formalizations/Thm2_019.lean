import Mathlib

namespace Agent019

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

Modelling choices (see final summary):
* Vectors `ℝ^n` are encoded as `Fin n → ℝ`.
* An affine map `ℝ^a → ℝ^b` is encoded concretely as a pair `(A, b)` with
  `A : Matrix (Fin b) (Fin a) ℝ` and `b : Fin b → ℝ`, acting by `x ↦ A.mulVec x + b`.
* A ReLU network with exactly `k` hidden layers is bundled as a structure
  `ReLUNetwork n k` carrying the sequence of layer widths (`widths 0 = n`,
  `widths (k+1) = 1`) together with the `k+1` affine maps `T^(1), …, T^(k+1)`
  between consecutive widths; `ReLUNetwork.eval` unfolds the alternating
  composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`.
* `ReLUn n k` is the set of functions representable with **at most** `k`
  hidden layers (the standard reading in the literature; it coincides with
  "exactly `k`" up to padding by trivial identity-computing layers, so either
  convention makes Theorem 2 true).
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of
  affine functions such that `f` locally agrees with (at least) one member of
  that family in a neighbourhood of every point. This is a genuine
  piecewise-linearity condition (finitely many affine "pieces" that patch
  together to a globally continuous function), not a max-of-affine normal
  form and not "representable by some ReLU network".
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined via `Real.logb 3` and
  `Nat.ceil` on the real number `(n : ℝ) - 1`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, encoded concretely as a matrix
together with a bias vector. -/
def AffineMap' (a b : ℕ) : Type := Matrix (Fin b) (Fin a) ℝ × (Fin b → ℝ)

/-- The function `ℝ^a → ℝ^b` computed by an affine transformation. -/
def AffineMap'.apply {a b : ℕ} (T : AffineMap' a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (Matrix.mulVec T.1 x) i + T.2 i

/-- A ReLU network with input dimension `n` and exactly `k` hidden layers:
a sequence of `k + 2` widths `widths 0 = n, widths 1, …, widths k, widths (k+1) = 1`
together with `k + 1` affine transformations `T^(i) : ℝ^{widths (i-1)} → ℝ^{widths i}`
for `i = 1, …, k + 1` (here indexed from `0` to `k`). -/
structure ReLUNetwork (n k : ℕ) where
  /-- The width of each layer, `0` (the input layer) through `k + 1` (the output layer). -/
  widths : ℕ → ℕ
  width_zero : widths 0 = n
  width_last : widths (k + 1) = 1
  /-- The affine transformation `T^(i+1) : ℝ^{widths i} → ℝ^{widths (i+1)}`, for `i ≤ k`. -/
  layer : (i : ℕ) → i < k + 1 → AffineMap' (widths i) (widths (i + 1))

/-- The vector produced at layer `i` (for `0 ≤ i ≤ k + 1`) when the network `net`
is run on input `x`. `ReLU` is applied after every layer except the last one,
matching the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`. -/
def ReLUNetwork.vecAt {n k : ℕ} (net : ReLUNetwork n k) (x : Fin n → ℝ) :
    (i : ℕ) → Fin (net.widths i) → ℝ
  | 0 => net.width_zero.symm ▸ x
  | i + 1 =>
      if h : i < k + 1 then
        let y := (net.layer i h).apply (net.vecAt x i)
        if i < k then reluVec y else y
      else
        fun _ => 0

/-- The real number computed by the network `net` on input `x`. -/
def ReLUNetwork.eval {n k : ℕ} (net : ReLUNetwork n k) (x : Fin n → ℝ) : ℝ :=
  (net.width_last ▸ net.vecAt x (k + 1)) ⟨0, by omega⟩

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network
with at most `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, ∃ net : ReLUNetwork n k', ∀ x, f x = net.eval x}

/-- An affine function `ℝ^n → ℝ`. -/
def IsAffineFun {n : ℕ} (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x, g x = (∑ i, a i * x i) + b

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`:
`f` is continuous, and there is a finite family of affine functions such that
`f` coincides with (at least) one member of that family on a neighbourhood
of every point. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ),
      (∀ j, IsAffineFun (g j)) ∧
      ∀ x : Fin n → ℝ, ∃ j, ∃ U ∈ nhds x, ∀ y ∈ U, f y = g j y}

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from Theorem 2. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL n = ReLUn n (⌈log₃(n-1)⌉ + 1)`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent019

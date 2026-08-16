import Mathlib

namespace Agent060

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

  "Better Neural Network Expressivity: Subdividing the Simplex"
  Bakaev, Brunck, Hertrich, Stade, Yehudayoff.

  Theorem 2. For n ≥ 3, we have CPWL_n = ReLU_{n, ⌈log_3(n−1)⌉ + 1}.

## Modelling choices (see summary at the bottom of the file / final report)

* Vectors `ℝ^n` are modelled as `Fin n → ℝ`.
* Affine transformations `ℝ^a → ℝ^b` are modelled concretely as `x ↦ A.mulVec x + bias`
  for a matrix `A` and bias vector `bias`.
* "Representable with `k` hidden layers" is modelled as an inductive-style existential
  (`represents n k f`) capturing the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` exactly, by peeling off the first affine
  map + ReLU and recursing on the remaining `k` hidden layers.
* `ReLUn n k` is taken to be the functions representable with **at most** `k` hidden
  layers (i.e. with some `k' ≤ k`). This is the reading that makes Theorem 2 a sensible
  equality: extra hidden layers can always be padded in via the identity trick
  `x = ReLU x - ReLU (-x)`, so the "exactly k" and "at most k" classes coincide in
  substance, but "at most k" is the reading under which `ReLUn n k` is monotone in `k`
  and matches the informal statement "representable with k hidden layers" (using no more
  than the allotted depth).
* `CPWL n` is defined genuinely: `f` is continuous, and there is a *finite* family of
  affine functions such that every point of `ℝ^n` has an open neighbourhood on which `f`
  agrees with one member of the family. This is a real piecewise-linearity condition
  (finitely many affine pieces, glued continuously), not a restatement of "computable by
  a ReLU network" and not a max-of-affine normal form.
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined literally via `Real.logb 3` and
  `Nat.ceil` (`⌈·⌉₊`), avoiding any need to relate it to `Nat.clog`.
-/

/-- Vectors in `ℝ^n`, modelled as functions `Fin n → ℝ`. -/
abbrev Vec (n : ℕ) := Fin n → ℝ

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector. -/
def reluVec {n : ℕ} (x : Vec n) : Vec n := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix `A` and a bias
vector, computing `x ↦ A * x + bias`. -/
structure AffMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  bias : Vec b

/-- Evaluation of an affine transformation. -/
def AffMap.eval {a b : ℕ} (T : AffMap a b) (x : Vec a) : Vec b :=
  T.A.mulVec x + T.bias

/-- `represents n k f` holds if `f : ℝ^n → ℝ` is computed by a ReLU network with exactly
`k` hidden layers, i.e. `f` arises as the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations
`T^(1), …, T^(k+1)` with `k` componentwise ReLU applications interleaved (matching the
definition of a ReLU network with `k` hidden layers, depth `k + 1`, from the paper).
We define this by recursion on `k`, peeling off the first affine map together with its
following ReLU, and recursing on the remaining `k` hidden layers of the tail network. -/
def represents : (n : ℕ) → (k : ℕ) → (Vec n → ℝ) → Prop
  | n, 0, f => ∃ T : AffMap n 1, ∀ x, f x = T.eval x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : AffMap n m) (g : Vec m → ℝ),
        represents m k g ∧ ∀ x, f x = g (reluVec (T.eval x))

/-- A function `ℝ^n → ℝ` is affine if it has the form `x ↦ (a ⬝ x) + b` for some vector
`a` of coefficients and scalar `b`. -/
def IsAffine {n : ℕ} (g : Vec n → ℝ) : Prop :=
  ∃ (a : Vec n) (b : ℝ), ∀ x : Vec n, g x = (∑ i, a i * x i) + b

/-- `ReLUn n k`, the set of functions `ℝ^n → ℝ` representable by a ReLU network with at
most `k` hidden layers (see the module docstring for why "at most" is the right reading
for Theorem 2). -/
def ReLUn (n k : ℕ) : Set (Vec n → ℝ) :=
  { f | ∃ k' ≤ k, represents n k' f }

/-- `CPWL n`, the set of continuous piecewise-linear functions `ℝ^n → ℝ`: `f` is
continuous, and there is a finite family of affine functions such that every point of
`ℝ^n` has an open neighbourhood on which `f` agrees with one member of the family. -/
def CPWL (n : ℕ) : Set (Vec n → ℝ) :=
  { f | Continuous f ∧
      ∃ S : Finset (Vec n → ℝ), (∀ g ∈ S, IsAffine g) ∧
        ∀ x : Vec n, ∃ g ∈ S, ∃ U : Set (Vec n), IsOpen U ∧ x ∈ U ∧ Set.EqOn f g U }

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from Theorem 2, defined literally via the real
logarithm `Real.logb 3` and `Nat.ceil`. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 : ∀ n : ℕ, n ≥ 3 → CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent060

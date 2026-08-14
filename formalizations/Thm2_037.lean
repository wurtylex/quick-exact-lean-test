import Mathlib

namespace Agent037

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

  "Better Neural Network Expressivity: Subdividing the Simplex"
  (Bakaev, Brunck, Hertrich, Stade, Yehudayoff)

  Theorem 2. For n ≥ 3, CPWL_n = ReLU_{n, ⌈log_3(n−1)⌉ + 1}.

## Modelling choices

* Vectors `ℝ^n` are encoded as `ℝn n := Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is encoded concretely by a matrix `A` and a
  translation vector `c`, evaluated as `x ↦ A * x + c` (via `Matrix.mulVec`).
* A ReLU network with `k` hidden layers computing `f : ℝn n → ℝ` is defined recursively
  (`computesReLU`): with `0` hidden layers it is a single affine transformation
  `ℝn n → ℝn 1`; with `k+1` hidden layers it is an affine transformation `ℝn n → ℝn m`
  (arbitrary hidden width `m`) followed by componentwise ReLU, whose output is then fed
  into a network with `k` hidden layers. This mirrors the definition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper, unfolded one layer at a time.
* `ReLUn n k` is taken to mean functions representable with **at most** `k` hidden
  layers (i.e. `∃ k' ≤ k, computesReLU k' n f`), not *exactly* `k`. This is the standard
  reading in this literature: extra hidden layers can always simulate fewer ones (e.g. by
  padding with an affine map into two nonnegative "positive/negative part" coordinates and
  subtracting after a ReLU, which realizes the identity), so `ReLU_{n,k}` is monotone in
  `k`, and this is the reading under which the stated equality with `CPWL_n` can hold
  (`CPWL_n` is by definition already closed under "using more layers than needed").
* `CPWL n` is defined mathematically as: continuous functions `f : ℝn n → ℝ` for which
  there is a finite cover of `ℝn n` by (closed) polyhedra, each given as a finite
  intersection of halfspaces, on each of which `f` agrees with some affine function. This
  is a genuine piecewise-linearity condition, independent of any network representation.
* The depth bound `⌈log_3(n−1)⌉ + 1` is encoded using the real logarithm `Real.logb 3`
  together with `Nat.ceil`.
-/

/-- `ℝ^n` encoded as functions `Fin n → ℝ`. -/
abbrev ℝn (n : ℕ) := Fin n → ℝ

/-- The ReLU activation function `max 0 ·` on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector. -/
def reluVec {n : ℕ} (x : ℝn n) : ℝn n := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix `A` and a
translation vector `c`, evaluated as `x ↦ A * x + c`. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : ℝn b

/-- Evaluation of an `AffineMap`. -/
def AffineMap.eval {a b : ℕ} (T : AffineMap a b) (x : ℝn a) : ℝn b :=
  T.A.mulVec x + T.c

/-- `computesReLU k n f` means: `f : ℝn n → ℝ` is computed by a ReLU network with input
dimension `n`, output dimension `1`, and exactly `k` hidden layers, i.e. by the alternating
composition of `k + 1` affine transformations and `k` componentwise applications of ReLU:
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`. -/
def computesReLU : (k : ℕ) → (n : ℕ) → (ℝn n → ℝ) → Prop
  | 0, n, f => ∃ T : AffineMap n 1, ∀ x, f x = T.eval x 0
  | (k + 1), n, f =>
      ∃ (m : ℕ) (T : AffineMap n m) (g : ℝn m → ℝ),
        computesReLU k m g ∧ ∀ x, f x = g (reluVec (T.eval x))

/-- `ReLUn n k`: the functions `ℝn n → ℝ` representable by a ReLU network with at most `k`
hidden layers (see the module docstring for why "at most" rather than "exactly" is the
right reading here). -/
def ReLUn (n k : ℕ) : Set (ℝn n → ℝ) :=
  {f | ∃ k' ≤ k, computesReLU k' n f}

/-- A function `ℝn n → ℝ` is affine if it has the form `x ↦ ⟨a, x⟩ + b`. -/
def IsAffineFn (n : ℕ) (g : ℝn n → ℝ) : Prop :=
  ∃ (a : ℝn n) (b : ℝ), ∀ x, g x = (∑ i, a i * x i) + b

/-- A (closed) polyhedron in `ℝn n`: a finite intersection of closed halfspaces
`{x | ⟨a, x⟩ ≤ b}`. -/
def IsPolyhedron (n : ℕ) (S : Set (ℝn n)) : Prop :=
  ∃ (m : ℕ) (a : Fin m → ℝn n) (b : Fin m → ℝ),
    S = {x | ∀ i, (∑ j, a i j * x j) ≤ b i}

/-- `CPWL n`: the continuous piecewise-linear functions `ℝn n → ℝ`, defined as those
continuous functions for which there is a finite cover of `ℝn n` by polyhedra, on each of
which `f` agrees with some affine function. This is a genuine polyhedral-subdivision
definition, not a "representable by ReLU network" or "max of affine functions" definition. -/
def CPWL (n : ℕ) : Set (ℝn n → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (P : Fin m → Set (ℝn n)) (g : Fin m → ℝn n → ℝ),
          (∀ i, IsPolyhedron n (P i)) ∧
          (∀ i, IsAffineFn n (g i)) ∧
          (∀ x : ℝn n, ∃ i, x ∈ P i) ∧
          (∀ i, ∀ x ∈ P i, f x = g i x) }

/-- The depth bound `⌈log_3(n − 1)⌉ + 1` from Theorem 2, using the real logarithm and
`Nat.ceil`. -/
def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n−1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent037

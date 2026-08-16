import Mathlib

namespace Agent030

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We encode `ℝ^n` as `Fin n → ℝ`.

## Modelling choices (see summary at the end)

* Vectors: `Fin n → ℝ`.
* Affine maps `ℝ^a → ℝ^b` are given concretely as `x ↦ A.mulVec x + c` for a matrix
  `A : Matrix (Fin b) (Fin a) ℝ` and bias `c : Fin b → ℝ`.
* "Computes with `k` hidden layers" is defined by recursion on `k`, directly mirroring the
  alternating composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper.
* `ReLUn n k` is taken to mean *representable with at most `k` hidden layers* (monotone in
  `k`), since that is the reading under which Theorem 2 (an equality, not just an inclusion)
  is the correct/true statement: `CPWL_n` is exhausted already at depth bound `K`, and more
  hidden layers do not produce functions outside `CPWL_n`.
* `CPWL n` is defined as: continuous, and admitting a *finite polyhedral subdivision*
  covering `ℝ^n` (each piece a finite intersection of closed halfspaces) on each piece of
  which `f` agrees with some affine function. This is a genuine geometric definition, not a
  "max of affines" normal form and not "representable by some ReLU network".
* The depth bound uses the real `Real.logb 3` composed with `Nat.ceil`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b` given by a matrix `A` and bias vector `c`,
applied concretely as `x ↦ A * x + c`. -/
def affineMap {a b : ℕ} (A : Matrix (Fin b) (Fin a) ℝ) (c : Fin b → ℝ) :
    (Fin a → ℝ) → (Fin b → ℝ) :=
  fun x => A.mulVec x + c

/-- `f` is affine (as a scalar-valued function `ℝ^n → ℝ`): it equals `a ⬝ x + c` for some
fixed coefficient vector `a` and constant `c`. -/
def IsAffineFn (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (c : ℝ), ∀ x : Fin n → ℝ, f x = (∑ i, a i * x i) + c

/-- A closed halfspace `{x | a ⬝ x ≤ b}` in `ℝ^n`. -/
def IsHalfspace (n : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), S = {x : Fin n → ℝ | (∑ i, a i * x i) ≤ b}

/-- A (closed, possibly unbounded) polyhedron: a finite intersection of closed halfspaces. -/
def IsPolyhedron (n : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (l : ℕ) (H : Fin l → Set (Fin n → ℝ)), (∀ j, IsHalfspace n (H j)) ∧ S = ⋂ j, H j

/-- The space of continuous piecewise-linear functions `ℝ^n → ℝ`: continuous functions that
admit a finite polyhedral subdivision of `ℝ^n` on each piece of which the function is affine. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (P : Fin m → Set (Fin n → ℝ)) (g : Fin m → (Fin n → ℝ) → ℝ),
          (∀ i, IsPolyhedron n (P i)) ∧
          (∀ i, IsAffineFn n (g i)) ∧
          (⋃ i, P i) = Set.univ ∧
          (∀ i, ∀ x ∈ P i, f x = g i x) }

/-- `ComputesWithHiddenLayers n k f` means `f : ℝ^n → ℝ` is computed by a ReLU network with
exactly `k` hidden layers, i.e. by an alternating composition of `k + 1` affine
transformations `T^(1), …, T^(k+1)` with componentwise ReLU applied between consecutive ones:
`f = T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`.

The base case `k = 0` is a single affine map `ℝ^n → ℝ^1` (no hidden layer, no ReLU). The
successor case peels off the first affine map `T^(1) : ℝ^n → ℝ^m` together with the
following ReLU, and recurses on a network `g` with `k` hidden layers computing `ℝ^m → ℝ`. -/
def ComputesWithHiddenLayers : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f =>
      ∃ (A : Matrix (Fin 1) (Fin n) ℝ) (c : Fin 1 → ℝ),
        ∀ x : Fin n → ℝ, f x = affineMap A c x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ) (g : (Fin m → ℝ) → ℝ),
        ComputesWithHiddenLayers m k g ∧
          ∀ x : Fin n → ℝ, f x = g (reluVec (affineMap A c x))

/-- `ReLUn n k`: the functions `ℝ^n → ℝ` representable by a ReLU network with *at most* `k`
hidden layers. (See the modelling-choice note above for why "at most" rather than
"exactly" is the reading that makes Theorem 2 a true equality.) -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, ComputesWithHiddenLayers n k' f }

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent030

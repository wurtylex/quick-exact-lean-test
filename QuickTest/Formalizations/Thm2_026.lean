import Mathlib

namespace Agent026

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We encode `ℝ^n` concretely as `Fin n → ℝ`.

## Modelling choices (see summary at call site)

* `relu` is `max 0 ·` on `ℝ`; `reluVec` applies it componentwise.
* An affine map `ℝ^a → ℝ^b` is a pair `(A, c)` with `A : Matrix (Fin b) (Fin a) ℝ`
  and `c : Fin b → ℝ`, acting as `x ↦ A.mulVec x + c` (spelled out with a `Finset.sum`
  to avoid extra `Matrix` API dependencies).
* A ReLU network with exactly `k` hidden layers, input dimension `n`, output dimension
  `m`, is encoded by the recursively defined type `NetParams n m k`: for `k = 0` it is
  a single affine map `ℝ^n → ℝ^m` (depth 1, 0 hidden layers); for `k+1` it is a choice of
  hidden width `h`, an affine map `ℝ^n → ℝ^h`, and a `(h, m, k)`-network for the rest.
  `NetParams.eval` unfolds this exactly as the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`.
* `ReLUn n k` is taken to be the set of functions representable with **at most** `k`
  hidden layers (existentially quantifying `k' ≤ k`). This is the standard reading in
  the depth-separation literature: it makes `ReLUn n ·` monotone nondecreasing in `k`,
  so that the equality `CPWL n = ReLUn n (⌈log_3(n-1)⌉+1)` expresses "this many hidden
  layers already suffice to reach the full class `CPWL n`, and no representable function
  ever leaves that class" — the natural way to read `MAX_{3^n+2} ∈ ReLU_{n+1}` extending
  monotonically. (Reading it as *exactly* `k` would make the statement false or
  ill-behaved for trivial reasons, e.g. constant functions needing padding layers.)
* `CPWL n` is defined as: `f` is continuous **and** there is a finite family of
  polyhedra (finite intersections of affine half-spaces) covering `ℝ^n`, on each of
  which `f` agrees with some affine function. This is a genuine piecewise-linearity
  condition (a finite polyhedral subdivision), not a max-of-affine normal form and not
  "representable by a ReLU network".
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined literally with `Real.logb 3` and
  `Nat.ceil` (`⌈·⌉₊`).
-/

noncomputable section

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^n`. -/
def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given by a matrix and a bias vector. -/
def AffineMap' (a b : ℕ) : Type := Matrix (Fin b) (Fin a) ℝ × (Fin b → ℝ)

/-- Evaluate an affine transformation `x ↦ A x + c`. -/
def applyAffine {a b : ℕ} (T : AffineMap' a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, T.1 i j * x j) + T.2 i

/-- Parameters of a ReLU network with input dimension `n`, output dimension `m`,
and exactly `k` hidden layers: for `k = 0` a single affine map, for `k + 1` a hidden
width `h`, an affine map `ℝ^n → ℝ^h`, together with the parameters of the remaining
`(h, m, k)`-network (to be composed with `ReLU` in between). -/
def NetParams (n m : ℕ) : ℕ → Type
  | 0 => AffineMap' n m
  | k + 1 => Σ h : ℕ, AffineMap' n h × NetParams h m k

/-- The function `ℝ^n → ℝ^m` computed by a ReLU network, i.e. the alternating
composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`. -/
def NetParams.eval {n m : ℕ} : (k : ℕ) → NetParams n m k → (Fin n → ℝ) → (Fin m → ℝ)
  | 0, T, x => applyAffine T x
  | k + 1, ⟨_, T, rest⟩, x => NetParams.eval k rest (reluVec (applyAffine T x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network
with **at most** `k` hidden layers (output dimension `1`). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, ∃ P : NetParams n 1 k', f = fun x => NetParams.eval k' P x 0 }

/-- A polyhedron in `ℝ^n`: a finite intersection of closed affine half-spaces. -/
def IsPolyhedron {n : ℕ} (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (a : Fin m → (Fin n → ℝ)) (b : Fin m → ℝ),
    S = ⋂ i, {x : Fin n → ℝ | (∑ j, a i j * x j) ≤ b i}

/-- `CPWL n` is the set of continuous, piecewise affine functions `ℝ^n → ℝ`: those `f`
that are continuous and admit a finite polyhedral subdivision of `ℝ^n` on each piece of
which `f` agrees with some affine function. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
      ∃ (m : ℕ) (S : Fin m → Set (Fin n → ℝ)) (A : Fin m → (Fin n → ℝ)) (c : Fin m → ℝ),
        (∀ i, IsPolyhedron (S i)) ∧
        (⋃ i, S i) = Set.univ ∧
        ∀ i, ∀ x ∈ S i, f x = (∑ j, A i j * x j) + c i }

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from the theorem statement. -/
noncomputable def depthBound (n : ℕ) : ℕ := ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

end

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉+1}`. -/
theorem theorem2 : ∀ n : ℕ, n ≥ 3 → CPWL n = ReLUn n (depthBound n) := sorry

end Agent026

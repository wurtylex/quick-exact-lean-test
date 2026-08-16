import Mathlib

namespace Agent063

open scoped BigOperators

/-- The ReLU activation function on `ℝ`. -/
def reluR (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => reluR (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given explicitly by a matrix `A` (encoded as a
function `Fin b → Fin a → ℝ`) and a bias vector `c`: `x ↦ A x + c`. -/
def affineApply {a b : ℕ} (A : Fin b → Fin a → ℝ) (c : Fin b → ℝ) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j : Fin a, A i j * x j) + c i

/-- `f : ℝ^n → ℝ` is a scalar affine function, i.e. what a ReLU network with `0` hidden
layers (a single affine transformation `ℝ^n → ℝ^1`, identified with `ℝ`) computes. -/
def IsAffine (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (c : Fin n → ℝ) (b : ℝ), ∀ x, f x = (∑ i : Fin n, c i * x i) + b

/-- `Represents n k f` : `f : ℝ^n → ℝ` is computed by a ReLU network with *exactly* `k`
hidden layers, in the sense of the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations
`T^(1), …, T^(k+1)` (of possibly different widths), with componentwise ReLU applied after
each of the first `k` of them.

Defined by recursion on `k`: with `0` hidden layers the network is a single affine map
`ℝ^n → ℝ` (`T^(1)` alone, no ReLU applied). With `k + 1` hidden layers, the first affine
map `T^(1) : ℝ^n → ℝ^m` (of some width `m`) is applied, then ReLU is applied componentwise,
and the remaining `k` hidden layers compute some `g : ℝ^m → ℝ` from the result, matching
`f = g ∘ ReLU ∘ T^(1)`. -/
def Represents : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => IsAffine n f
  | n, (k + 1), f =>
      ∃ (m : ℕ) (A : Fin m → Fin n → ℝ) (bvec : Fin m → ℝ) (g : (Fin m → ℝ) → ℝ),
        Represents m k g ∧ ∀ x, f x = g (reluVec (affineApply A bvec x))

/-- `ReLUn n k` : the functions `ℝ^n → ℝ` representable by a ReLU network with *at most*
`k` hidden layers. We read `ReLU_{n,k}` as "at most `k`" rather than "exactly `k`": this is
the standard convention in the expressivity literature, it makes the class monotone in
`k`, and it is the reading under which Theorem 2's equality `CPWL_n = ReLU_{n,k}` for a
*single, fixed* depth `k = ⌈log_3(n-1)⌉ + 1` can hold — e.g. affine functions
(representable with `0` hidden layers) must lie in `ReLU_{n,k}` for every `k ≥ 0`, which
holds definitionally only under the "at most" reading. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, Represents n k' f}

/-- A closed polyhedron in `ℝ^n`: a finite intersection of affine half-spaces
`{x | a_j ⬝ x + b_j ≤ 0}`. -/
def IsPolyhedron (n : ℕ) (P : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (a : Fin m → Fin n → ℝ) (b : Fin m → ℝ),
    P = {x | ∀ j : Fin m, (∑ i : Fin n, a j i * x i) + b j ≤ 0}

/-- `f : ℝ^n → ℝ` is continuous and piecewise linear: `f` is continuous, and there is a
finite family of closed polyhedra covering all of `ℝ^n`, on each of which `f` agrees with
some affine function. This is a genuine finite polyhedral subdivision, not merely
"representable by some ReLU network" and not a max-of-affine normal form. -/
def IsCPWL (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  Continuous f ∧
    ∃ (m : ℕ) (P : Fin m → Set (Fin n → ℝ)) (g : Fin m → (Fin n → ℝ) → ℝ),
      (∀ j, IsPolyhedron n (P j)) ∧
      (∀ j, IsAffine n (g j)) ∧
      (⋃ j, P j) = Set.univ ∧
      (∀ j, ∀ x ∈ P j, f x = g j x)

/-- `CPWL n` : the set of continuous piecewise linear functions `ℝ^n → ℝ`. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) := {f | IsCPWL n f}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so that
`n - 1 ≥ 2 > 0` and the real logarithm behaves as expected). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) : CPWL n = ReLUn n (depthBound n) := sorry

end Agent063

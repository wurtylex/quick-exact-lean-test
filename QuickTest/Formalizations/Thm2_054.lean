import Mathlib

namespace Agent054

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

"Better Neural Network Expressivity: Subdividing the Simplex"
(Bakaev, Brunck, Hertrich, Stade, Yehudayoff).

Theorem 2. For n ≥ 3, we have CPWL_n = ReLU_{n, ⌈log_3(n−1)⌉ + 1}.

## Modelling choices

* `ℝ^n` is modelled as `Vec n := Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is modelled concretely as
  `x ↦ A *ᵥ x + c` for a matrix `A` and a vector `c` (structure `AffineMap`).
* A ReLU network with exactly `k` hidden layers computing `f : Vec n → ℝ` is
  defined by recursion on `k`: with `0` hidden layers it is a single affine
  map into `ℝ`; with `k+1` hidden layers it is an affine map into some hidden
  width `m`, followed by componentwise ReLU, followed by a `k`-hidden-layer
  network on the resulting `m`-dimensional vector. This exactly reproduces
  the alternating composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`
  from the paper, with `k+1` affine maps and `k` applications of ReLU.
* `ReLUn n k` is taken to be the set of functions representable with **at
  most** `k` hidden layers (the standard reading in the depth-hierarchy
  literature, and the one under which `ReLUn n k` is monotone in `k`, so
  that the statement "the exact threshold depth `⌈log_3(n-1)⌉+1` suffices
  and is necessary" is a meaningful, non-vacuous equality with `CPWL n`).
* `CPWL n` is defined as: `f` is continuous **and** there is a finite family
  of closed convex regions covering `ℝ^n`, together with an affine function
  for each region, such that `f` agrees with the corresponding affine
  function on each region. This is a genuine piecewise-linearity condition
  (finite polyhedral-type subdivision + local affine agreement), not a
  "representable by a ReLU network" or "max of affine functions" definition.
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined using the real logarithm
  `Real.logb 3` together with `Nat.ceil`.
-/

/-- We model `ℝ^n` concretely as functions `Fin n → ℝ`. -/
abbrev Vec (n : ℕ) := Fin n → ℝ

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of ReLU to a vector. -/
def reluVec {n : ℕ} (x : Vec n) : Vec n := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix `A`
and a translation vector `c`, acting as `x ↦ A * x + c`. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Vec b

/-- The function computed by an affine transformation. -/
def AffineMap.eval {a b : ℕ} (T : AffineMap a b) (x : Vec a) : Vec b :=
  Matrix.mulVec T.A x + T.c

/-- `NetComputes k n f` means `f : ℝ^n → ℝ` is computed (exactly) by a ReLU
network with `k` hidden layers, i.e. by an alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine
transformations (with freely chosen hidden widths) and `k` componentwise
applications of ReLU. -/
def NetComputes : (k : ℕ) → (n : ℕ) → (Vec n → ℝ) → Prop
  | 0, n, f => ∃ T : AffineMap n 1, f = fun x => T.eval x 0
  | (k + 1), n, f =>
      ∃ (m : ℕ) (T : AffineMap n m) (g : Vec m → ℝ),
        NetComputes k m g ∧ f = fun x => g (reluVec (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU
network with **at most** `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set (Vec n → ℝ) :=
  { f | ∃ k' ≤ k, NetComputes k' n f }

/-- A scalar-valued affine function `ℝ^n → ℝ`. -/
def IsAffineFun (n : ℕ) (f : Vec n → ℝ) : Prop :=
  ∃ (w : Vec n) (b : ℝ), f = fun x => (∑ i, w i * x i) + b

/-- `CPWL n` is the set of continuous, piecewise linear functions `ℝ^n → ℝ`:
functions that are continuous and admit a finite covering of `ℝ^n` by
closed convex regions, on each of which `f` agrees with some affine
function. -/
def CPWL (n : ℕ) : Set (Vec n → ℝ) :=
  { f | Continuous f ∧
      ∃ (m : ℕ) (P : Fin m → Set (Vec n)) (a : Fin m → (Vec n → ℝ)),
        (∀ i, Convex ℝ (P i)) ∧
        (∀ i, IsClosed (P i)) ∧
        (⋃ i, P i) = Set.univ ∧
        (∀ i, IsAffineFun n (a i)) ∧
        (∀ i x, x ∈ P i → f x = a i x) }

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from the statement of Theorem 2. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL n = ReLUn n (⌈log_3(n-1)⌉ + 1)`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent054

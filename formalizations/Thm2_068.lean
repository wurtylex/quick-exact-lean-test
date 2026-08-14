import Mathlib

namespace Agent068

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

  Theorem 2. For n ≥ 3, CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}.

## Modelling choices

* The *input/output* space `ℝ^n` for the functions in `CPWL n` and `ReLUn n k` is encoded
  as `Fin n → ℝ`.
* Internally, the *hidden layers* of a ReLU network are encoded using the ambient
  "infinite vector" type `Vec := ℕ → ℝ`. An affine transformation is data consisting of a
  matrix `A : ℕ → ℕ → ℝ` and a bias vector, evaluated by summing over the first `inDim`
  coordinates only (`inDim` supplied at evaluation time). This avoids having to carry
  dependent equality proofs / `cast`s between `Fin (width i) → ℝ` types at every layer of
  the network, while still faithfully modelling "matrix times vector plus bias" affine
  maps between spaces of the prescribed (finite) dimensions.
* `ReLUn n k` is defined using the **"at most k hidden layers"** reading (i.e. as a union
  over `k' ≤ k` of the functions computable with *exactly* `k'` hidden layers). This is the
  reading that makes Theorem 2 true as a literal set equality: `ReLUn n k` must be
  monotone (increasing) in `k`, since e.g. all affine functions (0 hidden layers) lie in
  `CPWL n` and hence must lie in `ReLUn n K` for the specific depth bound `K`, and
  more generally the right-hand side of the theorem should contain everything representable
  with fewer than the stated number of hidden layers too.
* `CPWL n` is defined directly as: `f` is continuous, and there is a *finite* family of
  convex regions covering `ℝ^n` together with a matching finite family of affine functions,
  such that `f` agrees with the corresponding affine function on each region. This is a
  genuine piecewise-linearity condition (a finite polyhedral-type subdivision on each piece
  of which `f` is affine) and is deliberately *not* phrased as "representable by some ReLU
  network" nor as a max-of-affine-functions normal form.
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded using `Real.logb 3` and `Nat.ceil`.
-/

/-- The ambient space used internally for the (possibly high-dimensional) hidden layers of
a ReLU network: an "infinite vector", i.e. a function `ℕ → ℝ`, of which only finitely many
coordinates are ever actually used by a given network. -/
abbrev Vec := ℕ → ℝ

/-- The ReLU activation function `ReLU(x) = max{0, x}`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector. -/
def reluVec (x : Vec) : Vec := fun i => relu (x i)

/-- An affine transformation, given concretely as a matrix `A` (`A i j` is the `(i,j)`
entry) together with a bias vector. Evaluation is with respect to an explicit input
dimension `inDim`, so that `T.eval inDim x` computes `A * x + bias`, restricting the matrix
product to the first `inDim` coordinates of `x` (the mathematically relevant ones for an
input space of dimension `inDim`). -/
structure AffineMap where
  A : ℕ → ℕ → ℝ
  bias : Vec

/-- Evaluate an affine transformation `x ↦ A * x + bias`, with `A * x` summed over the
first `inDim` coordinates of `x` (the input dimension of this affine map). -/
def AffineMap.eval (T : AffineMap) (inDim : ℕ) (x : Vec) : Vec :=
  fun i => (Finset.range inDim).sum (fun j => T.A i j * x j) + T.bias i

/-- Apply `i` layers of "affine transformation followed by componentwise ReLU" to an input
vector, given a sequence `width : ℕ → ℕ` of layer widths (`width 0` is the input dimension)
and a sequence `T : ℕ → AffineMap` of affine transformations (`T j` maps from dimension
`width j` to dimension `width (j+1)`). -/
def networkForward (width : ℕ → ℕ) (T : ℕ → AffineMap) : ℕ → Vec → Vec
  | 0, x => x
  | (i + 1), x => reluVec ((T i).eval (width i) (networkForward width T i x))

/-- The scalar output computed by a network with `k` hidden layers: apply `k` layers of
affine-then-ReLU (via `networkForward`), then one final affine transformation `T k`
*without* a following ReLU, and read off the (single, by convention coordinate `0`) output
coordinate. This realizes the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper, with `T^(i)` corresponding to
`T (i-1)` here. -/
def networkCompute (width : ℕ → ℕ) (T : ℕ → AffineMap) (k : ℕ) (x : Vec) : ℝ :=
  ((T k).eval (width k) (networkForward width T k x)) 0

/-- Embed a finite-dimensional vector `x : Fin n → ℝ` into the ambient space `Vec`, padding
with zeros outside the first `n` coordinates. -/
def toVec (n : ℕ) (x : Fin n → ℝ) : Vec :=
  fun i => if h : i < n then x ⟨i, h⟩ else 0

/-- A ReLU network with input dimension `n` and exactly `k` hidden layers: a sequence of
layer widths `width 0, …, width (k+1)` with `width 0 = n` (the input dimension) and
`width (k+1) = 1` (the network outputs a scalar), together with the `k+1` affine
transformations `T 0, …, T k` of the alternating composition. -/
structure ReLUNetwork (n k : ℕ) where
  width : ℕ → ℕ
  hw0 : width 0 = n
  hwlast : width (k + 1) = 1
  T : ℕ → AffineMap

/-- The function `ℝ^n → ℝ` computed by a ReLU network. -/
def ReLUNetwork.compute (net : ReLUNetwork n k) (x : Fin n → ℝ) : ℝ :=
  networkCompute net.width net.T k (toVec n x)

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers (the union over `k' ≤ k` of those representable with exactly
`k'` hidden layers). See the module docstring for why "at most" (rather than "exactly") is
the reading under which Theorem 2 is a true statement. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, ∃ net : ReLUNetwork n k', f = net.compute }

/-- A function `ℝ^n → ℝ` is affine if it has the form `x ↦ ⟨a, x⟩ + b` for some vector `a`
and scalar `b`. -/
def IsAffineFun (n : ℕ) (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x : Fin n → ℝ, g x = (Finset.univ.sum fun i => a i * x i) + b

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: those `f` that
are continuous and admit a *finite* subdivision of `ℝ^n` into convex regions, together with
a matching finite family of affine functions, such that `f` agrees with the corresponding
affine function on each region of the subdivision. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (pieces : Fin m → (Fin n → ℝ) → ℝ) (region : Fin m → Set (Fin n → ℝ)),
          (∀ i, IsAffineFun n (pieces i)) ∧
          (∀ i, Convex ℝ (region i)) ∧
          (⋃ i, region i) = Set.univ ∧
          (∀ i (x : Fin n → ℝ), x ∈ region i → f x = pieces i x) }

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from the paper, for `n ≥ 3` (so `n - 1 ≥ 2 > 0` and
the logarithm is well-behaved). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) : CPWL n = ReLUn n (depthBound n) := sorry

end Agent068

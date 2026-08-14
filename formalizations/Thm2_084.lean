import Mathlib

namespace Agent084

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

  "For n ≥ 3, we have  CPWL_n = ReLU_{n, ⌈log_3(n−1)⌉ + 1}."

## Modelling choices

* Vectors `ℝ^n` are modelled as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` used inside a network layer is modelled
  concretely by a matrix and a bias vector (`AffineLayer`), evaluated as
  `x ↦ A * x + bias`.
* A ReLU network with `k` hidden layers computing `y` from input `x` is defined
  by recursion on `k` (`IsReLUNetworkOutput`), literally unfolding the
  alternating composition
  `T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}`
  from the paper, peeling off one affine layer + one ReLU at a time.
* `ReLUn n k` is taken to be functions computable with **at most** `k` hidden
  layers (`∃ k' ≤ k, ...`), not exactly `k`. This is the standard reading of
  `ReLU_{n,k}` (a network with `k` hidden layers can always simulate one with
  fewer hidden layers, e.g. by padding with layers that emulate the identity
  via `x = ReLU(x) - ReLU(-x)`), and it is the reading under which an equality
  statement like Theorem 2 is the natural one to state/prove.
* `CPWL n` is defined honestly as: continuous functions that additionally
  admit a *finite polyhedral subdivision* (a finite family of polyhedra,
  each cut out by finitely many affine inequalities, covering `ℝ^n`) on each
  piece of which the function agrees with an affine functional. This is a
  genuine piecewise-linearity condition, not a disguised "representable by a
  ReLU network" or "max of affine functions" definition.
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined literally via `Real.logb 3`
  and `Nat.ceil` (`⌈·⌉₊`), matching the paper's real-valued ceiling of a
  real logarithm.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a
bias vector: `x ↦ A * x + bias`. -/
structure AffineLayer (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  bias : Fin b → ℝ

/-- Evaluation of an `AffineLayer` at a point. -/
def AffineLayer.eval {a b : ℕ} (T : AffineLayer a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (T.A.mulVec x) i + T.bias i

/--
`IsReLUNetworkOutput n k x y` says that `y` is the value at `x` of *some*
function computed by a ReLU network with input dimension `n`, exactly `k`
hidden layers, and output dimension `1`, i.e. `y` is obtained from `x` by the
alternating composition
`T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}`
of `k + 1` affine transformations with componentwise ReLU, for some choice of
hidden-layer widths and affine transformations.

Defined by recursion on `k`: the base case `k = 0` is a single affine
transformation `ℝ^n → ℝ` (depth 1, no hidden layers); the successor case peels
off the first affine layer `T^{(1)} : ℝ^n → ℝ^m` together with the following
ReLU, and recurses on the remaining `k` hidden layers.
-/
def IsReLUNetworkOutput : (n k : ℕ) → (Fin n → ℝ) → ℝ → Prop
  | n, 0, x, y => ∃ T : AffineLayer n 1, T.eval x 0 = y
  | n, (k + 1), x, y =>
      ∃ (m : ℕ) (T : AffineLayer n m) (z : Fin m → ℝ),
        z = reluVec (T.eval x) ∧ IsReLUNetworkOutput m k z y

/--
`ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network
with **at most** `k` hidden layers, i.e. `f ∈ ReLUn n k` iff there is some
`k' ≤ k` and a `k'`-hidden-layer network whose output on every input `x`
equals `f x`.
-/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, ∀ x, IsReLUNetworkOutput n k' x (f x) }

/-- An affine functional `ℝ^n → ℝ`, `x ↦ ⟨coeff, x⟩ + const`. -/
structure AffineFunctional (n : ℕ) where
  coeff : Fin n → ℝ
  const : ℝ

/-- Evaluation of an `AffineFunctional`. -/
def AffineFunctional.eval {n : ℕ} (g : AffineFunctional n) (x : Fin n → ℝ) : ℝ :=
  (∑ i, g.coeff i * x i) + g.const

/-- A closed halfspace `{x | ⟨normal, x⟩ ≤ bound}` of `ℝ^n`. -/
structure Halfspace (n : ℕ) where
  normal : Fin n → ℝ
  bound : ℝ

/-- Membership of a point in a `Halfspace`. -/
def Halfspace.mem {n : ℕ} (H : Halfspace n) (x : Fin n → ℝ) : Prop :=
  (∑ i, H.normal i * x i) ≤ H.bound

/-- A (closed, convex) polyhedron of `ℝ^n`: a finite intersection of
halfspaces, represented as a list of the defining halfspaces. -/
def Polyhedron (n : ℕ) := List (Halfspace n)

/-- Membership of a point in a `Polyhedron`, i.e. it satisfies all the
defining halfspace inequalities. -/
def Polyhedron.mem {n : ℕ} (P : Polyhedron n) (x : Fin n → ℝ) : Prop :=
  ∀ H ∈ P, H.mem x

/--
`CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`:
functions `f` that are continuous, and for which there is a **finite**
polyhedral subdivision of `ℝ^n` (indexed by `Fin N`) — a finite family of
polyhedra covering `ℝ^n` — on each piece of which `f` agrees with some affine
functional.
-/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (N : ℕ) (P : Fin N → Polyhedron n) (g : Fin N → AffineFunctional n),
          (∀ x, ∃ i, (P i).mem x) ∧ (∀ i x, (P i).mem x → f x = (g i).eval x) }

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from Theorem 2, defined literally via
the real logarithm base `3` and the natural-number ceiling. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent084

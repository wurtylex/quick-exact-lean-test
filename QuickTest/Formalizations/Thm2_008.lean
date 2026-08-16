import Mathlib

namespace Agent008

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We model `ℝ^n` as `Fin n → ℝ`.

Modelling choices (see summary at the end of the task):
* Affine maps `ℝ^a → ℝ^b` are given explicitly and concretely by a matrix and a bias
  vector, `x ↦ A * x + c`.
* A ReLU network with `k` hidden layers is captured by the inductive relation
  `NetworkComputes n k f`, which unwinds exactly the alternating composition
  `T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}` from the paper's definition.
* `ReLUn n k` is the set of functions computable with **at most** `k` hidden layers
  (an existential over `j ≤ k`). This is the reading under which `ReLU_{n,k}` is
  monotone increasing in `k` (extra hidden layers can never hurt, since one can always
  route a signal through an extra affine + ReLU layer without changing the represented
  function), which is the natural reading that makes Theorem 2 an *equality* of sets
  rather than a bare inclusion.
* `CPWL n` is defined genuinely: continuity, together with a finite polyhedral
  subdivision of `ℝ^n` (each piece cut out by finitely many affine inequality
  constraints, i.e. an intersection of closed half-spaces) on each piece of which `f`
  agrees with some affine function.
* The depth bound `⌈log_3 (n-1)⌉ + 1` is defined directly from `Real.logb` and
  `Nat.ceil`, matching the paper's real-valued ceiling-of-log expression verbatim.
-/

/-- The ReLU function on `ℝ`. -/
noncomputable def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^n = Fin n → ℝ`. -/
noncomputable def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given explicitly and concretely by a matrix
`A` and a bias (translation) vector `c`, acting as `x ↦ A * x + c`. -/
structure AffineMap' (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- The function `ℝ^a → ℝ^b` computed by an `AffineMap'`. -/
noncomputable def AffineMap'.apply {a b : ℕ} (T : AffineMap' a b) (x : Fin a → ℝ) :
    Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `NetworkComputes n k f` holds when `f : ℝ^n → ℝ` is computed by a ReLU network with
input dimension `n` and exactly `k` hidden layers, i.e. by some alternating composition
`T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}` of affine transformations `T^{(i)}`
with componentwise ReLU, as in the paper's definition of a depth-`(k+1)` ReLU network.

* `base` is the case `k = 0` (no hidden layers): the network is a single affine map
  `T^{(1)} : ℝ^n → ℝ`.
* `step` peels off the first affine map `T^{(1)} : ℝ^n → ℝ^m` and the first `ReLU`,
  leaving a network with `k` hidden layers computing `g : ℝ^m → ℝ`; together they
  compute `x ↦ g (ReLU (T^{(1)} x))`, a network with `k + 1` hidden layers on `ℝ^n`. -/
inductive NetworkComputes : (n : ℕ) → (k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | base {n : ℕ} (T : AffineMap' n 1) :
      NetworkComputes n 0 (fun x => T.apply x 0)
  | step {n m k : ℕ} (T : AffineMap' n m) {g : (Fin m → ℝ) → ℝ}
      (hg : NetworkComputes m k g) :
      NetworkComputes n (k + 1) (fun x => g (reluVec (T.apply x)))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
**at most** `k` hidden layers (see the module docstring for why "at most" is the right
reading here). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ j ≤ k, NetworkComputes n j f }

/-- A set `P ⊆ ℝ^n` is a polyhedron if it is a finite intersection of closed half-spaces,
i.e. cut out by finitely many affine inequality constraints `A x ≤ b`. -/
def IsPolyhedron {n : ℕ} (P : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ),
    P = { x | A.mulVec x ≤ b }

/-- `CPWL n` is the space of continuous, piecewise linear (really: piecewise affine)
functions `ℝ^n → ℝ`: those `f` that are continuous and admit a finite polyhedral
subdivision of `ℝ^n` into pieces `P i`, on each of which `f` agrees with some affine
function `g i`. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
      ∃ (m : ℕ) (P : Fin m → Set (Fin n → ℝ)) (g : Fin m → AffineMap' n 1),
        (∀ i, IsPolyhedron (P i)) ∧
        (⋃ i, P i) = Set.univ ∧
        ∀ i, ∀ x ∈ P i, f x = (g i).apply x 0 }

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, computed via the real
logarithm `Real.logb 3` and the natural-number ceiling. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL n = ReLUn n (⌈log_3 (n - 1)⌉ + 1)`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent008

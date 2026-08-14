import Mathlib

namespace Agent059

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):  for `n ≥ 3`,  `CPWL n = ReLUn n (⌈log_3 (n-1)⌉ + 1)`.

## Modelling choices

* Vectors `ℝ^n` are encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is given concretely by a weight function
  `A : Fin b → Fin a → ℝ` (playing the role of a `b × a` matrix) and a bias
  `bias : Fin b → ℝ`, acting by `x ↦ A * x + bias`.
* A ReLU network with `k` hidden layers computing `f : ℝ^n → ℝ` is encoded
  recursively (`ReLURepresentable`): with `0` hidden layers, `f` must itself be an
  affine function (this is the single transformation `T^(1) : ℝ^n → ℝ`); with
  `k+1` hidden layers, `f` factors as `g ∘ ReLU ∘ T` where `T : ℝ^n → ℝ^m` is an
  affine transformation and `g : ℝ^m → ℝ` is representable with `k` hidden layers.
  Unwinding the recursion recovers exactly the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper.
* `ReLUn n k` is taken to be the functions representable with **at most** `k`
  hidden layers (`∃ j ≤ k, ReLURepresentable n j f`), not exactly `k`. This is the
  standard reading (a network with `j` hidden layers can always be padded to `k ≥ j`
  hidden layers, e.g. using `x = ReLU x - ReLU (-x)` as an identity pass-through
  layer), and it is also the reading under which the stated equality
  `CPWL n = ReLUn n (⌈log_3 (n-1)⌉ + 1)` can be true: e.g. affine functions lie in
  `CPWL n` but are representable with `0` hidden layers, not exactly
  `⌈log_3 (n-1)⌉ + 1` of them.
* `CPWL n` is defined as: `f` is continuous, and there is a finite polyhedral
  subdivision of `ℝ^n` (finitely many closed polyhedra, each cut out by finitely
  many affine inequalities, whose union is all of `ℝ^n`) on each piece of which `f`
  agrees with some affine function. This is a genuine piecewise-linearity condition,
  not a "representable by some ReLU network" definition and not a max-of-affine
  normal form.
* The depth bound is `Nat.ceil (Real.logb 3 (n - 1)) + 1`, matching
  `⌈log_3(n-1)⌉ + 1` with the real base-3 logarithm and the real ceiling.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `Fin m → ℝ`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- A concrete affine transformation `ℝ^a → ℝ^b`, given by a weight function
`A` (playing the role of a `b × a` matrix) and a bias vector, acting as
`x ↦ A * x + bias`. -/
structure AffineMap (a b : ℕ) where
  A : Fin b → Fin a → ℝ
  bias : Fin b → ℝ

/-- Evaluation of an `AffineMap`. -/
def AffineMap.eval {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, T.A i j * x j) + T.bias i

/-- `f : ℝ^n → ℝ` is an affine (real-valued) function. -/
def IsAffineFun {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (w : Fin n → ℝ) (c : ℝ), ∀ x, f x = (∑ j, w j * x j) + c

/-- `f` is representable by a ReLU network `ℝ^n → ℝ` with exactly `k` hidden
layers: with `0` hidden layers `f` must itself be affine (the single affine
transformation `T^(1)`); with `k + 1` hidden layers, `f` factors as
`g ∘ ReLU ∘ T` for an affine `T : ℝ^n → ℝ^m` and `g` representable with `k`
hidden layers. Unwinding this recursion gives precisely the alternating
composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`. -/
def ReLURepresentable : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => IsAffineFun f
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : AffineMap n m) (g : (Fin m → ℝ) → ℝ),
        ReLURepresentable m k g ∧ f = fun x => g (reluVec (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU
network with **at most** `k` hidden layers (see the module docstring for why
"at most", rather than "exactly", is the right reading here). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ j ≤ k, ReLURepresentable n j f }

/-- A closed polyhedron in `ℝ^n`, cut out by finitely many affine
inequalities `⟨a i, x⟩ ≤ b i`. -/
def IsPolyhedron {n : ℕ} (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (a : Fin m → (Fin n → ℝ)) (b : Fin m → ℝ),
    S = {x | ∀ i, (∑ j, a i j * x j) ≤ b i}

/-- `CPWL n`: the continuous, piecewise-linear functions `ℝ^n → ℝ`. `f` is
continuous, and there is a finite polyhedral subdivision of `ℝ^n` (finitely
many closed polyhedra whose union is all of `ℝ^n`) on each piece of which `f`
agrees with some affine function. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
      ∃ (m : ℕ) (S : Fin m → Set (Fin n → ℝ)) (g : Fin m → (Fin n → ℝ) → ℝ),
        (∀ i, IsPolyhedron (S i)) ∧
        (∀ i, IsAffineFun (g i)) ∧
        (⋃ i, S i) = Set.univ ∧
        (∀ i, ∀ x ∈ S i, f x = g i x) }

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from the theorem, using the real
base-3 logarithm and the real (`Nat.ceil`) ceiling. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent059

import Mathlib

namespace Agent046

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

  "For n ≥ 3, we have CPWL_n = ReLU_{n, ⌈log_3(n−1)⌉ + 1}."

## Modelling choices

* Vectors `ℝ^m` are encoded as `Fin m → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is encoded concretely as a matrix `A : Matrix
  (Fin b) (Fin a) ℝ` together with a bias vector, applied as `x ↦ A x + bias`.
* A ReLU network with `k` hidden layers computing `f : ℝ^n → ℝ` is defined by
  *structural recursion on `k`*: with `0` hidden layers, `f` is exactly one affine map
  `ℝ^n → ℝ`; with `k+1` hidden layers, `f` factors as `g ∘ ReLU ∘ T` where `T : ℝ^n → ℝ^m`
  is affine and `g` is computable with `k` hidden layers on `ℝ^m`. This directly encodes
  the alternating composition `T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}` from the
  paper.
* `ReLUn n k` is taken to be functions representable with **at most** `k` hidden layers
  (i.e. the union over `k' ≤ k` of the exactly-`k'` classes). This is the standard reading
  in the depth-separation literature and is the one that makes Theorem 2 meaningful: the
  classes `ReLUn n k` must be monotone increasing in `k` for "the smallest `k` for which
  `ReLUn n k` already covers all of `CPWL n`" to make sense as an equality statement.
* `CPWL n` is defined mathematically (not via ReLU networks!) as: continuous functions
  `f : ℝ^n → ℝ` admitting a *finite* subdivision of `ℝ^n` into polyhedral pieces (each a
  finite intersection of halfspaces) covering `ℝ^n`, on each of which `f` agrees with some
  affine function from a finite list.
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded literally using `Real.logb 3` and
  `Nat.ceil` (`⌈·⌉₊`), applied to the real number `(n - 1 : ℝ)` (ordinary real subtraction
  of the cast of `n`, not truncated natural subtraction).
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of ReLU to a vector. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias
vector: `x ↦ A x + bias`. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  bias : Fin b → ℝ

/-- Evaluating an `AffineMap` at a point. -/
def AffineMap.apply {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, T.A i j * x j) + T.bias i

/-- `NetComputes n k f` means `f : ℝ^n → ℝ` is computed by some ReLU network with exactly
`k` hidden layers, i.e. `f` is the alternating composition
`T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}` of `k + 1` affine transformations with
componentwise ReLU applications between consecutive ones. Defined by recursion on `k`:
with `0` hidden layers a single affine map `ℝ^n → ℝ` is applied; with `k + 1` hidden
layers, an affine map `T : ℝ^n → ℝ^m` is applied, then `ReLU`, and the remaining `k`
hidden layers compute `g` on `ℝ^m`, with `f = g ∘ ReLU ∘ T`. -/
def NetComputes : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : AffineMap n 1, f = fun x => T.apply x 0
  | n, k + 1, f =>
      ∃ (m : ℕ) (T : AffineMap n m) (g : (Fin m → ℝ) → ℝ),
        NetComputes m k g ∧ f = fun x => g (reluVec (T.apply x))

/-- `ReLUn n k`, the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, NetComputes n k' f }

/-- A function `ℝ^n → ℝ` is affine if it has the form `x ↦ c ⬝ x + d` for some vector `c`
and constant `d`. -/
def IsAffineFun (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (c : Fin n → ℝ) (d : ℝ), ∀ x, f x = (∑ i, c i * x i) + d

/-- A subset of `ℝ^n` is a (closed) polyhedron if it is a finite intersection of
halfspaces `{x | a ⬝ x ≤ b}`. -/
def IsPolyhedron (n : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (a : Fin m → Fin n → ℝ) (b : Fin m → ℝ),
    S = ⋂ i, {x : Fin n → ℝ | (∑ j, a i j * x j) ≤ b i}

/-- `CPWL n`, the set of continuous piecewise-linear functions `ℝ^n → ℝ`: continuous
functions for which there is a finite polyhedral subdivision of `ℝ^n` (finitely many
polyhedral pieces covering `ℝ^n`) together with a finite list of affine functions, such
that `f` agrees with one of these affine functions on each piece. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
      ∃ (m : ℕ) (g : Fin m → ((Fin n → ℝ) → ℝ)) (P : Fin m → Set (Fin n → ℝ)),
        (∀ i, IsAffineFun n (g i)) ∧
        (∀ i, IsPolyhedron n (P i)) ∧
        (⋃ i, P i) = Set.univ ∧
        ∀ i, ∀ x ∈ P i, f x = g i x }

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so `n - 1 ≥ 2`,
using real subtraction of the cast of `n`). -/
def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n−1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent046

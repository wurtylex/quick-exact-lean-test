import Mathlib

namespace Agent021

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

"Better Neural Network Expressivity: Subdividing the Simplex"
(Bakaev, Brunck, Hertrich, Stade, Yehudayoff)

Theorem 2. For n ≥ 3, CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}.

## Modelling choices

* Vectors `ℝ^n` are encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^n → ℝ^m` is modelled concretely as a pair `(A, b)` with
  `A : Matrix (Fin m) (Fin n) ℝ` and `b : Fin m → ℝ`, acting by `x ↦ A.mulVec x + b`.
* A ReLU network with `k` hidden layers computing `f : ℝ^n → ℝ` is modelled by the
  inductive predicate `ComputesReLU n k f`, which unwinds exactly the alternating
  composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper: the base case
  `k = 0` is a single affine map to `ℝ^1`, and the inductive step prepends one affine map
  `ℝ^n → ℝ^m` followed by a componentwise ReLU to a network already computing a function
  of `k` hidden layers on `ℝ^m`.
* `ReLUn n k` is taken to be the functions representable with **at most** `k` hidden
  layers (not exactly `k`). This is the standard reading in the expressivity literature,
  and it is the reading under which `ReLUn n k ⊆ ReLUn n (k+1)` holds and Theorem 2 is a
  sensible equality (a network with more hidden layers can always simulate one with fewer,
  e.g. by inserting extra affine layers realizing the identity via `x = ReLU x - ReLU(-x)`
  composed appropriately; we do not prove this fact here, we only fix the convention).
* `CPWL n` is defined honestly: `f` is continuous, and there is a *finite* collection of
  polyhedra (each cut out as a finite intersection of affine half-spaces) covering `ℝ^n`,
  on each of which `f` agrees with some affine function. This is a genuine
  piecewise-linearity condition, independent of any notion of ReLU network.
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined via the real logarithm `Real.logb 3` and
  `Nat.ceil` (`⌈·⌉₊`), matching the statement verbatim.
-/

/-- The scalar ReLU function. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^n`. -/
def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^n → ℝ^m`, given concretely by a matrix and a bias vector. -/
structure AffineMap (n m : ℕ) where
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ

/-- The function `ℝ^n → ℝ^m` computed by an affine transformation. -/
def AffineMap.apply {n m : ℕ} (T : AffineMap n m) (x : Fin n → ℝ) : Fin m → ℝ :=
  T.A.mulVec x + T.b

/-- `ComputesReLU n k f` holds when `f : ℝ^n → ℝ` is computed by a ReLU network with
exactly `k` hidden layers, i.e. by the alternating composition of `k + 1` affine
transformations with componentwise ReLU applications in between, as in the paper:
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`.

* Base case (`k = 0`, depth 1, no hidden layers): a single affine map `ℝ^n → ℝ^1`.
* Step case: prepend an affine map `ℝ^n → ℝ^m` and a componentwise ReLU to a network
  already computing a function `g : ℝ^m → ℝ` with `k` hidden layers. -/
inductive ComputesReLU : ∀ (n k : ℕ), ((Fin n → ℝ) → ℝ) → Prop
  | base {n : ℕ} (T : AffineMap n 1) :
      ComputesReLU n 0 (fun x => T.apply x 0)
  | step {n m k : ℕ} (T : AffineMap n m) {g : (Fin m → ℝ) → ℝ} (hg : ComputesReLU m k g) :
      ComputesReLU n (k + 1) (fun x => g (reluVec (T.apply x)))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
**at most** `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, ComputesReLU n k' f }

/-- A subset of `ℝ^n` is a (closed) polyhedron if it is a finite intersection of affine
half-spaces `{x | ⟨c, x⟩ ≤ d}`. -/
def IsPolyhedron (n : ℕ) (P : Set (Fin n → ℝ)) : Prop :=
  ∃ (M : ℕ) (c : Fin M → Fin n → ℝ) (d : Fin M → ℝ),
    P = {x : Fin n → ℝ | ∀ l : Fin M, (∑ j, c l j * x j) ≤ d l}

/-- `CPWL n` is the space of continuous piecewise-linear functions `ℝ^n → ℝ`: those that
are continuous and admit a finite polyhedral subdivision of `ℝ^n` on each piece of which
the function agrees with some affine function. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (N : ℕ) (P : Fin N → Set (Fin n → ℝ)) (a : Fin N → (Fin n → ℝ)) (b : Fin N → ℝ),
          (∀ i, IsPolyhedron n (P i)) ∧
          (⋃ i, P i) = Set.univ ∧
          (∀ i, ∀ x ∈ P i, f x = (∑ j, a i j * x j) + b i) }

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from the theorem statement, for `n ≥ 3` (so that
`n - 1 ≥ 2 > 0` and the logarithm is well-behaved). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent021

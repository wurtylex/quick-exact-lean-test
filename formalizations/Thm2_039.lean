import Mathlib

namespace Agent039

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

  "Better Neural Network Expressivity: Subdividing the Simplex"

Theorem 2 states: for `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`.

## Modelling choices (see final summary)

* Vectors `ℝ^n` are modelled as `Fin n → ℝ`.
* Affine maps `ℝ^a → ℝ^b` are modelled concretely by a matrix and a bias vector.
* A ReLU network with `k` hidden layers computing `f : ℝ^n → ℝ` is defined by
  structural recursion on `k`, mirroring the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper.
* `ReLUn n k` is taken to be the set of functions representable with **at most**
  `k` hidden layers (rather than *exactly* `k`). This is the reading under which
  the theorem is true and matches the informal usage "representable with `k`
  hidden layers" in the paper (any network can be padded to use more layers via
  an identity-simulating pair of ReLUs, so "exactly k" and "at most k" describe
  the same increasing filtration of `CPWL_n`; "at most k" is the more natural
  and directly usable definition).
* `CPWL n` is defined genuinely: continuity, together with the existence of a
  *finite* family of affine functions such that every point has a neighborhood
  on which `f` coincides with one member of the family. This is a real
  piecewise-linearity condition, not a "representable by a ReLU network" or
  max-of-affine restatement of the theorem.
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined using the real logarithm
  `Real.logb 3` together with `Nat.ceil`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector. -/
def reluVec {m : ℕ} (v : Fin m → ℝ) : Fin m → ℝ := fun i => relu (v i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix `A` and a
bias vector `c`, computing `x ↦ A * x + c`. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an `AffineMap`. -/
def AffineMap.eval {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `NetProp n k f` holds iff `f : ℝ^n → ℝ` is computed by a ReLU network with
exactly `k` hidden layers, i.e. `f` is the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations
`T^(1), …, T^(k+1)` (with `T^(k+1)` landing in `ℝ^1`), interspersed with `k`
applications of componentwise ReLU. Defined by recursion on `k`: the base case
`k = 0` is a single affine transformation `ℝ^n → ℝ^1`; the inductive step peels
off the first affine map `T^(1) : ℝ^n → ℝ^m` together with a ReLU application,
reducing to a network with `k` hidden layers on the remaining `k + 1` affine
maps. -/
def NetProp (n : ℕ) : ℕ → ((Fin n → ℝ) → ℝ) → Prop
  | 0, f => ∃ w : AffineMap n 1, ∀ x, f x = w.eval x 0
  | (k + 1), f =>
      ∃ (m : ℕ) (T : AffineMap n m) (g : (Fin m → ℝ) → ℝ),
        NetProp m k g ∧ ∀ x, f x = g (reluVec (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU
network with **at most** `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ j ≤ k, NetProp n j f}

/-- `CPWL n` is the set of continuous, genuinely piecewise-linear functions
`ℝ^n → ℝ`: `f` is continuous, and there is a finite family of affine functions
(given by weight vectors `w i` and intercepts `b i`, indexed by a finite type
`ι`) such that every point `x` has a neighborhood on which `f` agrees with one
member `i` of the family. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → Fin n → ℝ) (b : ι → ℝ),
      ∀ x : Fin n → ℝ, ∃ i : ι, ∃ U : Set (Fin n → ℝ), IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, f y = (∑ j, w i j * y j) + b i}

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from the theorem statement, using the
real logarithm `Real.logb 3` and `Nat.ceil`. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent039

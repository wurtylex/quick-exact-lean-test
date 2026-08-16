import Mathlib

namespace Agent045

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):  for `n ≥ 3`, `CPWL n = ReLUn n (⌈log_3 (n-1)⌉ + 1)`.

Modelling choices:
* `ℝ^n` is encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is encoded concretely as a matrix `A` together
  with a bias vector `c`, via `x ↦ A * x + c`.
* A ReLU network with `k` hidden layers computing `f : ℝ^n → ℝ` is encoded by the
  recursive predicate `ComputesWithHidden`, which literally unwinds the alternating
  composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper: peel off the
  first affine map, apply ReLU componentwise, and recurse with one fewer hidden layer.
* `ReLUn n k` is taken to be the functions representable with *at most* `k` hidden
  layers (not exactly `k`). This is the standard convention in this literature (depth
  can always be padded, e.g. via `x = ReLU x - ReLU (-x)`, so the classes are monotone
  in `k`), and it is the reading under which the stated equality `CPWL n = ReLUn n (…)`
  is the correct/true statement of Theorem 2.
* `CPWL n` is defined directly as: `f` is continuous, and there is a *finite* family of
  affine functions such that `f` agrees with (at least) one member of the family in a
  neighbourhood of every point. This is a genuine local/piecewise-affine condition; it
  is not defined via ReLU-network representability and is not a global max-of-affine
  normal form.
* The depth bound `⌈log_3 (n-1)⌉ + 1` is encoded using the real logarithm
  `Real.logb 3` together with `Nat.ceil`, matching the paper's real-valued `log_3`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector in `ℝ^m` (encoded as `Fin m → ℝ`). -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix `A` and a bias
vector `c`, so that it computes `x ↦ A * x + c`. -/
structure AffineTransform (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- The function `ℝ^a → ℝ^b` computed by an affine transformation. -/
def AffineTransform.eval {a b : ℕ} (T : AffineTransform a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, T.A i j * x j) + T.c i

/-- `ComputesWithHidden k n f` means `f : ℝ^n → ℝ` is computed by a ReLU network with
exactly `k` hidden layers, i.e. by the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations
`T^(1), …, T^(k+1)`, with `ReLU` applied componentwise between consecutive affine maps.
The base case `k = 0` is a single affine transformation `ℝ^n → ℝ^1` (no hidden layers,
depth `1`), and the recursive case peels off the first affine map and the ReLU applied
to its output, then recurses on the remaining `k` hidden layers with the new input
dimension `m`. -/
def ComputesWithHidden : (k : ℕ) → (n : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | 0, n, f => ∃ T : AffineTransform n 1, ∀ x, f x = T.eval x 0
  | (k + 1), n, f =>
      ∃ (m : ℕ) (T : AffineTransform n m) (g : (Fin m → ℝ) → ℝ),
        ComputesWithHidden k m g ∧ ∀ x, f x = g (reluVec (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers. (Depth can always be padded without changing the
represented function, e.g. via the identity `x = ReLU x - ReLU (-x)`, so this "at most"
reading is the one under which the classes `ReLUn n k` increase with `k` and Theorem 2's
equality with `CPWL n` is the intended, true statement.) -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, ComputesWithHidden k' n f}

/-- An affine function `ℝ^n → ℝ`, i.e. `x ↦ ⟨a, x⟩ + b` for some vector `a` and scalar `b`. -/
def IsAffineFun (n : ℕ) (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x, g x = (∑ i, a i * x i) + b

/-- `CPWL n` is the set of continuous, piecewise linear functions `ℝ^n → ℝ`: those `f`
that are continuous, and are locally equal, near every point, to one member of some
fixed *finite* family of affine functions. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
        ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ),
          (∀ i, IsAffineFun n (g i)) ∧
          ∀ x : Fin n → ℝ, ∃ i : Fin m, Filter.Eventually (fun y => f y = g i y) (nhds x)}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, using the real logarithm to
base `3` and `Nat.ceil`. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3 (n-1)⌉ + 1}`. -/
theorem theorem2 : ∀ n : ℕ, n ≥ 3 → CPWL n = ReLUn n (depthBound n) := sorry

end Agent045

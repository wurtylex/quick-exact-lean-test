import Mathlib

namespace Agent098

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):

  For n ≥ 3,  CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}.

## Modelling choices

* `ℝ^n` is encoded as `Fin n → ℝ`.
* Affine transformations `ℝ^a → ℝ^b` are encoded concretely as a matrix `A` together with a
  bias vector `b`, via `x ↦ A.mulVec x + b`.
* A ReLU network with *exactly* `k` hidden layers computing `f : ℝ^n → ℝ` is defined by
  recursion on `k`: with `0` hidden layers it is a single affine map `ℝ^n → ℝ^1`; with
  `k+1` hidden layers it is an affine map `ℝ^n → ℝ^m` followed by componentwise ReLU,
  followed by a network with `k` hidden layers on the result.
* `ReLUn n k` is taken to be the functions representable with **at most** `k` hidden
  layers (not *exactly* `k`). This is the reading that makes Theorem 2 true as a genuine
  equality: representability classes are monotone in the number of hidden layers (a
  network with `j ≤ k` hidden layers can always be padded, e.g. by inserting an extra
  affine layer that is the identity in effect, to one with exactly `k` hidden layers
  representing the same function), so "exactly k" and "at most k" differ only by this
  padding step, and the paper's `ReLU_{n,k}` is understood as the standard "at most k"
  notion of network complexity classes.
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of closed
  polyhedral pieces covering `ℝ^n` (each cut out by finitely many affine inequalities)
  together with an affine function per piece, such that `f` agrees with the affine
  function on each piece. This is a genuine finite polyhedral subdivision condition, not
  a "representable by a ReLU network" or "max of affine functions" definition.
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded using the real logarithm `Real.logb 3`
  applied to `(n : ℝ) - 1` and `Nat.ceil`, matching the paper's real-valued ceiling of a
  real logarithm exactly (for `n ≥ 3`, `(n : ℝ) - 1 ≥ 2 > 0` so the logarithm is
  well-behaved).
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias vector. -/
structure AffineTransform (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  bias : Fin b → ℝ

/-- The function `ℝ^a → ℝ^b` computed by an affine transformation. -/
def AffineTransform.eval {a b : ℕ} (T : AffineTransform a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.bias

/-- A scalar-valued affine function `ℝ^n → ℝ`, `x ↦ ⟨a, x⟩ + b`. Used for describing the
affine pieces of a CPWL function. -/
structure AffineFn (n : ℕ) where
  a : Fin n → ℝ
  b : ℝ

/-- The function `ℝ^n → ℝ` computed by a scalar affine function. -/
def AffineFn.eval {n : ℕ} (f : AffineFn n) (x : Fin n → ℝ) : ℝ :=
  (∑ i, f.a i * x i) + f.b

/-- A subset of `ℝ^n` is a (closed) polyhedron if it is a finite intersection of closed
half-spaces `{x | ⟨a_i, x⟩ ≤ b_i}`. -/
def IsPolyhedron (n : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (A : Fin m → (Fin n → ℝ)) (b : Fin m → ℝ),
    S = {x | ∀ i, (∑ j, A i j * x j) ≤ b i}

/-- `f : ℝ^n → ℝ` is continuous piecewise linear: it is continuous, and there is a finite
family of closed polyhedral pieces covering `ℝ^n`, together with an affine function per
piece, such that `f` agrees with the corresponding affine function on each piece. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (S : Fin m → Set (Fin n → ℝ)) (g : Fin m → AffineFn n),
      (∀ i, IsPolyhedron n (S i)) ∧
      (Set.univ = ⋃ i, S i) ∧
      (∀ i, ∀ x ∈ S i, f x = (g i).eval x)}

/-- `ReLURepExact k n f` means `f : ℝ^n → ℝ` is computed by a ReLU network with *exactly*
`k` hidden layers, i.e. by the alternating composition
`T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}` of `k + 1` affine transformations with
componentwise ReLU applications in between, ending in an affine map to `ℝ^1` (whose single
output component is the value of `f`). Defined by recursion on `k`. -/
def ReLURepExact : ℕ → (n : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | 0, n, f =>
      ∃ T : AffineTransform n 1, ∀ x, f x = T.eval x 0
  | (k + 1), n, f =>
      ∃ (m : ℕ) (T : AffineTransform n m) (g : (Fin m → ℝ) → ℝ),
        ReLURepExact k m g ∧ ∀ x, f x = g (fun i => relu (T.eval x i))

/-- `ReLUn n k`, the set of functions `ℝ^n → ℝ` representable by a ReLU network with *at
most* `k` hidden layers (see the module docstring for why "at most" rather than
"exactly" is the right reading for Theorem 2). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ j ≤ k, ReLURepExact j n f}

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from Theorem 2, with the ceiling of the real
logarithm base 3 taken via `Nat.ceil` and `Real.logb`. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent098

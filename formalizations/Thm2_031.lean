import Mathlib

namespace Agent031

/-
Modelling choices (see summary at the end of the task too):

* Vectors `ℝ^n` are encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is encoded concretely as a matrix `A : Matrix
  (Fin b) (Fin a) ℝ` together with a bias vector, evaluated as `x ↦ A * x + bias`.
* A ReLU network with `k` *hidden layers* computing `f : ℝ^n → ℝ` is defined by
  structural recursion on `k`:
    - `k = 0`: the network is a single affine map `ℝ^n → ℝ` (a "depth 1" network,
      i.e. `T^(1)` alone, no ReLU is ever applied).
    - `k+1`: the first hidden layer applies an affine map `T : ℝ^n → ℝ^m` followed by
      componentwise ReLU, and the resulting vector in `ℝ^m` feeds a network with `k`
      hidden layers (i.e. the remaining affine maps `T^(2), ..., T^(k+2)`).
  This exactly matches the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper.
* `ReLUn n k` is taken to be the set of functions representable with *at most* `k`
  hidden layers (an increasing union over `k' ≤ k`), which is the standard convention
  and the one under which `ReLU_{n,k}` is monotone in `k` (extra hidden layers can
  always simulate fewer, e.g. via the identity `x = ReLU(x) - ReLU(-x)`), matching the
  intended reading of Theorem 2.
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of affine
  functions `ℝ^n → ℝ` such that every point of `ℝ^n` has a neighbourhood on which `f`
  agrees with (at least) one member of the family. This is a genuine local
  piecewise-linearity condition, not a "max of affine functions" formula and not
  "representable by some ReLU network".
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded using `Real.logb 3` and `Nat.ceil`
  (notation `⌈·⌉₊`).
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on vectors. -/
def reluVec {m : ℕ} (v : Fin m → ℝ) : Fin m → ℝ := fun i => relu (v i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias
vector. -/
structure AffineMap' (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  bias : Fin b → ℝ

/-- Evaluation of an affine transformation: `x ↦ A * x + bias`. -/
def AffineMap'.eval {a b : ℕ} (T : AffineMap' a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, T.A i j * x j) + T.bias i

/-- `IsReLUComputable n k f` means `f : ℝ^n → ℝ` is computed by a ReLU network with
exactly `k` hidden layers, i.e. by the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations
`T^(1), ..., T^(k+1)`, with componentwise ReLU applied after each of the first `k` of
them. Defined by recursion on `k`, peeling off the first hidden layer at each step. -/
def IsReLUComputable : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : AffineMap' n 1, ∀ x, f x = T.eval x 0
  | n, k + 1, f =>
      ∃ (m : ℕ) (T : AffineMap' n m) (g : (Fin m → ℝ) → ℝ),
        IsReLUComputable m k g ∧ ∀ x, f x = g (reluVec (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, IsReLUComputable n k' f}

/-- `CPWL n` is the set of continuous, piecewise linear functions `ℝ^n → ℝ`: those that
are continuous and locally agree, near every point, with one of finitely many affine
functions. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (T : Fin m → AffineMap' n 1),
      ∀ x : Fin n → ℝ, ∃ i : Fin m, ∃ ε : ℝ, ε > 0 ∧
        ∀ y : Fin n → ℝ, dist y x < ε → f y = (T i).eval y 0}

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from the theorem statement. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) : CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent031

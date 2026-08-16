import Mathlib

namespace Agent022

/-!
Formalization of Theorem 2 of arXiv:2505.14338
("Better Neural Network Expressivity: Subdividing the Simplex").

Modelling choices:
* `ℝ^n` is encoded as `Fin n → ℝ`.
* An affine map `ℝ^a → ℝ^b` is encoded concretely as a matrix `A` together with a bias
  vector `c`, applied as `x ↦ A.mulVec x + c`.
* A ReLU network with *exactly* `k` hidden layers computing `f : ℝ^n → ℝ` is defined
  recursively: `k = 0` means `f` itself is affine (a single affine transform, the
  "depth 1 / 0 hidden layers" base case); `k+1` means `f` is obtained by first applying
  an affine transform `T : ℝ^n → ℝ^m`, then componentwise ReLU, then a function `g`
  computable with `k` hidden layers, i.e. `f = g ∘ reluVec ∘ T.apply`.
* `ReLUn n k` is taken to be functions representable with **at most** `k` hidden layers
  (the union over `j ≤ k` of "exactly `j`"), which is the standard reading in this
  literature: extra hidden layers can always simulate fewer, so `ReLU_{n,k}` naturally
  forms an increasing chain in `k`, and this is the reading under which Theorem 2 (an
  equality with a *specific* depth) is meaningful and true.
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family (indexed by
  `Fin m`) of affine functions (weight vector + bias) such that every point has a
  neighborhood on which `f` coincides with one of these affine functions. This is a
  genuine local piecewise-affinity condition (not a max/min-of-affine normal form, and
  not "representable by some ReLU network").
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded with `Real.logb 3` and `Nat.ceil`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias
vector. -/
structure AffineMap' (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def AffineMap'.apply {a b : ℕ} (T : AffineMap' a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `f : ℝ^n → ℝ` is computed by a ReLU network with **exactly** `k` hidden layers:
`k = 0` is a single affine transform (`T^(1)`, depth 1, 0 hidden layers); the step case
prepends an affine transform followed by a componentwise ReLU to a network with `k`
hidden layers computing the rest. -/
def ExactReLUComputable : ℕ → (n : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | 0, n, f => ∃ w : Fin n → ℝ, ∃ b : ℝ, ∀ x, f x = (∑ j, w j * x j) + b
  | (k + 1), n, f =>
      ∃ (m : ℕ) (T : AffineMap' n m) (g : (Fin m → ℝ) → ℝ),
        ExactReLUComputable k m g ∧ f = g ∘ reluVec ∘ T.apply

/-- `ReLUn n k`: functions `ℝ^n → ℝ` representable by a ReLU network with **at most**
`k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ j ≤ k, ExactReLUComputable j n f }

/-- `CPWL n`: continuous functions `ℝ^n → ℝ` that are, near every point, equal to one of
finitely many affine functions (a genuine local piecewise-linearity condition). -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
      ∃ (m : ℕ) (w : Fin m → Fin n → ℝ) (b : Fin m → ℝ),
        ∀ x : Fin n → ℝ, ∃ i : Fin m, ∃ U ∈ nhds x, ∀ y ∈ U, f y = (∑ j, w i j * y j) + b i }

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from the theorem statement. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent022

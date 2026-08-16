import Mathlib

namespace Agent053

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

"Better Neural Network Expressivity: Subdividing the Simplex"
(Bakaev, Brunck, Hertrich, Stade, Yehudayoff).

Theorem 2. For n ≥ 3, we have CPWL_n = ReLU_{n, ⌈log_3 (n-1)⌉ + 1}.

We encode ℝ^n as `Fin n → ℝ`.
-/

/-- The ReLU activation function on ℝ. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise (vector) ReLU on ℝ^m. -/
def reluVec {m : ℕ} (v : Fin m → ℝ) : Fin m → ℝ := fun i => relu (v i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix `A` and a bias
vector `c`, computing `x ↦ A * x + c`. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- The function `ℝ^a → ℝ^b` computed by an affine transformation. -/
def AffineMap.apply {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `computesReLUExact k n f` means `f : ℝ^n → ℝ` is computed by a ReLU network with
*exactly* `k` hidden layers, i.e. by an alternating composition

    T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)

of `k + 1` affine transformations `T^(1), …, T^(k+1)` with componentwise ReLU applied
after each of the first `k` of them. The hidden layer widths `n_1, …, n_k` are existentially
quantified (chosen by the network), while the input width is `n` and the output width is `1`
(functions here are real-valued). The definition proceeds by recursion on the number of
hidden layers: with `0` hidden layers a network is a single affine map `ℝ^n → ℝ`; with
`k + 1` hidden layers, a network first applies an affine map `T : ℝ^n → ℝ^m` followed by
componentwise ReLU, then feeds the result into a network with `k` hidden layers. -/
def computesReLUExact : (k : ℕ) → (n : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | 0, n, f => ∃ T : AffineMap n 1, ∀ x, f x = T.apply x 0
  | (k + 1), n, f =>
      ∃ (m : ℕ) (T : AffineMap n m) (g : (Fin m → ℝ) → ℝ),
        computesReLUExact k m g ∧ ∀ x, f x = g (reluVec (T.apply x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers. (This is the standard reading of `ReLU_{n,k}` in the depth-
separation literature: since the identity on ℝ can itself be computed with one hidden ReLU
layer via `x = ReLU(x) - ReLU(-x)`, a network with `j` hidden layers can always be padded
into one with any `k ≥ j` hidden layers computing the same function, so "exactly k" and
"at most k" give the same monotone family of classes, and "at most k" is the version for
which statements like Theorem 1 and Theorem 2 — asserting that *smaller* depths suffice —
are meaningful.) -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ j ≤ k, computesReLUExact j n f}

/-- An affine function `ℝ^n → ℝ`, i.e. `x ↦ ⟨w, x⟩ + b` for some weight vector `w` and
bias `b`. -/
def IsAffineFun (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (w : Fin n → ℝ) (b : ℝ), ∀ x, f x = (∑ i, w i * x i) + b

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: those `f` that
are continuous and admit a finite family of affine "pieces" such that every point of `ℝ^n`
has a neighborhood on which `f` coincides with one of these pieces. This is a genuine
polyhedral-subdivision-flavored definition of CPWL (local agreement with finitely many
affine functions), not a "representable by a ReLU network" or "max of affine functions"
definition. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
        ∃ (N : ℕ) (pieces : Fin N → (Fin n → ℝ) → ℝ),
          (∀ i, IsAffineFun n (pieces i)) ∧
          ∀ x : Fin n → ℝ, ∃ i : Fin N, ∃ ε > 0, ∀ y, dist y x < ε → f y = pieces i y}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so that `n - 1 ≥ 2`
and the logarithm is well-defined and positive). We use the real logarithm `Real.logb 3`
together with `Nat.ceil`. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3 (n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent053

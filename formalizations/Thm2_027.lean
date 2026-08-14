import Mathlib

namespace Agent027

/-
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"): for n ≥ 3, CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}.

Modelling choices (see summary at the end of this file / reported to the caller):
  * Vectors ℝ^m are encoded as `Fin m → ℝ`.
  * `ReLUn n k` is the set of functions computable by a ReLU network with input
    dimension `n` and *exactly* `k` hidden layers (i.e. `k + 1` affine transformations
    with a componentwise ReLU applied after each of the first `k` of them). This is
    the literal reading of the paper's notation `ReLU_{n,k}`, and it is consistent with
    Theorem 2's claim of *equality* of sets: since one can always simulate a shallower
    network with a deeper one (e.g. by padding with an extra affine map/ReLU pair that
    acts as the identity on the relevant range), `ReLU_{n,k}` is monotone increasing in
    `k`, so at the specific depth `⌈log_3(n-1)⌉ + 1` singled out by the theorem, "exactly
    k" and "at most k" describe the same set — namely all of CPWL_n.
  * `CPWL n` is defined as: continuous functions `ℝ^n → ℝ` that are *locally* equal to
    one of finitely many affine functions (a genuine piecewise-linearity condition, not
    a ReLU-representability condition and not a max-of-affine normal form).
  * The depth bound uses the real logarithm `Real.logb 3` together with `Nat.ceil`.
-/

/-- The ReLU activation function on ℝ. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of ReLU to a vector in `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias
vector: `x ↦ A * x + bias`. -/
structure AffineMap (a b : ℕ) where
  A    : Matrix (Fin b) (Fin a) ℝ
  bias : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def AffineMap.apply {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A *ᵥ x + T.bias

/-- `ComputesWithLayers k n f` means: `f : ℝ^n → ℝ` is computed by a ReLU network with
input dimension `n` and exactly `k` hidden layers, i.e. by an alternating composition

    T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)

of `k + 1` affine transformations `T^(1), …, T^(k+1)` (with componentwise ReLU applied
after each of the first `k` of them), for *some* choice of the intermediate layer widths
`n_1, …, n_k`.

Defined by recursion on `k`: the base case `k = 0` is a single affine map `ℝ^n → ℝ`
(zero hidden layers, i.e. `1 = k+1` affine transformation and no ReLUs); the successor
case peels off the first affine map `T^(1) : ℝ^n → ℝ^m` together with its ReLU, and
recursively requires the remaining function `g : ℝ^m → ℝ` to be computed by a network
with `k` hidden layers (i.e. by `T^(k+1) ∘ ReLU ∘ ⋯ ∘ ReLU ∘ T^(2)`). -/
def ComputesWithLayers : ℕ → (n : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | 0,     n, f => ∃ T : AffineMap n 1, ∀ x, f x = T.apply x 0
  | k + 1, n, f =>
      ∃ (m : ℕ) (T : AffineMap n m) (g : (Fin m → ℝ) → ℝ),
        ComputesWithLayers k m g ∧ ∀ x, f x = g (reluVec (T.apply x))

/-- `ReLUn n k`: the set of functions `ℝ^n → ℝ` representable by a ReLU network with
input dimension `n` and exactly `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ComputesWithLayers k n f}

/-- An affine function `ℝ^n → ℝ`: `x ↦ a ⬝ x + c` for some linear functional `a` and
constant `c`. -/
def IsAffine (n : ℕ) (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (c : ℝ), ∀ x, g x = (∑ i, a i * x i) + c

/-- `CPWL n`: the space of continuous, piecewise linear functions `ℝ^n → ℝ`. A function
`f` is CPWL if it is continuous and there is a finite family of affine functions such
that every point of `ℝ^n` has a neighbourhood on which `f` coincides with one of them
(a genuine finite polyhedral-type piecewise-linearity condition). -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
        ∃ S : Finset ((Fin n → ℝ) → ℝ), (∀ g ∈ S, IsAffine n g) ∧
          ∀ x : Fin n → ℝ, ∃ g ∈ S, ∀ᶠ y in nhds x, f y = g y}

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from Theorem 2, using the real logarithm and
`Nat.ceil`. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent027

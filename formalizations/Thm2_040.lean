import Mathlib

namespace Agent040

open scoped BigOperators

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m` (encoded as `Fin m → ℝ`). -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias
vector: `x ↦ A * x + c`. -/
structure Affine (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- The function `ℝ^a → ℝ^b` computed by an affine transformation. -/
def Affine.eval {a b : ℕ} (T : Affine a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, T.A i j * x j) + T.c i

/-- `NetworkComputes k n f` holds iff `f : ℝ^n → ℝ` is computed by a ReLU network with
exactly `k` hidden layers, i.e. by the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations, with
componentwise ReLU applied after each of the first `k` of them (matching the definition
in the paper's Introduction).

The recursion peels off the first affine map `T^(1) : ℝ^n → ℝ^m` (where `m` is the
width `n_1` of the first hidden layer) together with the ReLU applied to its output,
leaving a network with `k` hidden layers and input dimension `m` computing the rest.
The base case `k = 0` is a single affine map `ℝ^n → ℝ` (no hidden layers, no ReLU). -/
def NetworkComputes : ℕ → (n : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | 0, n, f => ∃ T : Affine n 1, ∀ x, f x = T.eval x 0
  | k + 1, n, f =>
      ∃ (m : ℕ) (T : Affine n m) (g : (Fin m → ℝ) → ℝ),
        NetworkComputes k m g ∧ ∀ x, f x = g (reluVec (T.eval x))

/-- `ReLUn n k`: the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*exactly* `k` hidden layers (the literal reading of "the subset of `CPWL_n`
representable with `k` hidden layers" from the paper). Note that an extra hidden layer
can always simulate the identity on each coordinate, since
`x = ReLU x - ReLU (-x)`; consequently `NetworkComputes k n f` implies
`NetworkComputes (k+1) n f`, so this "exactly `k`" reading is monotone in `k` and
coincides with an "at most `k`" reading — either is consistent with Theorem 2 as an
equality of sets for the specific bound below. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | NetworkComputes k n f }

/-- `CPWL n`: the continuous, piecewise-linear functions `ℝ^n → ℝ`. A function is CPWL
if it is continuous and there is a *finite* family `S` of affine functions such that
every point of `ℝ^n` has a neighborhood on which `f` agrees with (at least) one member
of `S`. This is a genuine piecewise-linearity condition: it is not automatically
satisfied by every continuous function, and it does not presuppose representability by
a ReLU network or a max-of-affine normal form. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
      ∃ S : Finset (Affine n 1), ∀ x : Fin n → ℝ,
        ∃ T ∈ S, ∀ᶠ y in nhds x, f y = T.eval y 0 }

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so `n - 1 ≥ 2`
and the real logarithm base `3` is well-defined and positive on it). -/
def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 : ∀ n : ℕ, n ≥ 3 → CPWL n = ReLUn n (depthBound n) := sorry

end Agent040

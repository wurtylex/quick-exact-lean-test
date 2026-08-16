import Mathlib

namespace Agent089

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

"Better Neural Network Expressivity: Subdividing the Simplex"
(Bakaev, Brunck, Hertrich, Stade, Yehudayoff).

Theorem 2. For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`.

We encode `ℝ^n` as `Fin n → ℝ`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of ReLU to a vector in `Fin n → ℝ`. -/
def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias
vector: `x ↦ A * x + b`. -/
def AffineFun (a b : ℕ) := Matrix (Fin b) (Fin a) ℝ × (Fin b → ℝ)

/-- Evaluation of an affine transformation. -/
def AffineFun.eval {a b : ℕ} (T : AffineFun a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.1.mulVec x + T.2

/-- `NNComputesExact n k f` means `f : ℝ^n → ℝ` is computed by a ReLU network with
*exactly* `k` hidden layers, i.e. `f` arises as the alternating composition

    T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)

of `k + 1` affine transformations `T^(1), …, T^(k+1)` with matching intermediate
dimensions `n = n_0, n_1, …, n_k, n_{k+1} = 1`.

The recursion peels off the first affine map `T^(1) : ℝ^n → ℝ^m` together with the
subsequent ReLU, and recurses on the remaining network (with `k` hidden layers,
computing `ℝ^m → ℝ`) that produces the final affine map `T^(k+1)` in its base case. -/
def NNComputesExact : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : AffineFun n 1, ∀ x, f x = T.eval x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : AffineFun n m) (g : (Fin m → ℝ) → ℝ),
        NNComputesExact m k g ∧ ∀ x, f x = g (reluVec (T.eval x))

/-- `ReLUn n k`, the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers. We take the "at most" reading (rather than "exactly `k`")
because a network with `j ≤ k` hidden layers can always be padded to have `k` hidden
layers (e.g. by adding trivial extra affine/ReLU layers), so `ReLU_{n,k}` is naturally
increasing in `k`; this is also the reading under which Theorem 2's equality
`CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉+1}` is the correct statement (it must in particular
contain low-complexity functions such as affine functions, which need only `0` hidden
layers). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ j : ℕ, j ≤ k ∧ NNComputesExact n j f}

/-- An affine (degree-`≤ 1` polynomial) function `ℝ^n → ℝ`. -/
def IsAffine (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x, f x = (∑ i, a i * x i) + b

/-- `CPWL n`, the space of continuous piecewise-linear functions `ℝ^n → ℝ`: those `f`
that are continuous and are, locally around every point, equal to one of finitely many
globally-fixed affine functions. This is a genuine piecewise-affine condition (a finite
polyhedral-type subdivision into pieces on which `f` is affine), independent of any
notion of ReLU network. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
       ∃ S : Finset ((Fin n → ℝ) → ℝ),
         (∀ ℓ ∈ S, IsAffine n ℓ) ∧
         ∀ x : Fin n → ℝ, ∃ ℓ ∈ S, ∃ U ∈ nhds x, ∀ y ∈ U, f y = ℓ y}

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from Theorem 2, encoded using the real
logarithm `Real.logb 3` and `Nat.ceil`. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent089

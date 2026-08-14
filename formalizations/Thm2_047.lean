import Mathlib

namespace Agent047

/-! ### Basic building blocks: ReLU, affine maps -/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b` given concretely by a matrix `A` and a bias
vector `c`, applied as `x ↦ A * x + c`. -/
def affineApply {a b : ℕ} (A : Matrix (Fin b) (Fin a) ℝ) (c : Fin b → ℝ)
    (x : Fin a → ℝ) : Fin b → ℝ :=
  A.mulVec x + c

/-! ### ReLU networks -/

/-- `NetComputes n m k f` says that `f : ℝ^n → ℝ^m` is computed by a ReLU network with
`k` hidden layers, i.e. by an alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ... ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations
`T^(1), ..., T^(k+1)` with componentwise ReLU applied after each of the first `k` of them.
We build this up recursively from the *output* side: a `0`-hidden-layer network is a
single affine map (depth `1`), and a `(k+1)`-hidden-layer network is a `k`-hidden-layer
network `g : ℝ^n → ℝ^p` followed by a ReLU and one more affine map `ℝ^p → ℝ^m`. -/
def NetComputes : (n m k : ℕ) → ((Fin n → ℝ) → (Fin m → ℝ)) → Prop
  | n, m, 0, f =>
      ∃ (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ), ∀ x, f x = affineApply A c x
  | n, m, (k + 1), f =>
      ∃ (p : ℕ) (g : (Fin n → ℝ) → (Fin p → ℝ)) (A : Matrix (Fin m) (Fin p) ℝ)
        (c : Fin m → ℝ),
        NetComputes n p k g ∧ ∀ x, f x = affineApply A c (reluVec (g x))

/-- A scalar function `f : ℝ^n → ℝ` is computed by a ReLU network with `k` hidden layers
if it is (identifying `ℝ` with `ℝ^1`) the output of a `NetComputes` network
`ℝ^n → ℝ^1`. -/
def ReluComputable (n k : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  NetComputes n 1 k (fun x (_ : Fin 1) => f x)

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers. We use "at most" rather than "exactly": a network can always
be padded with extra layers that compute the identity via ReLU (`x = ReLU x - ReLU (-x)`),
so the classes of functions representable with `k` and with `k + 1` hidden layers are
naturally increasing in `k`. Reading `ReLU_{n,k}` as "at most `k` hidden layers" is what
makes the single equality `CPWL_n = ReLU_{n,k}` (for one specific `k`) the right statement
of Theorem 2, without silently relying on a separate monotonicity/padding lemma. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, ReluComputable n k' f }

/-! ### CPWL functions -/

/-- An affine function `ℝ^n → ℝ`, given by a linear part `a` and a constant `b`. -/
def IsAffineFun (n : ℕ) (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x : Fin n → ℝ, g x = (Finset.univ.sum fun i => a i * x i) + b

/-- The space of continuous, piecewise-linear functions `ℝ^n → ℝ`: continuous functions
that, at every point of `ℝ^n`, locally agree with one of finitely many affine functions.
This is a genuine piecewise-linearity condition (not "representable by some ReLU
network" and not a max-of-affine normal form), matching the informal definition of CPWL
in the paper. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ), (∀ i, IsAffineFun n (g i)) ∧
          ∀ x : Fin n → ℝ, ∃ i, ∀ᶠ y in nhds x, f y = g i y }

/-! ### The depth bound `⌈log_3 (n - 1)⌉ + 1` -/

/-- The number of hidden layers `⌈log_3 (n - 1)⌉ + 1` from the statement of Theorem 2,
using the real logarithm `Real.logb 3` and `Nat.ceil`. For `n ≥ 3` we have `n - 1 ≥ 2`,
so the argument of the logarithm is positive. -/
def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-! ### Theorem 2 -/

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉+1}`: the continuous
piecewise-linear functions on `ℝ^n` are exactly those representable by a ReLU network
with at most `⌈log_3(n-1)⌉ + 1` hidden layers. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent047

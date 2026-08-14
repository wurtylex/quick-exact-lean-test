import Mathlib

namespace Agent023

/-! ## ReLU activation -/

/-- The ReLU activation function on `ℝ`. -/
noncomputable def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU applied to a vector in `ℝ^m`, encoded as `Fin m → ℝ`. -/
noncomputable def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-! ## Affine transformations -/

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix `A` and a bias
    vector `c`, computing `x ↦ A * x + c`. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
noncomputable def AffineMap.eval {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- A function `ℝ^n → ℝ` is affine (scalar-valued affine transformation). -/
def IsAffineFun {n : ℕ} (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), g = fun x => (∑ i, a i * x i) + b

/-! ## Functions computed by a ReLU network -/

/-- `IsReLUNetworkFunc k n f` says that `f : ℝ^n → ℝ` is *computed* by a ReLU network
    with exactly `k` hidden layers, i.e. by the alternating composition
    `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`
    of `k + 1` affine transformations `T^(1), …, T^(k+1)`, with componentwise ReLU applied
    between consecutive affine transformations (and no ReLU after the last one, since the
    output is a single real number).

    We define this by recursion on `k`:
    * with `0` hidden layers, the network is just a single affine transformation
      `T^(1) : ℝ^n → ℝ` (a depth-1 network with no hidden layers);
    * with `k + 1` hidden layers, we first apply an affine transformation
      `T^(1) : ℝ^n → ℝ^m` to the input, then ReLU componentwise, and the remaining
      `k` hidden layers (given by `T^(2), …, T^(k+1)`) act on the `m`-dimensional result. -/
def IsReLUNetworkFunc : (k n : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | 0, _n, f => IsAffineFun f
  | (k + 1), n, f =>
      ∃ (m : ℕ) (T : AffineMap n m) (g : (Fin m → ℝ) → ℝ),
        IsReLUNetworkFunc k m g ∧ f = fun x => g (reluVec (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
    *at most* `k` hidden layers.

    Modelling choice: we read `ReLU_{n,k}` as "at most `k` hidden layers" rather than
    "exactly `k` hidden layers". This is the reading under which `ReLUn n k` is monotone
    in `k` (`ReLUn n k ⊆ ReLUn n (k+1)`, since one can always spend extra hidden layers
    without being forced to use them), which is the natural reading needed for
    `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉+1}` to assert that every CPWL function needs *at most*
    that many hidden layers (the content of Theorem 2), rather than the much stronger and
    false-looking claim that every CPWL function needs *exactly* that many. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, IsReLUNetworkFunc k' n f}

/-! ## Continuous piecewise-linear functions -/

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: those that
    are continuous, and for which there is a finite family of affine functions such that
    every point of `ℝ^n` has an open neighbourhood on which `f` agrees with one of them.
    This is a genuine local piecewise-affine condition, not a "max of affine functions"
    normal form and not a "representable by some ReLU network" reformulation. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
       ∃ (m : ℕ) (g : Fin m → ((Fin n → ℝ) → ℝ)),
         (∀ j, IsAffineFun (g j)) ∧
         ∀ x : Fin n → ℝ, ∃ j : Fin m, ∃ U : Set (Fin n → ℝ),
           IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, f y = g j y}

/-! ## The depth bound of Theorem 2 -/

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so `n - 1 ≥ 2 > 0`
    and the real logarithm `Real.logb 3 (n - 1)` is well-behaved). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-! ## Theorem 2 -/

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉+1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent023

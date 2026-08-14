import Mathlib

namespace Agent017

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

"Better Neural Network Expressivity: Subdividing the Simplex"

Theorem 2. For n ≥ 3, we have CPWL_n = ReLU_{n, ⌈log_3(n−1)⌉ + 1}.

## Modelling choices

* Vectors ℝ^m are modelled as `Fin m → ℝ`.
* An affine transformation ℝ^a → ℝ^b is modelled concretely by the structure `Aff a b`,
  carrying a matrix `A : Matrix (Fin b) (Fin a) ℝ` and a bias vector `c : Fin b → ℝ`,
  evaluated as `x ↦ A *ᵥ x + c`.
* `relu : ℝ → ℝ` is `fun x => max 0 x`, and `reluV` is its componentwise application
  to vectors.
* "`f` is computed by a ReLU network with exactly `k` hidden layers" is captured by the
  recursive predicate `ComputesWithLayers n k f`: with `0` hidden layers `f` itself must
  be (the scalar output of) a single affine map `ℝ^n → ℝ`; with `k+1` hidden layers, `f`
  factors as `g ∘ reluV ∘ T` where `T : ℝ^n → ℝ^m` is affine and `g` is computable with
  `k` hidden layers from `ℝ^m`.
* `ReLUn n k` is read as **"at most k hidden layers"** (not exactly k): this is the
  standard convention in the expressivity literature, and it is the reading under which
  the stated equality can be true, since `ReLUn n k` is then monotone increasing in `k`
  and the theorem says it *saturates* to all of `CPWL n` once `k` reaches the stated
  bound. Under the "exactly k" reading, `ReLUn n k` need not even be a subset of
  `ReLUn n (k+1)` (padding a network with extra layers is not automatic), so the
  displayed equality of sets would generally fail.
* `CPWL n` is defined mathematically (not via ReLU networks, and not as a max-of-affine
  normal form) as: `f` is continuous, and there is a *finite* family of affine functions
  `Fin N → Aff n 1` such that every point `x` has a neighbourhood on which `f` agrees
  with (at least) one member of the family. This is the "finite family of affine
  functions that `f` locally agrees with" formulation suggested by the task spec.
* The depth bound `⌈log_3(n−1)⌉ + 1` is defined via the genuine real logarithm
  `Real.logb 3` composed with `Nat.ceil`, applied to the natural number `n - 1`
  (well-defined since the theorem only concerns `n ≥ 3`, so `n - 1 ≥ 2`).
-/

/-- `relu : ℝ → ℝ`, the scalar ReLU activation. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector `ℝ^m`. -/
def reluV {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias
vector, i.e. `x ↦ A *ᵥ x + c`. -/
structure Aff (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def Aff.eval {a b : ℕ} (T : Aff a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `ComputesWithLayers n k f` : the function `f : ℝ^n → ℝ` is computed by a ReLU
network with exactly `k` hidden layers, in the sense of the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of affine transformations `T^(i)`. -/
def ComputesWithLayers : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : Aff n 1, ∀ x, f x = (T.eval x) 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : Aff n m) (g : (Fin m → ℝ) → ℝ),
        ComputesWithLayers m k g ∧ ∀ x, f x = g (reluV (T.eval x))

/-- `ReLUn n k`, the set of functions `ℝ^n → ℝ` representable with **at most** `k`
hidden layers (see the modelling notes above for why "at most" rather than "exactly"
is the reading that makes the theorem true). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, ComputesWithLayers n k' f}

/-- `CPWL n`, the set of continuous piecewise-linear functions `ℝ^n → ℝ`: continuous
functions that, near every point, agree with one member of some fixed finite family of
affine functions. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
      ∃ (N : ℕ) (g : Fin N → Aff n 1),
        ∀ x : Fin n → ℝ, ∃ (U : Set (Fin n → ℝ)) (i : Fin N),
          U ∈ nhds x ∧ ∀ y ∈ U, f y = (g i).eval y 0}

/-- The depth bound `⌈log_3(n − 1)⌉ + 1` from the statement of Theorem 2. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n - 1 : ℕ) : ℝ)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL n = ReLUn n (⌈log_3(n−1)⌉ + 1)`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent017

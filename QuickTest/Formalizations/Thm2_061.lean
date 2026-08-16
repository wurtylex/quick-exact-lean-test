import Mathlib

namespace Agent061

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):  For `n ≥ 3`, `CPWL n = ReLUn n (⌈log_3 (n-1)⌉ + 1)`.

Modelling choices:
* `ℝ^m` is encoded as `Fin m → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is a function of the form `x ↦ A.mulVec x + c`
  for a matrix `A` and a vector `c` (`IsAffineMap`); the special case of a scalar-valued
  affine map `ℝ^a → ℝ` is `IsAffineFn`.
* `relu` is `max 0 ·` on `ℝ`, applied componentwise as `reluVec`.
* `NetComputes k n f` says `f : ℝ^n → ℝ` is computed by *some* ReLU network with
  exactly `k` hidden layers, via the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` described in the paper. It is defined by
  recursion on `k`: with `0` hidden layers the network is a single affine map; with
  `k+1` hidden layers, the input first passes through an affine map into some
  intermediate dimension `m`, then ReLU, and the rest is computed by a network with `k`
  hidden layers on `ℝ^m`.
* `ReLUn n k` is taken to be functions representable with **at most** `k` hidden layers
  (not exactly `k`): since one can always pad a network with extra affine/ReLU layers
  that act as the identity, the "at most" and "exactly, for k large enough" classes
  coincide in spirit, but "at most" is the reading under which `ReLUn n k` forms an
  increasing chain in `k` and Theorem 2 (which asserts these classes eventually cover
  all of `CPWL n`) is the natural, true statement.
* `CPWL n` is defined as continuous functions that are *locally* equal to a member of
  some finite family of affine functions, near every point — a genuine finite
  polyhedral / piecewise-affine condition, not a "max of affine pieces" normal form and
  not "representable by a ReLU network".
* The depth bound `⌈log_3 (n-1)⌉ + 1` is encoded via the real logarithm `Real.logb 3`
  and `Nat.ceil`.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- `f : ℝ^a → ℝ^b` is an affine transformation: `f x = A * x + c` for some matrix `A`
and vector `c`. -/
def IsAffineMap {a b : ℕ} (f : (Fin a → ℝ) → (Fin b → ℝ)) : Prop :=
  ∃ (A : Matrix (Fin b) (Fin a) ℝ) (c : Fin b → ℝ), ∀ x, f x = A.mulVec x + c

/-- A scalar-valued affine function `ℝ^n → ℝ`. -/
def IsAffineFn {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x : Fin n → ℝ, f x = (∑ i, a i * x i) + b

/-- `NetComputes k n f` : `f : ℝ^n → ℝ` is computed by a ReLU network with exactly
`k` hidden layers, i.e. by the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations. -/
def NetComputes : ℕ → (n : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | 0, _n, f => IsAffineFn f
  | k + 1, n, f =>
      ∃ (m : ℕ) (T : (Fin n → ℝ) → (Fin m → ℝ)) (g : (Fin m → ℝ) → ℝ),
        IsAffineMap T ∧ NetComputes k m g ∧ ∀ x, f x = g (reluVec (T x))

/-- The set of functions `ℝ^n → ℝ` representable by a ReLU network with **at most**
`k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, NetComputes k' n f}

/-- `f : ℝ^n → ℝ` is continuous piecewise linear: it is continuous, and there is a
finite family of affine functions such that near every point `f` agrees with one of
them. -/
def IsCPWL {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  Continuous f ∧
    ∃ S : Finset ((Fin n → ℝ) → ℝ),
      (∀ h ∈ S, IsAffineFn h) ∧
        ∀ x : Fin n → ℝ, ∃ h ∈ S, ∀ᶠ y in nhds x, f y = h y

/-- The space of continuous piecewise linear functions `ℝ^n → ℝ`. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) := {f | IsCPWL f}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from the theorem, for `n ≥ 3` (so `n - 1 ≥ 2`
as a real number). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3 (n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent061

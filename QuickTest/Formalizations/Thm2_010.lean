import Mathlib

namespace Agent010

/-!
# Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity: Subdividing the Simplex")

We formalize `CPWL_n = ReLU_{n, ⌈log₃(n-1)⌉ + 1}` for `n ≥ 3`.

## Modelling choices

* `ℝ^n` is encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is encoded concretely as a pair `(A, c)` with
  `A : Matrix (Fin b) (Fin a) ℝ` and `c : Fin b → ℝ`, acting as `x ↦ A.mulVec x + c`.
* A ReLU network with exactly `k` hidden layers computing `f : ℝ^n → ℝ` is defined by
  recursion on `k`, mirroring the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper: the base case `k = 0` is a
  single affine map `ℝ^n → ℝ` (depth 1, no hidden layers), and the successor case peels off
  the first affine map `T^(1) : ℝ^n → ℝ^m` together with the following `ReLU`, leaving a
  network with `k` hidden layers computing the "tail" function `g : ℝ^m → ℝ`.
* `ReLUn n k` is taken to mean *at most* `k` hidden layers (`∃ k' ≤ k, ...`), not *exactly*
  `k`. This is the reading under which Theorem 2 (an equality with one specific `k`) can be
  true: the classes for exactly `k` hidden layers are not literally nested (a network with
  exactly `k` hidden layers cannot in general also be written with exactly `k+1`, unless one
  allows padding by identity layers), so the paper's `ReLU_{n,k}` is implicitly the
  "at most" / cumulative class, monotone in `k`, which is what makes an equality `CPWL_n =
  ReLU_{n,k}` for a single threshold `k` a meaningful and provable statement.
* `CPWL n` is defined mathematically (not via ReLU networks, and not as a max-of-affine
  normal form) as: `f` is continuous, and there is a *finite* family of affine functions
  `φ : Fin m → (ℝ^n → ℝ)` such that every point `x` has a neighborhood on which `f` agrees
  with (i.e. equals) some `φ i`. This is the standard "finite family of affine pieces,
  locally agreeing with `f`" formulation of continuous piecewise-linearity.
* The depth bound `⌈log₃(n-1)⌉ + 1` is defined using `Real.logb 3` and `Nat.ceil` (`⌈·⌉₊`)
  applied to the real number `(n : ℝ) - 1`, matching the paper's real-valued `log_3` and
  ceiling exactly.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a translation
vector, acting as `x ↦ A * x + c`. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an `AffineMap`. -/
def AffineMap.eval {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `NetComputes n k f` means `f : ℝ^n → ℝ` is computed by a ReLU network with exactly `k`
hidden layers, i.e. by an alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations with
componentwise ReLU. The base case `k = 0` is a bare affine map `ℝ^n → ℝ` (depth 1, no
hidden layers); the successor case peels off the first affine map into a hidden layer of
some width `m`, applies `ReLU`, and requires the remaining function `g : ℝ^m → ℝ` to be
computed by a network with `k` hidden layers. -/
def NetComputes : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : AffineMap n 1, ∀ x, f x = T.eval x 0
  | n, k + 1, f =>
      ∃ (m : ℕ) (T : AffineMap n m) (g : (Fin m → ℝ) → ℝ),
        NetComputes m k g ∧ f = fun x => g (reluVec (T.eval x))

/-- `ReLUn n k`, the set of functions `ℝ^n → ℝ` representable by a ReLU network with *at
most* `k` hidden layers (see the module docstring for why "at most" rather than "exactly"
is the reading that makes Theorem 2 true). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, NetComputes n k' f }

/-- `CPWL n`, the set of continuous piecewise-linear functions `ℝ^n → ℝ`: `f` is continuous,
and there is a finite family of affine functions such that every point has a neighborhood
on which `f` coincides with one member of the family. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
      ∃ (m : ℕ) (φ : Fin m → AffineMap n 1),
        ∀ x : Fin n → ℝ, ∃ i : Fin m, ∀ᶠ y in nhds x, f y = (φ i).eval y 0 }

/-- The depth bound `⌈log₃(n - 1)⌉ + 1` from the paper, with `log₃` the real logarithm to
base `3` and `⌈·⌉` the ceiling (as `Nat.ceil` of a real number). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log₃(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent010

import Mathlib

namespace Agent016

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We formalize:

  Theorem 2. For n ≥ 3, CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}.

## Modelling choices (see summary at the end of the file / final chat reply)

* Vectors `ℝ^n` are modelled as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is modelled concretely as a pair `(A, c)` of a
  matrix `A : Matrix (Fin b) (Fin a) ℝ` and a bias vector `c : Fin b → ℝ`, applied as
  `x ↦ A.mulVec x + c`.
* "Computed by a ReLU network with `k` hidden layers" is defined by structural recursion
  on `k` (as an inductive predicate `ComputesHidden`), directly mirroring the alternating
  composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper: a network with
  `0` hidden layers is a single affine map to `ℝ^1`; a network with `k+1` hidden layers is
  an affine map into some intermediate width `m`, followed by a component-wise ReLU,
  followed by a network with `k` hidden layers on `ℝ^m`.
* `ReLUn n k` is the set of functions representable with **at most** `k` hidden layers
  (i.e. `∃ k' ≤ k`), not exactly `k`. This is the standard reading in the expressivity
  literature (adding hidden layers never hurts, since a network with fewer hidden layers
  can always be padded to a deeper one), and it is the reading that makes an equality
  `CPWL_n = ReLU_{n,k}` for a *specific* `k` a meaningful, non-vacuous statement (namely:
  `k` hidden layers suffice for *all* of `CPWL_n`, and no CPWL function needs more).
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of affine
  functions such that `f` locally agrees (in a neighbourhood of every point) with one
  member of the family. This is a genuine piecewise-linearity condition (not "representable
  by some ReLU network", and not a global max-of-affine normal form), following the spec.
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined using `Real.logb 3` and `Nat.ceil`.
-/

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias vector. -/
def AffineT (a b : ℕ) : Type := (Matrix (Fin b) (Fin a) ℝ) × (Fin b → ℝ)

/-- Evaluate an affine transformation: `x ↦ A * x + c`. -/
def applyAffine {a b : ℕ} (T : AffineT a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.1.mulVec x + T.2

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Component-wise application of ReLU to a vector. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- `ComputesHidden n k f` means the function `f : ℝ^n → ℝ` is computed by a ReLU network
with input dimension `n` and exactly `k` hidden layers, i.e. `f` is the alternating
composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations
with `k` component-wise applications of ReLU in between, ending in output dimension `1`. -/
inductive ComputesHidden : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | zero {n : ℕ} (T : AffineT n 1) :
      ComputesHidden n 0 (fun x => applyAffine T x 0)
  | succ {n m k : ℕ} (T : AffineT n m) {g : (Fin m → ℝ) → ℝ}
      (hg : ComputesHidden m k g) :
      ComputesHidden n (k + 1) (fun x => g (reluVec (applyAffine T x)))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, ComputesHidden n k' f }

/-- An affine function `ℝ^n → ℝ`, given as `x ↦ ⟨a, x⟩ + c` for some coefficient vector
`a` and constant `c`. -/
def IsAffineFun {n : ℕ} (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (c : ℝ), ∀ x, g x = (∑ i, a i * x i) + c

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: those that
are continuous and, at every point, locally agree with one member of some fixed finite
family of affine functions. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
      ∃ (m : ℕ) (g : Fin m → ((Fin n → ℝ) → ℝ)),
        (∀ i, IsAffineFun (g i)) ∧
        ∀ x : Fin n → ℝ, ∃ i, ∀ᶠ y in nhds x, f y = g i y }

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from Theorem 2. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, the CPWL functions on `ℝ^n` are exactly those representable
by a ReLU network with at most `⌈log_3(n - 1)⌉ + 1` hidden layers. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent016

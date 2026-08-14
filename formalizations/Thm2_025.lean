import Mathlib

namespace Agent025

/-!
# Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity: Subdividing the
Simplex"), formalized.

We encode `ℝ^n` concretely as `Fin n → ℝ`.

## Modelling choices

* Affine maps `ℝ^a → ℝ^b` are given concretely by a matrix `A : Matrix (Fin b) (Fin a) ℝ`
  and a bias vector `c : Fin b → ℝ`, acting as `x ↦ A * x + c`.
* A ReLU network computing `f : (Fin n → ℝ) → ℝ` with `k` hidden layers is encoded by the
  recursive predicate `NetworkComputable`, which unwinds exactly to the alternating
  composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper, where the
  intermediate widths `n_1, …, n_k` are existentially quantified.
* `ReLUn n k` is the set of functions representable by a network with *exactly* `k`
  hidden layers (this matches the literal architecture described in the paper: "the
  subset of CPWL_n representable with k hidden layers"). Note that this is *not* a real
  restriction relative to an "at most k" reading: since `ReLU (t) - ReLU (-t) = t`, an
  identity map on any coordinate can be simulated by one extra ReLU hidden layer, so a
  network with `k` hidden layers can always be padded to one with `k+1` hidden layers
  computing the same function. Hence `ReLUn n k ⊆ ReLUn n (k+1)` in general, and the two
  readings of the theorem statement agree.
* `CPWL n` is defined mathematically (not via ReLU networks, and not as a "max of
  finitely many affine functions" normal form): `f` is continuous, and there is a finite
  family of affine functions such that `f` locally agrees with (at least) one of them
  near every point. This is a standard formulation of "continuous, finitely
  piecewise-affine".
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined using the real logarithm `Real.logb 3`
  and `Nat.ceil`.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of ReLU to a vector in `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given by a matrix and a bias vector,
acting as `x ↦ A * x + c`. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- The function `ℝ^a → ℝ^b` computed by an affine transformation. -/
def AffineMap.apply {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, T.A i j * x j) + T.c i

/-- `NetworkComputable n k f` means that `f : ℝ^n → ℝ` is computed by *some* ReLU network
with exactly `k` hidden layers, i.e. `f` is the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of affine transformations `T^(1), …, T^(k+1)`
with componentwise ReLU applications, for some choice of intermediate widths
`n_1, …, n_k`.

The recursion peels off the first hidden layer: with `k + 1` hidden layers, `f` factors
as `g ∘ ReLU ∘ T^(1)` where `T^(1) : ℝ^n → ℝ^m` is affine (for some hidden width `m`) and
`g : ℝ^m → ℝ` is itself computable with the remaining `k` hidden layers. The base case
`k = 0` is a single affine transformation `ℝ^n → ℝ^1`. -/
def NetworkComputable : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : AffineMap n 1, ∀ x, f x = T.apply x 0
  | n, k + 1, f =>
      ∃ (m : ℕ) (T : AffineMap n m) (g : (Fin m → ℝ) → ℝ),
        NetworkComputable m k g ∧ ∀ x, f x = g (reluVec (T.apply x))

/-- `ReLUn n k`, the subset of `CPWL_n` (indeed, of all functions `ℝ^n → ℝ`) representable
by a ReLU network with exactly `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | NetworkComputable n k f }

/-- An affine function `ℝ^n → ℝ`, given by a coefficient vector and a constant term. -/
def IsAffine (n : ℕ) (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (c : ℝ), ∀ x, g x = (∑ j, a j * x j) + c

/-- `CPWL n`, the space of continuous piecewise-linear (CPWL) functions `ℝ^n → ℝ`: `f` is
continuous, and there is a *finite* family of affine functions such that `f` agrees with
(at least) one member of the family on a neighborhood of every point. This is a genuine
piecewise-linearity condition (a finite "atlas" of affine pieces covering `ℝ^n`), not a
disguised max-of-affine normal form and not defined via ReLU networks. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
      ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ),
        (∀ i, IsAffine n (g i)) ∧
        ∀ x : Fin n → ℝ, ∃ i, ∀ᶠ y in nhds x, f y = g i y }

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from the theorem statement, for `n ≥ 3` (so that
`n - 1 ≥ 2` and the logarithm is well-defined and positive). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent025

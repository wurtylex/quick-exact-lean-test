import Mathlib

namespace Agent024

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We model an `n`-dimensional real vector as a function `Fin n → ℝ`.

An affine transformation `ℝ^a → ℝ^b` is modelled concretely as `x ↦ A.mulVec x + c`
for a matrix `A : Matrix (Fin b) (Fin a) ℝ` and a bias vector `c : Fin b → ℝ`.

A ReLU network with `k` hidden layers computing `f : (Fin n → ℝ) → ℝ` is modelled by
the inductive predicate `NetComputes n k f`, which unfolds exactly the alternating
composition
    `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ... ∘ ReLU ∘ T^(1)`
from the paper: the base case `k = 0` is a single affine map `n → 1` (no hidden
layers, no ReLU applied); the successor case peels off the first affine map
`T^(1) : n → m` together with the following componentwise ReLU, and recurses on a
network with `k` hidden layers from the (existentially quantified) intermediate
width `m`.

`ReLUn n k` is then the set of functions representable with **at most** `k` hidden
layers (the standard convention for this notation in the depth-separation
literature: `ReLU_{n,k}` is monotone increasing in `k`, since one can always pad a
shallower network with extra trivial affine+ReLU layers to reach exactly `k`
hidden layers without changing the represented function). With this convention
`CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}` says: every CPWL function on `ℝ^n` is
representable with at most that many hidden layers (and, trivially, every function
representable with that many hidden layers is CPWL).

`CPWL n` is defined as the continuous functions that are, near every point, equal
to one of finitely many affine functions (a genuine local piecewise-linearity
condition on a finite family of affine pieces — not defined via ReLU networks and
not via a max-of-affines normal form).
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector. -/
def reluVec {m : ℕ} (v : Fin m → ℝ) : Fin m → ℝ := fun i => relu (v i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias
vector. -/
structure Affine (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- The function computed by an affine transformation. -/
def Affine.toFun {a b : ℕ} (T : Affine a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `NetComputes n k f` holds iff `f : (Fin n → ℝ) → ℝ` is computed by some ReLU
network with input dimension `n`, exactly `k` hidden layers, and output dimension
`1`, i.e. by some alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`
of affine transformations `T^(1), …, T^(k+1)` (with the intermediate widths
`n_1, …, n_k` existentially quantified). -/
inductive NetComputes : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop where
  /-- Zero hidden layers: the network is a single affine map `T^(1) : ℝ^n → ℝ`. -/
  | base {n : ℕ} (T : Affine n 1) :
      NetComputes n 0 (fun x => T.toFun x 0)
  /-- `k + 1` hidden layers: apply the first affine map `T^(1) : ℝ^n → ℝ^m`,
  then componentwise ReLU, then recurse on a network with `k` hidden layers
  from the intermediate width `m`. -/
  | step {n m k : ℕ} (T : Affine n m) {f : (Fin m → ℝ) → ℝ}
      (hf : NetComputes m k f) :
      NetComputes n (k + 1) (fun x => f (reluVec (T.toFun x)))

/-- The set of functions `ℝ^n → ℝ` representable by a ReLU network with **at most**
`k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, NetComputes n k' f}

/-- The space of continuous piecewise linear functions `ℝ^n → ℝ`: continuous
functions that, in a neighbourhood of every point, coincide with one of finitely
many affine functions. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ N : ℕ, ∃ pieces : Fin N → Affine n 1,
      ∀ x : Fin n → ℝ, ∃ i : Fin N, ∀ᶠ y in nhds x, f y = (pieces i).toFun y 0}

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from the theorem, with the ceiling of the
real logarithm base `3` taken via `Nat.ceil`. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, the continuous piecewise linear functions on `ℝ^n`
are exactly those representable by a ReLU network with at most
`⌈log_3(n - 1)⌉ + 1` hidden layers. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent024

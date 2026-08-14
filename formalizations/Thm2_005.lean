import Mathlib

namespace Agent005

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We model `ℝ^n` concretely as `Fin n → ℝ`.

## Modelling choices (see summary at the end)

* Affine maps `ℝ^a → ℝ^b` are modelled concretely by a matrix `A : Matrix (Fin b) (Fin a) ℝ`
  and a bias vector `c : Fin b → ℝ`, via `x ↦ A.mulVec x + c`.
* A ReLU network with `k` hidden layers computing `f : (Fin n → ℝ) → ℝ` is defined
  *recursively* on `k`: with `0` hidden layers, `f` is exactly one affine (scalar-valued)
  map; with `k+1` hidden layers, `f` factors as (some function computable with `k` hidden
  layers on `m` real inputs) composed with (an affine map `ℝ^n → ℝ^m` followed by
  componentwise ReLU).
* `ReLUn n k` is taken to be the set of functions representable with **at most** `k`
  hidden layers (i.e. `∃ k' ≤ k`), matching the usual convention that these expressivity
  classes are increasing in `k` (`ReLUn n k ⊆ ReLUn n (k+1)`), which is the reading under
  which the stated equality `CPWL n = ReLUn n (depthBound n)` is the correct/true
  statement of Theorem 2 (a function needing strictly fewer than the bound is still in the
  class).
* `CPWL n` is defined as: continuous functions `f` that agree, in a neighborhood of every
  point, with one of finitely many affine functions (a genuine local-piecewise-linearity
  condition, not simply "representable by a ReLU network" and not a max-of-affine normal
  form).
* The depth bound `⌈log_3 (n-1)⌉ + 1` is defined using the real logarithm `Real.logb 3`
  together with `Nat.ceil`.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (v : Fin m → ℝ) : Fin m → ℝ := fun i => relu (v i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias vector. -/
def affineComp {a b : ℕ} (A : Matrix (Fin b) (Fin a) ℝ) (c : Fin b → ℝ) (x : Fin a → ℝ) :
    Fin b → ℝ :=
  A.mulVec x + c

/-- A scalar-valued (i.e. `ℝ^a → ℝ`) affine map, given by a weight vector and a bias. -/
def affineScalar {a : ℕ} (w : Fin a → ℝ) (c : ℝ) (x : Fin a → ℝ) : ℝ :=
  (Finset.univ.sum fun i => w i * x i) + c

/-- `f` is affine, i.e. of the form `x ↦ ⟨w, x⟩ + c`. -/
def IsAffine {a : ℕ} (f : (Fin a → ℝ) → ℝ) : Prop :=
  ∃ (w : Fin a → ℝ) (c : ℝ), f = affineScalar w c

/-- `computesReLU k n f` means: `f : ℝ^n → ℝ` is *exactly* computed by a ReLU network with
`k` hidden layers, i.e. by an alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`
of `k + 1` affine transformations with componentwise ReLU applications in between.
Recursion is on the number of hidden layers: with `0` hidden layers the network is a
single affine map; with `k + 1` hidden layers, the first affine map `T^(1) : ℝ^n → ℝ^m`
followed by a ReLU is applied, and the remaining computation is a `k`-hidden-layer network
on the `m` resulting coordinates. -/
def computesReLU : ℕ → (n : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | 0, n, f => IsAffine f
  | (k + 1), n, f =>
      ∃ (m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ) (g : (Fin m → ℝ) → ℝ),
        computesReLU k m g ∧ f = g ∘ (fun x => reluVec (affineComp A c x))

/-- `ReLUn n k`: the set of functions `ℝ^n → ℝ` representable by a ReLU network with
**at most** `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, computesReLU k' n f}

/-- `CPWL n`: the continuous, piecewise-linear functions `ℝ^n → ℝ`. A function is CPWL if
it is continuous and, around every point, agrees with one of finitely many affine
functions (a genuine local piecewise-affineness condition). -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
      ∃ F : Finset ((Fin n → ℝ) → ℝ), (∀ g ∈ F, IsAffine g) ∧
        ∀ x : Fin n → ℝ, ∃ g ∈ F, ∃ U : Set (Fin n → ℝ), IsOpen U ∧ x ∈ U ∧ Set.EqOn f g U}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so `n - 1 ≥ 2`). -/
def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent005

import Mathlib

namespace Agent056

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

`CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}` for `n ≥ 3`.

## Modelling choices

* Vectors `ℝ^n` are encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is packaged as a matrix `A : Matrix (Fin b) (Fin a) ℝ`
  together with a bias vector `bias : Fin b → ℝ`, evaluated as `x ↦ A.mulVec x + bias`.
* A ReLU network with input dimension `n` and `k` hidden layers and (scalar) output is
  defined as an inductive family `ReLUNet n k`:
  - `output T` : a network with `0` hidden layers, i.e. a single affine map
    `T : AffMap n 1` (this realizes `T^{(1)}`, the depth-`1` case with no hidden layers).
  - `layer T rest` : a network with `k+1` hidden layers, consisting of an affine map
    `T : AffMap n m` (this is `T^{(1)}`) followed by componentwise `ReLU`, followed by a
    network `rest : ReLUNet m k` computing the rest of the alternating composition
    `T^{(k+2)} ∘ ReLU ∘ ⋯ ∘ ReLU ∘ T^{(2)}`.
  Unfolding `ReLUNet.compute` on `layer T₁ (layer T₂ (⋯ (output T_{k+1})))` literally produces
  `T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}` applied to the input, matching the paper's
  definition of what a ReLU network computes.
* `ReLUn n k` is the set of functions representable with **at most** `k` hidden layers
  (i.e. `∃ k' ≤ k`, a network with `k'` hidden layers computing `f`). This is the standard
  convention in the neural-network-depth literature (e.g. Hertrich et al.): it makes
  `ReLUn n k` monotone increasing in `k`, which is what makes an *equality*
  `CPWL_n = ReLU_{n,k}` (rather than merely `⊇`) a sensible and true statement once `k`
  reaches the stated depth bound, since any network can be padded with extra layers that
  implement the identity via `ReLU(x) - ReLU(-x) = x`.
* `CPWL n` is defined mathematically (not via ReLU networks, and not as a "max of finitely
  many affine functions" normal form) as: `f` is continuous, and there is a *finite* family
  of affine functionals `ℝ^n → ℝ` such that every point `x` has a neighborhood on which `f`
  coincides with (at least) one member of the family. This is the standard "finite polyhedral
  subdivision, affine on each piece" reading of continuous piecewise linearity.
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined explicitly using the real logarithm
  `Real.logb 3` and `Nat.ceil`, exactly mirroring the paper's real-valued ceiling expression.
-/

/-- The scalar ReLU function `x ↦ max 0 x`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (v : Fin m → ℝ) : Fin m → ℝ := fun i => relu (v i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias vector. -/
structure AffMap (a b : ℕ) where
  /-- The linear part. -/
  A : Matrix (Fin b) (Fin a) ℝ
  /-- The translation part. -/
  bias : Fin b → ℝ

/-- Evaluation of an affine transformation: `x ↦ A * x + bias`. -/
def AffMap.eval {a b : ℕ} (T : AffMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.bias

/-- A ReLU network with input dimension `n`, `k` hidden layers, and scalar output,
built by peeling off affine transformations and `ReLU` activations one hidden layer at a time,
exactly following the alternating composition
`T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}`
from the paper's definition of a ReLU network. -/
inductive ReLUNet : ℕ → ℕ → Type where
  /-- `0` hidden layers: a single affine map `ℝ^n → ℝ` (this is `T^{(1)}` alone). -/
  | output {n : ℕ} (T : AffMap n 1) : ReLUNet n 0
  /-- `k+1` hidden layers: an affine map to a hidden layer of width `m`, a `ReLU`
  activation, and then a network with `k` hidden layers computing the rest. -/
  | layer {n m k : ℕ} (T : AffMap n m) (rest : ReLUNet m k) : ReLUNet n (k + 1)

/-- The function `ℝ^n → ℝ` computed by a ReLU network, following the alternating composition
of affine maps and componentwise `ReLU`. -/
def ReLUNet.compute {n k : ℕ} : ReLUNet n k → (Fin n → ℝ) → ℝ
  | ReLUNet.output T, x => T.eval x 0
  | ReLUNet.layer T rest, x => rest.compute (reluVec (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
**at most** `k` hidden layers (the standard convention making `ReLUn n ·` monotone in `k`). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, ∃ net : ReLUNet n k', ∀ x, f x = net.compute x }

/-- An affine functional `ℝ^n → ℝ`, given by a coefficient vector and a constant term. -/
structure AffineFunctional (n : ℕ) where
  /-- The linear coefficients. -/
  coeff : Fin n → ℝ
  /-- The constant term. -/
  const : ℝ

/-- Evaluation of an affine functional: `x ↦ ⟨coeff, x⟩ + const`. -/
def AffineFunctional.eval {n : ℕ} (g : AffineFunctional n) (x : Fin n → ℝ) : ℝ :=
  (Finset.univ.sum fun i => g.coeff i * x i) + g.const

/-- `CPWL n` is the space of continuous piecewise-linear functions `ℝ^n → ℝ`: functions that
are continuous and are given, near every point, by one of finitely many affine functionals
(a finite polyhedral subdivision on whose pieces `f` is affine). -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
      ∃ (m : ℕ) (g : Fin m → AffineFunctional n),
        ∀ x : Fin n → ℝ, ∃ i : Fin m, ∀ᶠ y in nhds x, f y = (g i).eval y }

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from the paper, as a natural number, using the real
base-`3` logarithm and the ceiling function. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent056

import Mathlib

namespace Agent018

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):  for `n ≥ 3`,  `CPWL n = ReLUn n (⌈log₃(n-1)⌉ + 1)`.

## Modelling choices

* Vectors `ℝ^m` are encoded as `Fin m → ℝ`.
* Affine transformations `ℝ^a → ℝ^b` are given concretely by a matrix `A : Matrix (Fin b)
  (Fin a) ℝ` together with a bias vector `c : Fin b → ℝ`, evaluated as `x ↦ A.mulVec x + c`.
* A ReLU network with `k` hidden layers and input dimension `n` is modelled by the inductive
  type `ReLUNet n k`: either a single affine map `ℝ^n → ℝ` (the `k = 0` case, i.e. depth `1`,
  no hidden layers), or an affine map `ℝ^n → ℝ^m` followed by componentwise ReLU and then a
  network with `k` hidden layers on `ℝ^m` (the `k + 1` case). This exactly encodes the
  alternating composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper.
* `ReLUn n k` is the set of functions representable by a network with **at most** `k` hidden
  layers (rather than *exactly* `k`). We choose this reading because it is the one that makes
  statements like Theorem 2 meaningful and true: representability is monotone in the number of
  hidden layers (a network with fewer layers can always be reproduced, via standard padding
  tricks, by one with more layers), so "the depth needed to represent all of `CPWL n`" should be
  read as a least upper bound, i.e. "representable with at most this many hidden layers".
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of scalar affine
  functions `g_1, …, g_m : ℝ^n → ℝ` such that every point `x` has a neighbourhood on which `f`
  coincides with (at least) one of the `g_i`. This is a genuine local-piecewise-affine condition
  (not defined as "representable by some ReLU network", and not a max-of-affine normal form).
* The depth bound `⌈log₃(n-1)⌉ + 1` is defined using the real logarithm `Real.logb 3` and
  `Nat.ceil`, matching the paper's real-valued ceiling of `log_3(n-1)`.
-/

/-- The ReLU function on `ℝ`. -/
noncomputable def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
noncomputable def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ :=
  fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias vector. -/
structure AffineMap' (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation: `x ↦ A x + c`. -/
def AffineMap'.eval {a b : ℕ} (T : AffineMap' a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- A ReLU network with input dimension `n` and `k` hidden layers, outputting a scalar.
`ReLUNet.output T` is a network with `0` hidden layers (just the affine map `T : ℝ^n → ℝ`,
i.e. `T^(1)` alone). `ReLUNet.layer T rest` prepends an affine map `T : ℝ^n → ℝ^m`
and a ReLU nonlinearity to a network `rest` with `k` hidden layers on `ℝ^m`, producing a
network with `k + 1` hidden layers on `ℝ^n`. This encodes exactly the alternating
composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`. -/
inductive ReLUNet : ℕ → ℕ → Type
  | output {n : ℕ} (T : AffineMap' n 1) : ReLUNet n 0
  | layer {n m k : ℕ} (T : AffineMap' n m) (rest : ReLUNet m k) : ReLUNet n (k + 1)

/-- The function `ℝ^n → ℝ` computed by a ReLU network. -/
noncomputable def ReLUNet.eval : ∀ {n k : ℕ}, ReLUNet n k → (Fin n → ℝ) → ℝ
  | _, _, ReLUNet.output T, x => T.eval x 0
  | _, _, ReLUNet.layer T rest, x => rest.eval (reluVec (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
**at most** `k` hidden layers (see the discussion above for why "at most" rather than
"exactly" is the reading that makes Theorem 2 correct). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ j ≤ k, ∃ N : ReLUNet n j, f = N.eval}

/-- A scalar affine function `ℝ^n → ℝ`, `x ↦ ⟨a, x⟩ + b`. -/
structure ScalarAffine (n : ℕ) where
  a : Fin n → ℝ
  b : ℝ

/-- Evaluation of a scalar affine function. -/
def ScalarAffine.eval {n : ℕ} (g : ScalarAffine n) (x : Fin n → ℝ) : ℝ :=
  (∑ i, g.a i * x i) + g.b

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: those that are
continuous and, at every point, locally agree with one of a finite family of scalar affine
functions. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (g : Fin m → ScalarAffine n),
      ∀ x : Fin n → ℝ, ∃ i : Fin m, ∀ᶠ y in nhds x, f y = (g i).eval y}

/-- The depth bound `⌈log₃(n - 1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so `n - 1 ≥ 2`). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL n = ReLUn n (⌈log₃(n-1)⌉ + 1)`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent018

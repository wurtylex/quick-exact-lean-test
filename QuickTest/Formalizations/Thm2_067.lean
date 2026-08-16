import Mathlib

namespace Agent067

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

**Modelling choices** (see summary at call site):
* Vectors `ℝ^n` are encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is encoded concretely as `x ↦ W.mulVec x + c` for a
  matrix `W : Matrix (Fin b) (Fin a) ℝ` and bias `c : Fin b → ℝ`.
* "Representable with `k` hidden layers" (`Represents`) is defined by recursion on `k`,
  directly mirroring the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper, peeling off the first affine
  map / ReLU pair at each recursive step. `ReLUn n k` is the set of functions representable
  with *exactly* `k` hidden layers (the direct reading of "the subset of `CPWL_n`
  representable with `k` hidden layers"); note that padding with an extra trivial
  identity-simulating hidden layer (via `ReLU(x) - ReLU(-x) = x`) shows this is in fact
  monotone in `k`, so "exactly `k`" and "at most `k`" agree for `k ≥ 1`, making this choice
  harmless for the truth of the theorem.
* `CPWL n` is defined as: `f` is continuous, and there is a *finite family* of affine
  functions (indexed by `Fin m` for some `m`) such that every point `x` has a neighbourhood
  on which `f` coincides with (at least) one member of the family. This is a genuine
  piecewise-linearity condition (local agreement with a finite affine atlas), not a
  max-of-affine normal form and not "representable by a ReLU network".
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded with the real `Real.logb 3` and `Nat.ceil`
  (`⌈·⌉₊`), applied to `(n : ℝ) - 1`.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^n`. -/
def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => relu (x i)

/-- Evaluation of an affine transformation `ℝ^a → ℝ^b` given by a matrix `W` and bias `c`. -/
def affineEval {a b : ℕ} (W : Matrix (Fin b) (Fin a) ℝ) (c : Fin b → ℝ) (x : Fin a → ℝ) :
    Fin b → ℝ :=
  W.mulVec x + c

/-- `Represents n k f` means `f : ℝ^n → ℝ` is computed by a ReLU network with `k` hidden
layers, i.e. `f = T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` for some affine transformations
`T^(1), …, T^(k+1)` of compatible (existentially quantified, except the input dimension `n`
and output dimension `1`) widths.

The recursion peels off the first affine map `T^(1) : ℝ^n → ℝ^m` together with the
following `ReLU`, leaving a function `h` of the remaining `k - 1` layers on the
(existentially quantified) hidden width `m`. The base case `k = 0` is a single affine map
`ℝ^n → ℝ` (`T^(1)`, with no `ReLU` applied). -/
def Represents : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ w : Fin n → ℝ, ∃ b : ℝ, f = fun x => (∑ i, w i * x i) + b
  | n, k + 1, f =>
      ∃ m : ℕ, ∃ W : Matrix (Fin m) (Fin n) ℝ, ∃ c : Fin m → ℝ, ∃ h : (Fin m → ℝ) → ℝ,
        Represents m k h ∧ f = fun x => h (reluVec (affineEval W c x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
exactly `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Represents n k f}

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: `f` is
continuous, and there is a finite family of affine functions, indexed by `Fin m`, such that
every point of `ℝ^n` has a neighbourhood on which `f` agrees with one member of the family. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
        ∃ m : ℕ, ∃ w : Fin m → Fin n → ℝ, ∃ b : Fin m → ℝ,
          ∀ x : Fin n → ℝ, ∃ i : Fin m,
            ∀ᶠ y in nhds x, f y = (∑ j, w i j * y j) + b i}

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from the paper, for `n ≥ 3` (so `n - 1 ≥ 2`). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent067

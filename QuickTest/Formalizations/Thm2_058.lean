import Mathlib

namespace Agent058

open Filter

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We encode `ℝ^n` concretely as `Fin n → ℝ`.

Modelling choices (see final summary):
* Affine maps `ℝ^a → ℝ^b` are given concretely by a matrix and a bias vector.
* A "ReLU network with `k` hidden layers" is encoded via a width function on `ℕ`
  (built from the fixed input dimension `n` and a free choice of hidden widths)
  together with a dependent family of affine layers, composed with `reluVec` inserted
  after every layer except the last.
* `ReLUn n k` is the set of functions representable with **at most** `k` hidden
  layers (monotone increasing in `k`), which is the standard reading making
  `ReLU_{n,k}` an increasing filtration of `CPWL_n` and matches Theorem 1's
  statement "`MAX_{3^n+2} ∈ ReLU_{n+1}`".
* `CPWL n` is defined as: continuous, and locally (in a neighborhood of every
  point) equal to one of finitely many affine functions. This is a genuine
  piecewise-linearity condition, not a "max of affine functions" normal form and
  not "representable by some ReLU network".
* The depth bound uses the real logarithm `Real.logb 3` together with `Nat.ceil`.
-/

/-- The ReLU activation function on `ℝ`. -/
noncomputable def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector in `ℝ^m`. -/
noncomputable def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ :=
  fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias
vector: `x ↦ A * x + c`. -/
structure AffineMapRn (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine map on a vector. -/
noncomputable def AffineMapRn.eval {a b : ℕ} (T : AffineMapRn a b) (x : Fin a → ℝ) :
    Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- Given the input dimension `n` and a choice of hidden widths `hidden : ℕ → ℕ`
(where `hidden i` is meant to be the width of hidden layer `i`), `mkWidths n hidden`
is the width function `widths : ℕ → ℕ` with `widths 0 = n` (definitionally) and
`widths (i+1) = hidden i`. -/
def mkWidths (n : ℕ) (hidden : ℕ → ℕ) : ℕ → ℕ
  | 0 => n
  | (i + 1) => hidden i

/-- `netApply widths T k m x` evaluates the first `m` layers `T 0, ..., T (m-1)` of a
network with layer-width function `widths` and layer family `T`, applying `relu`
after every layer *except* layer `k` (the intended final layer, `T^(k+1)` in the
paper's notation, indexed `k` here since layers are `0`-indexed). Composing up to
`m = k + 1` therefore computes
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`, i.e. a network with `k` hidden
layers. -/
noncomputable def netApply (widths : ℕ → ℕ)
    (T : (i : ℕ) → AffineMapRn (widths i) (widths (i + 1))) (k : ℕ) :
    (m : ℕ) → (Fin (widths 0) → ℝ) → (Fin (widths m) → ℝ)
  | 0, x => x
  | (m + 1), x =>
      let y := (T m).eval (netApply widths T k m x)
      if m + 1 ≤ k then reluVec y else y

/-- The set of functions `ℝ^n → ℝ` representable by a ReLU network with *at most*
`k` hidden layers: there is some `j ≤ k`, a choice of `j` hidden widths, and a
family of `j + 1` affine layers `T^(1), ..., T^(j+1)` (of matching dimensions,
with output dimension `1`) whose alternating ReLU composition computes `f`. -/
noncomputable def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ (j : ℕ), j ≤ k ∧
      ∃ (hidden : ℕ → ℕ) (hwj : mkWidths n hidden (j + 1) = 1)
        (T : (i : ℕ) → AffineMapRn (mkWidths n hidden i) (mkWidths n hidden (i + 1))),
        f = fun x => netApply (mkWidths n hidden) T j (j + 1) x
          (Fin.cast hwj.symm (0 : Fin 1))}

/-- The set of continuous piecewise-linear functions `ℝ^n → ℝ`: `f` is continuous,
and there is a *finite* family of affine functions such that every point of `ℝ^n`
has a neighborhood on which `f` agrees with one member of the family. -/
noncomputable def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (g : Fin m → AffineMapRn n 1),
      ∀ x : Fin n → ℝ, ∃ i : Fin m, ∀ᶠ y in nhds x, f y = (g i).eval y 0}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, using the real logarithm
base `3` and `Nat.ceil`. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, every continuous piecewise-linear function on `ℝ^n`
is representable by a ReLU network with `⌈log_3 (n - 1)⌉ + 1` hidden layers, and
conversely. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent058

import Mathlib

namespace Agent014

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):  for `n ≥ 3`,  `CPWL n = ReLUn n (⌈log_3 (n-1)⌉ + 1)`.

## Modelling choices

* `ℝ^n` is encoded as `Fin n → ℝ`.
* Affine transformations `ℝ^a → ℝ^b` are modelled concretely as `x ↦ A * x + c` via the
  structure `AffineT`.
* A ReLU network with `k` hidden layers computing `f : (Fin n → ℝ) → ℝ` is modelled by the
  predicate `IsReLUNetFun n k f`, defined by recursion on `k`, which literally unfolds the
  alternating composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper: the
  base case `k = 0` is a single affine map `ℝ^n → ℝ` (no ReLU, i.e. depth 1, the last
  affine transform `T^(k+1)`), and the successor case peels off the first affine map
  `T^(1) : ℝ^n → ℝ^m`, applies `ReLU` componentwise, and recurses on a network with `k`
  fewer hidden layers computing the rest.  This reading takes `ReLUn n k` to mean
  "representable by a network with *exactly* `k` hidden layers" (matching the paper's
  literal phrasing "representable with `k` hidden layers"); this is harmless for the
  theorem because a network with `k` hidden layers can always be padded into one with
  `k+1` hidden layers (insert an extra affine layer that is the identity, followed by
  `ReLU` applied to an appropriately shifted/duplicated copy of the coordinates), so the
  classes `ReLUn n k` are increasing in `k` and the equality with `CPWL n` at the stated
  bound is the intended, faithful statement.
* `CPWL n` is defined honestly via a genuine finite polyhedral subdivision: `f` is CPWL if
  it is continuous and there is a finite family of "pieces", each given by an affine
  function together with a polyhedral region (a finite intersection of half-spaces
  `{x | ⟨normal, x⟩ ≤ bound}`), whose regions cover `ℝ^n` and on each of which `f` agrees
  with the piece's affine function.  This is *not* "representable by some ReLU network"
  and *not* a max-of-affine normal form.
* The depth bound `⌈log_3 (n-1)⌉ + 1` is defined using `Real.logb 3` and `Nat.ceil` (`⌈·⌉₊`).
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector in `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix `A` and a
translation vector `c`, computing `x ↦ A * x + c`. -/
structure AffineT (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def AffineT.eval {a b : ℕ} (T : AffineT a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `IsReLUNetFun n k f` means `f : ℝ^n → ℝ` is computed by a ReLU network with exactly `k`
hidden layers, i.e. `f` is the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations
`T^(1), …, T^(k+1)` interspersed with componentwise `ReLU`.  Defined by recursion on `k`:
the base case is a single affine map (the final transform `T^(k+1)`, no `ReLU`), and each
successor step peels off the first affine transform together with its following `ReLU`. -/
def IsReLUNetFun : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : AffineT n 1, ∀ x, f x = T.eval x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : AffineT n m) (g : (Fin m → ℝ) → ℝ),
        IsReLUNetFun m k g ∧ ∀ x, f x = g (reluVec (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
`k` hidden layers (i.e. depth `k + 1`). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) := {f | IsReLUNetFun n k f}

/-- A single piece of a piecewise-linear subdivision of `ℝ^n`: an affine function together
with a polyhedral region on which it is meant to agree with the global function, the
region being given as a finite intersection of half-spaces `⟨normal j, x⟩ ≤ bound j`. -/
structure PWLPiece (n : ℕ) where
  aff : AffineT n 1
  numConstraints : ℕ
  normal : Fin numConstraints → (Fin n → ℝ)
  bound : Fin numConstraints → ℝ

/-- The polyhedral region associated to a piece. -/
def PWLPiece.region {n : ℕ} (P : PWLPiece n) : Set (Fin n → ℝ) :=
  {x | ∀ j, (∑ i, P.normal j i * x i) ≤ P.bound j}

/-- `f : ℝ^n → ℝ` is continuous and piecewise linear: it is continuous, and there is a
finite family of pieces, each a polyhedral region together with an affine function, whose
regions cover all of `ℝ^n` and on each of which `f` agrees with the piece's affine
function. -/
def IsCPWL (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  Continuous f ∧
    ∃ (ι : Type) (_ : Fintype ι) (pieces : ι → PWLPiece n),
      (⋃ i, (pieces i).region) = Set.univ ∧
        ∀ i, ∀ x ∈ (pieces i).region, f x = (pieces i).aff.eval x 0

/-- `CPWL n` is the set of continuous piecewise-linear functions `ℝ^n → ℝ`. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) := {f | IsCPWL n f}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, using the real logarithm to base
`3` and the natural-number ceiling. -/
noncomputable def depthBound (n : ℕ) : ℕ := ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL n = ReLUn n (⌈log_3 (n - 1)⌉ + 1)`. -/
theorem theorem2 : ∀ n : ℕ, n ≥ 3 → CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent014

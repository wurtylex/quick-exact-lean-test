import Mathlib

namespace Agent020

/-!
Formalization of Theorem 2 of arXiv:2505.14338
("Better Neural Network Expressivity: Subdividing the Simplex"):

  For `n ≥ 3`, `CPWL n = ReLUn n (⌈log_3 (n - 1)⌉ + 1)`.

## Modelling choices

* Vectors `ℝ^m` are encoded as `Vec m := Fin m → ℝ`.
* Affine transformations `ℝ^a → ℝ^b` are encoded concretely as a matrix/bias pair
  `(A, c) : Matrix (Fin b) (Fin a) ℝ × Vec b` acting by `x ↦ A.mulVec x + c`.
* A ReLU network with exactly `k` hidden layers, input dimension `n`, is encoded by
  the inductive family `ReLUNet n k`, mirroring the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper: the base case `k = 0`
  is a single affine map `ℝ^n → ℝ` (no hidden layer at all), and the inductive case
  prepends one affine map `ℝ^n → ℝ^m` followed componentwise by ReLU, then continues
  with a network with `k` hidden layers on the resulting `m`-dimensional hidden layer.
* `ReLUn n k` is the set of functions *exactly* representable with `k` hidden layers
  (matching the paper's literal phrasing "the network has k hidden layers"); this is
  consistent with Theorem 2 because any network can be padded with extra hidden
  layers implementing the identity (via the standard `x = ReLU(x) - ReLU(-x))`
  trick), so exact-`k` and at-most-`k` representability coincide once a function is
  known to be representable with some `k' ≤ k`.
* `CPWL n` is defined as: `f` is continuous, and there is a finite family of affine
  functionals `ℝ^n → ℝ` such that every point `x` has a neighbourhood on which `f`
  agrees with one of them. This is a genuine local piecewise-affine condition (not a
  "max of affine functions" normal form, and not "representable by a ReLU network").
* The depth bound `⌈log_3 (n - 1)⌉ + 1` is encoded using `Real.logb 3` and `Nat.ceil`
  (`⌈·⌉₊`), applied to the real cast of the natural number `n - 1`.
-/

/-- `ℝ^m`, encoded as functions `Fin m → ℝ`. -/
def Vec (m : ℕ) : Type := Fin m → ℝ

/-- The scalar ReLU function `x ↦ max 0 x`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector. -/
def reluVec {m : ℕ} (x : Vec m) : Vec m := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias
vector: `x ↦ A * x + c`. -/
def AffineMap (a b : ℕ) : Type := Matrix (Fin b) (Fin a) ℝ × Vec b

/-- Evaluation of an affine transformation. -/
def AffineMap.eval {a b : ℕ} (T : AffineMap a b) (x : Vec a) : Vec b :=
  T.1.mulVec x + T.2

/-- A ReLU network with input dimension `n` and exactly `k` hidden layers, encoded as
the alternating composition of `k + 1` affine transformations with componentwise ReLU
applied after each of the first `k` of them.

* `output T` is a network with `0` hidden layers: it is just the single affine map
  `T : ℝ^n → ℝ` (the map `T^(1)` of the paper, applied with no ReLU at all).
* `layer T rest` is a network with `k + 1` hidden layers: first apply the affine map
  `T : ℝ^n → ℝ^m` and componentwise ReLU (this is the new hidden layer of width `m`),
  then continue with `rest`, a network with `k` hidden layers on `ℝ^m`. -/
inductive ReLUNet : ℕ → ℕ → Type where
  | output {n : ℕ} (T : AffineMap n 1) : ReLUNet n 0
  | layer {n m k : ℕ} (T : AffineMap n m) (rest : ReLUNet m k) : ReLUNet n (k + 1)

/-- The function `ℝ^n → ℝ` computed by a ReLU network. -/
def ReLUNet.compute : {n k : ℕ} → ReLUNet n k → Vec n → ℝ
  | _, _, ReLUNet.output T, x => T.eval x 0
  | _, _, ReLUNet.layer T rest, x => rest.compute (reluVec (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network
with input dimension `n` and *exactly* `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set (Vec n → ℝ) :=
  { f | ∃ net : ReLUNet n k, f = net.compute }

/-- An affine functional `ℝ^n → ℝ`, i.e. `x ↦ ⟨w, x⟩ + b` for some weight vector `w`
and bias `b`, packaged via `AffineMap n 1`. -/
def IsAffineFun {n : ℕ} (f : Vec n → ℝ) : Prop :=
  ∃ T : AffineMap n 1, f = fun x => T.eval x 0

/-- `CPWL n`, the space of continuous piecewise-linear functions `ℝ^n → ℝ`: `f` is
continuous, and there is a finite family of affine functionals such that every point
of `ℝ^n` has a neighbourhood on which `f` coincides with one member of the family. -/
def CPWL (n : ℕ) : Set (Vec n → ℝ) :=
  { f | Continuous f ∧
      ∃ (N : ℕ) (affines : Fin N → (Vec n → ℝ)),
        (∀ i, IsAffineFun (affines i)) ∧
        ∀ x : Vec n, ∃ i, ∀ᶠ y in nhds x, f y = affines i y }

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2. -/
def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n - 1 : ℕ) : ℝ)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent020

import Mathlib

namespace Agent074

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

"Better Neural Network Expressivity: Subdividing the Simplex"
(Bakaev, Brunck, Hertrich, Stade, Yehudayoff).

We encode `ℝ^n` concretely as `Fin n → ℝ`.

## Modelling choices

* `ReLU` networks are encoded as an inductive family `ReLUNet a k`, indexed by the input
  dimension `a` and the number `k` of hidden layers. A network with `k` hidden layers is
  either
    - (`k = 0`) a single affine transformation `T : ℝ^a → ℝ^1` (no ReLU at all), or
    - (`k = k' + 1`) an affine transformation `T : ℝ^a → ℝ^m` followed by a componentwise
      `ReLU`, followed by a network with `k'` hidden layers and input dimension `m`.
  This directly mirrors the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ... ∘ ReLU ∘ T^(1)` from the paper, built up recursively from
  the first layer inward.
* `ReLUn n k` is taken to be the set of functions representable with **at most** `k` hidden
  layers (not *exactly* `k`). This is the standard convention (and the one under which
  `ReLUn n k` is monotone in `k`, so `Theorem 2`, an equality of sets at a single value of
  `k`, is even a sensible/true statement): every CPWL function needs *at most* the stated
  number of hidden layers, and conversely every function representable with at most that
  many hidden layers is CPWL.
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* cover of `ℝ^n` by
  polyhedra (each cut out by finitely many affine inequalities) on each of which `f` agrees
  with *some* affine function. This is a genuine piecewise-linearity condition (finite
  polyhedral subdivision + local affineness) and is not defined via representability by a
  ReLU network, nor via a max-of-affine-functions normal form.
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded using the real logarithm `Real.logb 3` and
  `Nat.ceil`, matching the paper's real-valued ceiling of a real logarithm.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias vector. -/
structure AffineTransform (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  bias : Fin b → ℝ

/-- The function computed by an affine transformation: `x ↦ A * x + bias`. -/
def AffineTransform.toFun {a b : ℕ} (T : AffineTransform a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.bias

/-- A ReLU network with input dimension `a` and `k` hidden layers, encoded recursively as
the alternating composition of affine transformations and componentwise ReLU, ending in a
single affine transformation to the scalar output. -/
inductive ReLUNet : ℕ → ℕ → Type
  | output {a : ℕ} (T : AffineTransform a 1) : ReLUNet a 0
  | layer {a m k : ℕ} (T : AffineTransform a m) (rest : ReLUNet m k) : ReLUNet a (k + 1)

/-- The real-valued function `ℝ^a → ℝ` computed by a ReLU network. -/
def ReLUNet.eval : {a k : ℕ} → ReLUNet a k → (Fin a → ℝ) → ℝ
  | _, _, ReLUNet.output T, x => T.toFun x 0
  | _, _, ReLUNet.layer T rest, x => rest.eval (reluVec (T.toFun x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, ∃ net : ReLUNet n k', f = net.eval }

/-- `f : ℝ^n → ℝ` is an affine function, given concretely by a linear functional (as a
dot product with a vector) plus a constant. -/
def IsAffineFun (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (c : ℝ), ∀ x, f x = c + ∑ j, a j * x j

/-- A polyhedron in `ℝ^n`: a set cut out by finitely many affine inequalities. -/
def IsPolyhedron (n : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (a : ι → Fin n → ℝ) (b : ι → ℝ),
    S = { x | ∀ i, ∑ j, a i j * x j ≤ b i }

/-- `CPWL n`: continuous functions `ℝ^n → ℝ` that are affine on each piece of some finite
polyhedral subdivision of `ℝ^n`. This is a genuine piecewise-linearity condition, not a
max-of-affine normal form and not "representable by a ReLU network". -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
      ∃ (ι : Type) (_ : Fintype ι) (P : ι → Set (Fin n → ℝ)),
        (∀ i, IsPolyhedron n (P i)) ∧
        (⋃ i, P i) = Set.univ ∧
        ∀ i, ∃ g, IsAffineFun n g ∧ Set.EqOn f g (P i) }

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from the paper, as a natural number. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent074

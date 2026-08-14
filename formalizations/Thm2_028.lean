import Mathlib

namespace Agent028

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):  for `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`.

## Modelling choices

* `ℝ^n` is encoded as `Fin n → ℝ`.
* Affine transformations `ℝ^a → ℝ^b` are given concretely by a weight matrix (as a
  function `Fin b → Fin a → ℝ`) and a bias vector `Fin b → ℝ`, acting as `x ↦ A x + c`.
* A ReLU network with `k` hidden layers, input dimension `n` and output dimension `m` is
  modelled by the recursively defined predicate `IsReLUNetFun`, mirroring the alternating
  composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper: `k = 0` hidden
  layers means a single affine map, and `k+1` hidden layers means an affine map into some
  hidden width `h`, followed by (componentwise) ReLU, followed by a network with `k` hidden
  layers from `h` to `m`.
* `ReLUn n k` is the set of scalar functions `ℝ^n → ℝ` representable by a network with
  *at most* `k` hidden layers (this is the reading under which Theorem 2, an equality of
  sets, is true: adding extra hidden layers never removes representability, so the classes
  `ReLU_{n,k}` are monotone increasing in `k`).
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of affine
  functions `ℝ^n → ℝ` such that every point of `ℝ^n` has a neighbourhood on which `f` agrees
  with one member of the family. This is a genuine piecewise-linearity condition (not a
  disguised "representable by a ReLU network" or "max of finitely many affine functions"
  definition).
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded using `Real.logb 3` and `Nat.ceil`, applied
  to the natural number `n - 1` (well-behaved since `n ≥ 3` gives `n - 1 ≥ 2`).
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given by a matrix `A` (as a function of indices)
and a bias vector `c`, acting as `x ↦ A x + c`. -/
structure Affine (a b : ℕ) where
  A : Fin b → Fin a → ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def Affine.apply {a b : ℕ} (T : Affine a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, T.A i j * x j) + T.c i

/-- `IsReLUNetFun k n m f` means the function `f : ℝ^n → ℝ^m` is *exactly* computed by a
ReLU network with `k` hidden layers, i.e. by an alternating composition of `k + 1` affine
transformations and `k` componentwise ReLU applications:
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`. -/
def IsReLUNetFun : (k n m : ℕ) → ((Fin n → ℝ) → (Fin m → ℝ)) → Prop
  | 0, n, m, f => ∃ T : Affine n m, f = T.apply
  | (k + 1), n, m, f =>
      ∃ (h : ℕ) (T : Affine n h) (g : (Fin h → ℝ) → (Fin m → ℝ)),
        IsReLUNetFun k h m g ∧ f = g ∘ reluVec ∘ T.apply

/-- `ReLUn n k` is the set of scalar functions `ℝ^n → ℝ` representable by a ReLU network
with *at most* `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, IsReLUNetFun k' n 1 (fun x _ => f x) }

/-- An affine (scalar-valued) function `ℝ^n → ℝ`, given by a weight vector and a bias. -/
structure AffineFunc (n : ℕ) where
  w : Fin n → ℝ
  b : ℝ

/-- Evaluation of a scalar affine function. -/
def AffineFunc.eval {n : ℕ} (T : AffineFunc n) (x : Fin n → ℝ) : ℝ :=
  (∑ i, T.w i * x i) + T.b

/-- `CPWL n` is the set of continuous, piecewise linear functions `ℝ^n → ℝ`: those that are
continuous and, near every point, agree with one of finitely many affine functions. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (ι : Type) (_ : Fintype ι) (T : ι → AffineFunc n),
          ∀ x : Fin n → ℝ, ∃ i : ι, Filter.Eventually (fun y => f y = (T i).eval y) (nhds x) }

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from the paper, for `n - 1 ≥ 2` (i.e. `n ≥ 3`). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n - 1 : ℕ) : ℝ)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent028

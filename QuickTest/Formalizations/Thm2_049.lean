import Mathlib

namespace Agent049

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We model `ℝ^n` concretely as `Fin n → ℝ`.

## Modelling choices (see summary at the end of the task)

* `relu` is `max 0 ·` on `ℝ`, and `reluVec` applies it componentwise.
* An affine map `ℝ^n → ℝ^m` is given concretely by a matrix `A : Matrix (Fin m) (Fin n) ℝ`
  and a bias vector `c : Fin m → ℝ`, evaluated as `x ↦ A.mulVec x + c`.
* A ReLU network with exactly `k` hidden layers computing `f : ℝ^n → ℝ` is defined
  *recursively* on `k`: with `0` hidden layers `f` must itself be affine (a single affine
  transformation, no ReLU applied at all); with `k+1` hidden layers, `f` factors as
  `g ∘ (reluVec ∘ (affine map ℝ^n → ℝ^m))` for some hidden width `m` and some function `g`
  computable with `k` hidden layers on input dimension `m`.
* `ReLUn n k` is taken to be the functions representable with **at most** `k` hidden
  layers (not *exactly* `k`). This is the reading under which Theorem 2, stated as a set
  *equality* `CPWL n = ReLUn n (depthBound n)`, can be true: `ReLUn n k` is monotone
  increasing in `k` (more layers can only help), and `CPWL n` is the union over all `k` of
  the exactly-`k` classes, so the "at most" reading is needed for the depth bound `K` to
  give a class that is closed under adding further (necessarily useless, since `CPWL n`
  is already everything representable) hidden layers.
* The depth bound `⌈log_3 (n-1)⌉ + 1` is defined literally via `Real.logb 3` and
  `Nat.ceil`, applied to the real number `(n - 1 : ℝ)`.
* `CPWL n` is defined as: continuous functions `f : ℝ^n → ℝ` admitting a *finite*
  polyhedral subdivision of `ℝ^n` (each piece a finite intersection of affine
  halfspaces, i.e. `{x | ∀ i, A.mulVec x i ≤ b i}`) covering all of `ℝ^n`, on each piece
  of which `f` agrees with *some* affine function. This is a genuine
  piecewise-affine-subdivision definition, not a "representable by a ReLU network" or
  "max of affine functions" definition.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (v : Fin m → ℝ) : Fin m → ℝ := fun i => relu (v i)

/-- A function `ℝ^n → ℝ` is affine if it is of the form `x ↦ ⟨a, x⟩ + b`. -/
def IsAffine (n : ℕ) (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), g = fun x => (∑ i, a i * x i) + b

/-- A subset of `ℝ^n` is a (closed) polyhedron if it is a finite intersection of affine
halfspaces `{x | A.mulVec x i ≤ b i}`. -/
def IsPolyhedron (n : ℕ) (P : Set (Fin n → ℝ)) : Prop :=
  ∃ (r : ℕ) (A : Matrix (Fin r) (Fin n) ℝ) (b : Fin r → ℝ),
    P = {x | ∀ i, A.mulVec x i ≤ b i}

/-- The space of continuous piecewise linear (CPWL) functions `ℝ^n → ℝ`: continuous
functions that admit a finite polyhedral subdivision of `ℝ^n` on each piece of which the
function agrees with some affine function. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (r : ℕ) (P : Fin r → Set (Fin n → ℝ)),
      (∀ i, IsPolyhedron n (P i)) ∧
      (⋃ i, P i) = Set.univ ∧
      ∀ i, ∃ g, IsAffine n g ∧ Set.EqOn f g (P i)}

/-- `ComputesK n k f` holds iff `f : ℝ^n → ℝ` is computed by some ReLU network with
*exactly* `k` hidden layers: `k = 0` means `f` is a single affine transformation
(depth 1, no ReLU applied); `k+1` means `f` is obtained by first applying an affine
transformation `ℝ^n → ℝ^m` followed by (componentwise) ReLU, then feeding the result into
a network with `k` hidden layers. -/
def ComputesK : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ (a : Fin n → ℝ) (b : ℝ), f = fun x => (∑ i, a i * x i) + b
  | n, k + 1, f =>
      ∃ (m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ) (g : (Fin m → ℝ) → ℝ),
        ComputesK m k g ∧ f = g ∘ (fun x => reluVec (A.mulVec x + c))

/-- `ReLUn n k`: the functions `ℝ^n → ℝ` representable by a ReLU network with *at most*
`k` hidden layers (see the module docstring for why "at most" rather than "exactly"). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ j ≤ k, ComputesK n j f}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so `n - 1 ≥ 2`). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL n = ReLUn n (⌈log_3 (n-1)⌉ + 1)`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent049

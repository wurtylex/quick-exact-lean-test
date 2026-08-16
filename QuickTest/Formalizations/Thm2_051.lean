import Mathlib

namespace Agent051

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

"Better Neural Network Expressivity: Subdividing the Simplex"
(Bakaev, Brunck, Hertrich, Stade, Yehudayoff)

**Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`.

## Modelling choices

* We encode `ℝ^n` as `Fin n → ℝ`.
* Affine maps `ℝ^a → ℝ^b` are encoded concretely as `x ↦ A.mulVec x + c` for a matrix `A`
  and a bias vector `c` (structure `AffMap`).
* A "ReLU network with `k` hidden layers computing `f`" is defined recursively on `k`
  (predicate `IsReLUComputable n k f`): with `0` hidden layers, `f` itself must be an
  affine map `ℝ^n → ℝ`; with `k+1` hidden layers, `f` factors as `g ∘ ReLU ∘ T` where `T`
  is an affine map `ℝ^n → ℝ^m`, `ReLU` is applied componentwise, and `g` is computable with
  `k` hidden layers. This is the literal unwinding of the alternating-composition
  definition in the paper.
* `ReLUn n k` is defined as the set of functions computable with **exactly** `k` hidden
  layers (the literal reading of "representable with `k` hidden layers"). Note that a
  ReLU network can always simulate the identity function on one extra hidden layer
  (e.g. `x ↦ ReLU(x) - ReLU(-x)`), so in fact `ReLUn n k ⊆ ReLUn n (k+1)` holds
  mathematically, meaning the "exactly `k`" and "at most `k`" readings coincide as sets;
  we simply pick the more literal "exactly `k`" phrasing.
* `CPWL n` is defined as the set of continuous functions `f : ℝ^n → ℝ` such that there is
  a *finite* family of affine functions with the property that `f` agrees with (at least)
  one member of the family on a neighborhood of every point -- i.e. `f` is genuinely
  locally affine, glued from finitely many affine pieces. This is a real
  piecewise-linearity condition (not "max of affine functions", and not "representable by
  some ReLU network").
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded via `Real.logb 3` and `Nat.ceil`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias vector. -/
structure AffMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- The function computed by an affine map: `x ↦ A x + c`. -/
def AffMap.eval {a b : ℕ} (T : AffMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `IsReLUComputable n k f` means that `f : ℝ^n → ℝ` is computed by a ReLU network with
`n` inputs and exactly `k` hidden layers, i.e. by an alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations with
componentwise ReLU applications, as in the paper's definition of a ReLU network. -/
def IsReLUComputable : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : AffMap n 1, ∀ x, f x = T.eval x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : AffMap n m) (g : (Fin m → ℝ) → ℝ),
        IsReLUComputable m k g ∧ ∀ x, f x = g (fun i => relu (T.eval x i))

/-- `ReLUn n k`: the set of functions `ℝ^n → ℝ` representable by a ReLU network with
exactly `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | IsReLUComputable n k f}

/-- An affine function `ℝ^n → ℝ`, given by a linear functional plus a constant. -/
def IsAffine (n : ℕ) (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x, g x = (∑ i, a i * x i) + b

/-- `CPWL n`: the set of continuous, genuinely piecewise-linear functions `ℝ^n → ℝ`, i.e.
continuous functions that agree, on a neighborhood of every point, with one member of a
single finite family of affine functions. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
        ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ),
          (∀ j, IsAffine n (g j)) ∧
          ∀ x : Fin n → ℝ, ∃ j, ∃ ε > 0, ∀ y, dist y x < ε → f y = g j y}

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so `n - 1 ≥ 2`). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n - 1 : ℕ) : ℝ)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent051

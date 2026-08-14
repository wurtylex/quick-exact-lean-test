import Mathlib

namespace Agent087

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We model `ℝ^n` as `Fin n → ℝ`.  An affine transformation `ℝ^a → ℝ^b` is modelled
concretely as `x ↦ A.mulVec x + b` for a matrix `A : Matrix (Fin b) (Fin a) ℝ` and a
translation vector `b : Fin b → ℝ`.

A ReLU network with `k` hidden layers computing `f : ℝ^n → ℝ` is modelled by the
predicate `Represents n k f`, defined by recursion on `k`:

* `k = 0` : `f` itself is an affine functional `ℝ^n → ℝ` (this is the case of a
  single affine transformation `T^(1)` with no hidden layers at all, matching the
  paper's convention that depth `k+1` with `k` hidden layers).
* `k+1`   : `f` is obtained by first applying an affine transformation
  `x ↦ A.mulVec x + b : ℝ^n → ℝ^m` (this is `T^(1)`), then applying `ReLU`
  componentwise, and then computing the rest of the network (with `k` hidden
  layers, i.e. `T^(2), ..., T^(k+2)` composed with the remaining `ReLU`s) on the
  result.

We read `ReLU_{n,k}` **literally** as "representable by a network with *exactly*
`k` hidden layers" (not "at most `k`"), matching the paper's phrasing "the subset
of `CPWL_n` representable with `k` hidden layers". Note that with this
definition `ReLUn n k` is in fact still monotone in `k` (one can always pad a
network with an extra hidden layer that implements the identity on the split
positive/negative parts of a vector), so this reading does not conflict with
`CPWL n = ReLUn n (⌈log_3 (n-1)⌉ + 1)` being the intended, literal equality of
sets from the paper.

`CPWL n` is defined honestly as: `f` is continuous, and there is a *finite*
family of affine functionals such that `f` locally agrees with (at least) one of
them in a neighbourhood of every point (a genuine finite polyhedral/local
piecewise-affine condition, not "representable by some ReLU network" and not a
max-of-affine normal form).
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector in `ℝ^m`. -/
def reluVec {m : ℕ} (v : Fin m → ℝ) : Fin m → ℝ := fun i => relu (v i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a
translation vector: `x ↦ A.mulVec x + b`. -/
def affineMap {a b : ℕ} (A : Matrix (Fin b) (Fin a) ℝ) (c : Fin b → ℝ) :
    (Fin a → ℝ) → (Fin b → ℝ) :=
  fun x => A.mulVec x + c

/-- A scalar-valued function `ℝ^n → ℝ` is affine if it has the form
`x ↦ ⟪c, x⟫ + b` for some vector `c` and scalar `b`. -/
def IsAffine (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (c : Fin n → ℝ) (b : ℝ), f = fun x => (∑ i, c i * x i) + b

/-- `Represents n k f` means `f : ℝ^n → ℝ` is computed by a ReLU network with
exactly `k` hidden layers, i.e. by an alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations
with componentwise `ReLU` in between. -/
def Represents (n : ℕ) : ℕ → ((Fin n → ℝ) → ℝ) → Prop
  | 0, f => IsAffine n f
  | k + 1, f =>
      ∃ (m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ)
        (g : (Fin m → ℝ) → ℝ),
        Represents m k g ∧ f = fun x => g (reluVec (affineMap A c x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU
network with exactly `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Represents n k f}

/-- `CPWL n` is the space of continuous, piecewise-linear functions `ℝ^n → ℝ`:
`f` is continuous and there is a finite family of affine functionals such that
`f` coincides with one of them on a neighbourhood of every point of `ℝ^n`. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
        ∃ (r : ℕ) (a : Fin r → (Fin n → ℝ) → ℝ),
          (∀ i, IsAffine n (a i)) ∧
          ∀ x : Fin n → ℝ, ∃ i, ∀ᶠ y in nhds x, f y = a i y}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from the paper, for `n ≥ 3` (so that
`n - 1 ≥ 2 > 0` and the real logarithm behaves as expected). -/
def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent087

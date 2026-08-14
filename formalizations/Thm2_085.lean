import Mathlib

namespace Agent085

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

  "Better Neural Network Expressivity: Subdividing the Simplex"
  (Bakaev, Brunck, Hertrich, Stade, Yehudayoff)

  Theorem 2. For n ≥ 3, CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}.

## Modelling choices

* Vectors `ℝ^m` are encoded as `Fin m → ℝ`.
* Affine maps `ℝ^a → ℝ^b` are given concretely by a matrix `A : Matrix (Fin b) (Fin a) ℝ`
  together with a bias vector `bias : Fin b → ℝ`, acting by `x ↦ A.mulVec x + bias`.
* A ReLU network with `k` hidden layers computing `f : ℝ^n → ℝ` is modelled *recursively*
  on `k`: with `0` hidden layers, `f` itself must be affine (a single affine transformation
  `T^(1)`, matching "depth 1"); with `k+1` hidden layers, `f` factors as
  `f x = g (relu (T x))` where `T : ℝ^n → ℝ^m` is affine, `relu` is applied componentwise,
  and `g : ℝ^m → ℝ` is computed by a network with `k` hidden layers. Unrolling this recursion
  reproduces exactly the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper, with `k+1` affine
  transformations and `k` applications of ReLU.
* `ReLUn n k` is the set of functions computed by *some* network with *exactly* `k` hidden
  layers. Note that (by the standard "ReLU(x) - ReLU(-x) = x" padding trick, not proved
  here) the family `ReLUn n k` is increasing in `k`, so "exactly k" and "at most k" describe
  the *same* set `ReLUn n k`; we use the "exactly k" reading since it is the more direct
  transcription of the recursive definition above.
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of affine
  functions `ℝ^n → ℝ` such that `f` locally (in a neighbourhood of every point) agrees with
  one member of the family. This is the "finite family of affine functions that `f` locally
  agrees with" option suggested by the spec; it is a genuine piecewise-linearity condition,
  not a max-of-affine normal form and not "representable by some ReLU network".
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined via `Real.logb 3` and `Nat.ceil` on the real
  number `(n : ℝ) - 1`.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias vector. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  bias : Fin b → ℝ

/-- The function `ℝ^a → ℝ^b` computed by an affine transformation. -/
def AffineMap.apply {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.bias

/-- `f : ℝ^n → ℝ` is an affine (scalar-valued) function, i.e. computed by a single affine
transformation `ℝ^n → ℝ^1` (identified with `ℝ`). This is the `k = 0` (no hidden layers,
depth 1) base case of a ReLU network. -/
def IsAffine1 (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ w : Fin n → ℝ, ∃ c : ℝ, ∀ x : Fin n → ℝ, f x = (∑ i, w i * x i) + c

/-- `Computes n k f` : the function `f : ℝ^n → ℝ` is computed by a ReLU network with `k`
hidden layers, i.e. by an alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations with
componentwise ReLU. Defined recursively on `k`: the base case `k = 0` is a bare affine
transformation (a single `T^(1)`, no ReLU applied), and the `k + 1` case peels off the first
affine transformation `T^(1) : ℝ^n → ℝ^m`, applies ReLU, and requires the remainder to be
computed by a network with `k` hidden layers on `ℝ^m`. -/
def Computes : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => IsAffine1 n f
  | n, k + 1, f =>
      ∃ (m : ℕ) (T : AffineMap n m) (g : (Fin m → ℝ) → ℝ),
        Computes m k g ∧ ∀ x : Fin n → ℝ, f x = g (reluVec (T.apply x))

/-- `ReLUn n k` : the set of functions `ℝ^n → ℝ` representable by a ReLU network with
(exactly, equivalently at most, by monotonicity in `k`) `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Computes n k f}

/-- `CPWL n` : the continuous piecewise-linear functions `ℝ^n → ℝ`, defined as those
functions that are continuous and locally agree, in a neighbourhood of every point, with
one member of some finite family of affine functions. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (w : Fin m → (Fin n → ℝ)) (c : Fin m → ℝ),
      ∀ x : Fin n → ℝ, ∃ i : Fin m,
        ∀ᶠ y in nhds x, f y = (∑ j, w i j * y j) + c i}

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so `n - 1 ≥ 2 > 0`). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent085

import Mathlib

namespace Agent015

/- ================= Vectors and ReLU ================= -/

/-- We encode `ℝ^n` concretely as `Fin n → ℝ`. -/
abbrev Vec (n : ℕ) := Fin n → ℝ

/-- The scalar ReLU function `x ↦ max 0 x`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on vectors. -/
def reluVec {n : ℕ} (x : Vec n) : Vec n := fun i => relu (x i)

/- ================= Affine transformations ================= -/

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix `A` and a
bias vector `c`, computing `x ↦ A * x + c`. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Vec b

/-- The function computed by an affine transformation. -/
def AffineMap.toFun {a b : ℕ} (T : AffineMap a b) (x : Vec a) : Vec b :=
  T.A.mulVec x + T.c

/- ================= ReLU networks ================= -/

/-- `Represents n k f` holds when `f : ℝ^n → ℝ` is computed by *some* ReLU network
with input dimension `n`, exactly `k` hidden layers, and output dimension `1`, i.e.
`f` arises as the alternating composition

  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`

of `k + 1` affine transformations with componentwise ReLU applied between
consecutive affine transformations (and nowhere else). We build this up by
recursion on `k`, peeling off the *first* affine + ReLU layer at each step:
a network with `k + 1` hidden layers from `ℝ^n` is a first affine map
`T^(1) : ℝ^n → ℝ^m` followed by a ReLU, followed by a network with `k` hidden
layers from `ℝ^m`. The base case `k = 0` is a single affine map `ℝ^n → ℝ`
with no ReLU applied at all, matching the definition with `k + 1 = 1` affine
transformation and no hidden layers. -/
def Represents : (n : ℕ) → (k : ℕ) → (Vec n → ℝ) → Prop
  | n, 0, f => ∃ T : AffineMap n 1, ∀ x : Vec n, f x = T.toFun x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : AffineMap n m) (g : Vec m → ℝ),
        Represents m k g ∧ ∀ x : Vec n, f x = g (reluVec (T.toFun x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network
with **exactly** `k` hidden layers (this is the reading under which Theorem 2, an
equality of sets, is true: with "at most `k`" the right-hand side would be an
increasing union over depths and the displayed equality would not pin down the
exact value `⌈log_3(n-1)⌉ + 1`). -/
def ReLUn (n k : ℕ) : Set (Vec n → ℝ) := { f | Represents n k f }

/- ================= CPWL functions ================= -/

/-- `f : ℝ^n → ℝ` is continuous piecewise linear (CPWL) if it is continuous and
there is a *finite* family of affine functions `g_1, …, g_m : ℝ^n → ℝ` such that
around every point `x`, `f` coincides with one of the `g_i` on a whole
neighbourhood of `x` (a finite polyhedral-type subdivision on whose pieces `f`
is affine, phrased via local agreement rather than a global max-of-affine
normal form). -/
def IsCPWL (n : ℕ) (f : Vec n → ℝ) : Prop :=
  Continuous f ∧
    ∃ (m : ℕ) (g : Fin m → AffineMap n 1),
      ∀ x : Vec n, ∃ i : Fin m, ∃ ε > 0,
        ∀ y : Vec n, dist y x < ε → f y = (g i).toFun y 0

/-- `CPWL n` is the set of continuous piecewise linear functions `ℝ^n → ℝ`. -/
def CPWL (n : ℕ) : Set (Vec n → ℝ) := { f | IsCPWL n f }

/- ================= Depth bound ================= -/

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from the theorem statement, using the
real logarithm `Real.logb 3` and `Nat.ceil` for the ceiling. -/
noncomputable def depthBound (n : ℕ) : ℕ := ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/- ================= Theorem 2 ================= -/

/-- **Theorem 2.** For `n ≥ 3`, `CPWL n = ReLUn n (⌈log_3(n-1)⌉ + 1)`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent015

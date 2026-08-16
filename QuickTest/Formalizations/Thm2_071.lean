import Mathlib

namespace Agent071

/-!
Formalization of Theorem 2 of arXiv:2505.14338
("Better Neural Network Expressivity: Subdividing the Simplex").

Encoding choices (see summary at the end of the task):
* `ℝ^n` is encoded as `Fin n → ℝ`.
* `ReLUn n k` is the set of functions computable by a ReLU network with **at most**
  `k` hidden layers (the standard convention in this literature, which makes
  `ReLUn n k` monotone in `k` and makes the statement of Theorem 2 meaningful).
* `CPWL n` is defined via continuity plus a genuine *local* piecewise-affine condition:
  there is a finite family of affine functions such that every point has a
  neighbourhood on which `f` agrees with one member of the family.
* The depth bound `⌈log_3 (n-1)⌉ + 1` is encoded with the real logarithm
  `Real.logb 3` and `Nat.ceil`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias
vector, as `x ↦ A x + c`. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def AffineMap.eval {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, T.A i j * x j) + T.c i

/-- `f : ℝ^n → ℝ` is computed by a ReLU network with **exactly** `k` hidden layers:
there is a sequence of layer widths `w 0 = n, w 1, ..., w k, w (k+1) = 1` and
`k + 1` affine transformations `T i : ℝ^{w i} → ℝ^{w (i+1)}`, `i = 0, ..., k`, such
that, starting from the input `x`, alternately applying `T i` and (except after the
final, output-producing, affine map) componentwise ReLU produces a sequence of
vectors `z 0, ..., z (k+1)` with `z 0 = x`, `z (k+1)` one-dimensional, and
`f x = z (k+1)`. This mirrors the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ... ∘ ReLU ∘ T^(1)` from the paper. -/
def ComputesWithHiddenLayers (n k : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (w : Fin (k + 2) → ℕ) (h0 : w 0 = n) (hL : w (Fin.last (k + 1)) = 1)
    (T : (i : Fin (k + 1)) → AffineMap (w i.castSucc) (w i.succ)),
    ∀ x : Fin n → ℝ, ∃ z : (i : Fin (k + 2)) → Fin (w i) → ℝ,
      z 0 = x ∘ Fin.cast h0 ∧
      (∀ i : Fin (k + 1), i.val < k →
        z i.succ = reluVec ((T i).eval (z i.castSucc))) ∧
      (∀ i : Fin (k + 1), i.val = k →
        z i.succ = (T i).eval (z i.castSucc)) ∧
      f x = z (Fin.last (k + 1)) (Fin.cast hL.symm 0)

/-- The set of functions `ℝ^n → ℝ` representable by a ReLU network with **at most**
`k` hidden layers. (Using "at most" rather than "exactly" is the standard reading
of `ReLU_{n,k}` in this literature; it is the reading that makes `ReLU_{n,k}`
monotone in `k`, as needed for the union over `k` to sensibly exhaust `CPWL_n`.) -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, ComputesWithHiddenLayers n k' f }

/-- An affine (i.e. degree ≤ 1 polynomial) function `ℝ^n → ℝ`. -/
def IsAffineFun {n : ℕ} (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x, g x = (∑ i, a i * x i) + b

/-- The space of continuous piecewise-linear (CPWL) functions `ℝ^n → ℝ`: continuous
functions that, near every point, coincide with one member of some fixed finite
family of affine functions. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ),
          (∀ j, IsAffineFun (g j)) ∧
          ∀ x : Fin n → ℝ, ∃ j : Fin m, ∃ U ∈ nhds x, Set.EqOn f (g j) U }

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so that
`(n : ℝ) - 1 ≥ 2`). -/
noncomputable def depthBound (n : ℕ) : ℕ := ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent071

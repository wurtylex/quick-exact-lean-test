import Mathlib

/-!
# Reference formalization of Theorem 2

*Better Neural Network Expressivity: Subdividing the Simplex*, arXiv:2505.14338,
Bakaev–Brunck–Hertrich–Stade–Yehudayoff.

> **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log₃(n−1)⌉+1}`.

This is the hub of the star comparison: every sampled formalization is compared
against *this* file rather than against its neighbour, so that two agents which
both match it are equal to each other for free.

Two deliberate choices, both matching the paper:

* `ReLUn n k` is **at most `k`** hidden layers.  (The "exactly `k`" reading
  denotes the same set — pad with `x = relu x − relu (−x)` — but only as a
  theorem, not definitionally.)
* `CPWL n` is the honest piecewise-linearity condition: continuous, plus a
  finite polyhedral cover of `ℝⁿ` on each piece of which `f` agrees with an
  affine function.  It is *not* phrased as "representable by a ReLU network"
  (which would make Theorem 2 a tautology) and not as a max-of-affine normal
  form (which would assume the hard direction).
-/

namespace Ref

/-- The ReLU activation on `ℝ`. -/
noncomputable def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝⁿ`, encoded as `Fin n → ℝ`. -/
noncomputable def reluVec {n : ℕ} (v : Fin n → ℝ) : Fin n → ℝ := fun i => relu (v i)

/-- An affine map `ℝ^a → ℝ^b`, as a matrix together with a translation. -/
structure Aff (a b : ℕ) where
  M : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- `x ↦ M x + c`. -/
def Aff.eval {a b : ℕ} (T : Aff a b) (x : Fin a → ℝ) : Fin b → ℝ := T.M.mulVec x + T.c

/-- `ComputedBy n k f` : `f : ℝⁿ → ℝ` is computed by a ReLU network with
**exactly** `k` hidden layers, i.e. the alternating composition
`T⁽ᵏ⁺¹⁾ ∘ relu ∘ T⁽ᵏ⁾ ∘ ⋯ ∘ relu ∘ T⁽¹⁾` of `k+1` affine maps. -/
def ComputedBy : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0,     f => ∃ T : Aff n 1, ∀ x, f x = T.eval x 0
  | n, (k+1), f => ∃ (m : ℕ) (T : Aff n m) (g : (Fin m → ℝ) → ℝ),
      ComputedBy m k g ∧ ∀ x, f x = g (reluVec (T.eval x))

/-- `ReLU_{n,k}` : functions `ℝⁿ → ℝ` computed by a ReLU network with **at most**
`k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) := {f | ∃ j ≤ k, ComputedBy n j f}

/-- An affine functional `ℝⁿ → ℝ`. -/
def IsAffine {n : ℕ} (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x, g x = (∑ i, a i * x i) + b

/-- A closed affine halfspace of `ℝⁿ`. -/
def IsHalfspace (n : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), S = {x | (∑ i, a i * x i) ≤ b}

/-- A polyhedron of `ℝⁿ` : a finite intersection of halfspaces.  Note `m = 0`
gives `⋂ (i : Fin 0), _ = univ`, so `ℝⁿ` itself is a polyhedron. -/
def IsPolyhedron (n : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (H : Fin m → Set (Fin n → ℝ)), (∀ i, IsHalfspace n (H i)) ∧ S = ⋂ i, H i

/-- `IsCPWL n f` : `f` is continuous and there is a finite polyhedral cover of
`ℝⁿ` on each piece of which `f` agrees with an affine functional. -/
def IsCPWL (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  Continuous f ∧
    ∃ (m : ℕ) (P : Fin m → Set (Fin n → ℝ)) (g : Fin m → ((Fin n → ℝ) → ℝ)),
      (∀ i, IsPolyhedron n (P i)) ∧ (∀ i, IsAffine (g i)) ∧
        (⋃ i, P i) = Set.univ ∧ ∀ i, ∀ x ∈ P i, f x = g i x

/-- `CPWL_n` : the continuous piecewise-linear functions `ℝⁿ → ℝ`. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) := {f | IsCPWL n f}

/-- The depth bound `⌈log₃(n−1)⌉ + 1`. -/
noncomputable def depthBound (n : ℕ) : ℕ := ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log₃(n−1)⌉+1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) : CPWL n = ReLUn n (depthBound n) := sorry

end Ref

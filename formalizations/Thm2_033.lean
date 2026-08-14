import Mathlib

namespace Agent033

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We encode `ℝ^n` concretely as `Fin n → ℝ`.

Theorem 2 states: for `n ≥ 3`,
`CPWL_n = ReLU_{n, ⌈log_3 (n-1)⌉ + 1}`.

## Modelling choices (see summary at the end of the task)

* Vectors: `Fin n → ℝ`.
* Affine maps `ℝ^a → ℝ^b`: an explicit structure `x ↦ A * x + c` with `A` a matrix
  and `c` a vector.
* A ReLU network with `k` hidden layers computing `f : (Fin n → ℝ) → ℝ` is defined
  recursively on `k`: for `k = 0` it is a single affine map `n → 1`; for `k + 1` it is
  an affine map `n → m` followed by (componentwise) ReLU, followed by a `k`-hidden-layer
  network from `m` to the output. This exactly mirrors the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper.
* `ReLUn n k` is taken to be functions representable with *at most* `k` hidden layers
  (a union over `j ≤ k` of the "exactly `j`" sets). This is the reading under which
  `ReLUn n k` is monotone in `k` (extra layers can only help, e.g. by simulating the
  identity via `x = ReLU(x) - ReLU(-x)` on doubled width) and hence the equality with
  `CPWL_n` in Theorem 2 is the natural/true statement.
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of affine
  functions such that every point of `ℝ^n` has an open neighborhood on which `f`
  coincides with (at least) one member of the family. This is a genuine
  piecewise-linearity condition (not defined via ReLU-representability, and not a
  max-of-affine normal form).
* The depth bound `⌈log_3 (n-1)⌉ + 1` is defined via `Real.logb 3` and `Nat.ceil`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of ReLU to a vector. -/
def reluVec {k : ℕ} (x : Fin k → ℝ) : Fin k → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given explicitly by a matrix and a bias
vector: `x ↦ A * x + c`. -/
structure AffineMapRn (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine map. -/
def AffineMapRn.eval {a b : ℕ} (T : AffineMapRn a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `ComputesReLU n k f` means `f : ℝ^n → ℝ` is computed by a ReLU network with
exactly `k` hidden layers, i.e. `f = T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`
for some affine transformations `T^(1), …, T^(k+1)` of matching dimensions. -/
def ComputesReLU : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : AffineMapRn n 1, ∀ x, f x = T.eval x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : AffineMapRn n m) (g : (Fin m → ℝ) → ℝ),
        ComputesReLU m k g ∧ ∀ x, f x = g (reluVec (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network
with *at most* `k` hidden layers (see the discussion above for why "at most" is the
right reading). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ j ≤ k, ComputesReLU n j f }

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: `f` is
continuous, and there is a finite family of affine functions such that every point
has an open neighborhood on which `f` agrees with one member of the family. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (a : Fin m → (Fin n → ℝ)) (b : Fin m → ℝ),
          ∀ x : Fin n → ℝ, ∃ i : Fin m, ∃ U : Set (Fin n → ℝ),
            IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, f y = (∑ j, a i j * y j) + b i }

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from the theorem statement. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3 (n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent033

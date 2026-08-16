import Mathlib

namespace Agent057

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):  for `n ≥ 3`,  `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`.

Modelling choices (see summary at the end of the task too):
* Vectors `ℝ^n` are modelled as `Fin n → ℝ`.
* Affine maps `ℝ^a → ℝ^b` are modelled concretely and explicitly as `x ↦ A * x + c` via a
  custom structure `AffMap` (a matrix `A` and bias vector `c`), to avoid any risk of
  silently picking up Mathlib's `Continuous`/`Convex`-heavy general affine map API for
  something that is meant to be an elementary, concrete object.
* "Computed by a ReLU network with `k` hidden layers" is defined as an inductive predicate
  `ComputesReLU n m k f`, built by induction on `k`: `k = 0` is a bare affine map
  (`depth = 1`, i.e. `T^{(1)}`, no hidden layer), and the `k+1` case prepends an affine map
  followed by a componentwise ReLU in front of a `k`-hidden-layer network. This directly
  encodes the alternating composition
  `T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}` from the paper.
* `ReLUn n k` is taken to mean representable with **at most** `k` hidden layers (not
  exactly `k`): this is the reading under which the classes are increasing in `k` and under
  which Theorem 2's single bound `⌈log_3(n-1)⌉ + 1` can equal all of `CPWL_n` (rather than
  merely some strict subset that jumps around non-monotonically with `k`).
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of polyhedral
  pieces (each cut out by finitely many affine inequalities) covering `ℝ^n`, on each of
  which `f` agrees with some affine function. This is a genuine piecewise-linearity
  condition (finite polyhedral subdivision + affine on each piece), not a "representable by
  some ReLU network" nor a "max of affine functions" definition.
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined via the real logarithm `Real.logb 3` and
  `Nat.ceil` (`⌈·⌉₊`), matching the paper's `⌈log_3(n−1)⌉ + 1` literally.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^n`. -/
def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix `A` and a bias
vector `c`, computing `x ↦ A * x + c`. -/
structure AffMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an `AffMap`. -/
def AffMap.eval {a b : ℕ} (T : AffMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `ComputesReLU n m k f` means: the function `f : ℝ^n → ℝ^m` is computed by a ReLU
network with `k` hidden layers, i.e. `f` is the alternating composition
`T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}` of `k + 1` affine transformations
`T^{(1)}, …, T^{(k+1)}` with componentwise ReLU applied after each of the first `k` of
them. The `base` case (`k = 0`) is a single affine transformation (depth `1`, no hidden
layer); the `step` case peels off the first affine transformation and ReLU, leaving a
network with one fewer hidden layer. -/
inductive ComputesReLU : (n m k : ℕ) → ((Fin n → ℝ) → (Fin m → ℝ)) → Prop
  | base {n m : ℕ} (T : AffMap n m) : ComputesReLU n m 0 T.eval
  | step {n p m k : ℕ} (T : AffMap n p) (g : (Fin p → ℝ) → (Fin m → ℝ))
      (hg : ComputesReLU p m k g) :
      ComputesReLU n m (k + 1) (g ∘ reluVec ∘ T.eval)

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with at
most `k` hidden layers (output dimension `m = 1`). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, ComputesReLU n 1 k' (fun x _ => f x)}

/-- A polyhedron in `ℝ^n`: the intersection of finitely many closed affine half-spaces
`{x | a i x ≤ b i}`. -/
def IsPolyhedron (n : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (a : ι → (Fin n → ℝ) →ₗ[ℝ] ℝ) (b : ι → ℝ),
    S = ⋂ i, {x | a i x ≤ b i}

/-- `f : ℝ^n → ℝ` is continuous and piecewise linear: it is continuous, and there is a
finite polyhedral subdivision of `ℝ^n` (a finite family of polyhedra covering `ℝ^n`) on
each piece of which `f` agrees with some affine function. -/
def IsCPWL (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  Continuous f ∧
    ∃ (ι : Type) (_ : Fintype ι) (S : ι → Set (Fin n → ℝ)) (A : ι → (Fin n → ℝ) →ᵃ[ℝ] ℝ),
      (∀ i, IsPolyhedron n (S i)) ∧
        (⋃ i, S i) = Set.univ ∧
        (∀ i, ∀ x ∈ S i, f x = A i x)

/-- The set of continuous piecewise linear functions `ℝ^n → ℝ`. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | IsCPWL n f}

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from Theorem 2. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent057

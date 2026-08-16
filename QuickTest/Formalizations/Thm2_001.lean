import Mathlib

namespace Agent001

/-- The ReLU activation function on `ℝ`. -/
noncomputable def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on a vector in `ℝ^n`, encoded as `Fin n → ℝ`. -/
noncomputable def reluVec {n : ℕ} (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => relu (v i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix `A` and a
translation vector `c`, acting as `x ↦ A * x + c`. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def AffineMap.eval {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `IsReLUNet n k f` says that `f : ℝ^n → ℝ` is *computed* by a ReLU network with `n`
inputs and `k` hidden layers, i.e. `f` arises as the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations with
componentwise ReLU in between (so the network has depth `k + 1` and `k` hidden layers,
matching the paper's convention). We recurse on the *first* layer: with `0` hidden
layers the network is a single affine transformation `ℝ^n → ℝ^1`, i.e. `f` itself is an
affine functional on `ℝ^n`; with `k + 1` hidden layers, `f` is obtained by first
applying an affine map `T^(1) : ℝ^n → ℝ^m` to some hidden width `m`, then componentwise
ReLU, and then feeding the result into a network with `k` hidden layers computing
`ℝ^m → ℝ`. -/
def IsReLUNet : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x, f x = (∑ i, a i * x i) + b
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : AffineMap n m) (g : (Fin m → ℝ) → ℝ),
        IsReLUNet m k g ∧ ∀ x, f x = g (reluVec (T.eval x))

/-- `ReLUn n k`: the set of functions `ℝ^n → ℝ` representable by a ReLU network with
exactly `k` hidden layers, i.e. `ReLU_{n,k}` from the paper. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) := {f | IsReLUNet n k f}

/-- A closed affine halfspace of `ℝ^n`. -/
def IsHalfspace (n : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), S = {x | (∑ i, a i * x i) ≤ b}

/-- A (closed, convex) polyhedron of `ℝ^n`: a finite intersection of halfspaces. -/
def IsPolyhedron (n : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (H : Fin m → Set (Fin n → ℝ)), (∀ i, IsHalfspace n (H i)) ∧ S = ⋂ i, H i

/-- `IsCPWL n f`: `f : ℝ^n → ℝ` is continuous and piecewise linear, meaning there is a
finite polyhedral subdivision of `ℝ^n` (a finite family of polyhedra covering `ℝ^n`) on
each piece of which `f` agrees with some affine function. This is a genuine
piecewise-linearity condition, independent of any notion of ReLU-network
representability and not phrased as a max-of-affine normal form. -/
def IsCPWL (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  Continuous f ∧
    ∃ (m : ℕ) (P : Fin m → Set (Fin n → ℝ)) (a : Fin m → (Fin n → ℝ)) (b : Fin m → ℝ),
      (∀ i, IsPolyhedron n (P i)) ∧ (⋃ i, P i) = Set.univ ∧
        ∀ i, ∀ x ∈ P i, f x = (∑ j, a i j * x j) + b i

/-- `CPWL n`: the space of continuous piecewise-linear functions `ℝ^n → ℝ`. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) := {f | IsCPWL n f}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2. Here `n - 1` (with `n ≥ 3`,
so `n - 1 ≥ 2` as a natural number) is cast to `ℝ` before taking the base-3 real
logarithm and its ceiling. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n - 1 : ℕ) : ℝ)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent001

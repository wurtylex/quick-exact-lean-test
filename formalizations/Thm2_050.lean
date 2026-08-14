import Mathlib

namespace Agent050

/-!
Formalization of Theorem 2 of arXiv:2505.14338
("Better Neural Network Expressivity: Subdividing the Simplex").

Vector encoding: `ℝ^n` is modelled as `Fin n → ℝ`.

`ReLUn n k` is taken to mean "representable by a ReLU network with **at most** `k`
hidden layers" (the standard reading in this literature: adding useless extra
layers, e.g. via an identity affine map, never hurts, so the classes are
monotone increasing in `k`; this is also the reading under which Theorem 1's
consequence "every CPWL function on `R^n` can be represented with
`⌈log_3(n-1)⌉ + 1` hidden layers" and Theorem 2's equality both make sense).
-/

/-- ReLU on the reals. -/
noncomputable def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
noncomputable def reluVec {m : ℕ} (v : Fin m → ℝ) : Fin m → ℝ :=
  fun i => relu (v i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias
vector: `x ↦ A x + c`. -/
structure AffMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- The function `ℝ^a → ℝ^b` computed by an affine transformation. -/
noncomputable def AffMap.eval {a b : ℕ} (T : AffMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, T.A i j * x j) + T.c i

/-- A ReLU network with input dimension `n` and `k` hidden layers, encoded
recursively: a network with `0` hidden layers is a single affine output map
`ℝ^n → ℝ`; a network with `k+1` hidden layers is an affine map `ℝ^n → ℝ^m`
followed by componentwise ReLU, followed by a network with `k` hidden layers
on `ℝ^m`. This directly mirrors the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ... ∘ ReLU ∘ T^(1)` from the paper. -/
inductive ReLUNet : ℕ → ℕ → Type
  | last {n : ℕ} (T : AffMap n 1) : ReLUNet n 0
  | cons {n m k : ℕ} (T : AffMap n m) (rest : ReLUNet m k) : ReLUNet n (k + 1)

/-- The function `ℝ^n → ℝ` computed by a ReLU network. -/
noncomputable def ReLUNet.eval : {n k : ℕ} → ReLUNet n k → (Fin n → ℝ) → ℝ
  | _, _, ReLUNet.last T, x => T.eval x 0
  | _, _, ReLUNet.cons T rest, x => rest.eval (reluVec (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU
network with **at most** `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, ∃ net : ReLUNet n k', f = net.eval }

/-- A function `ℝ^n → ℝ` is affine iff it has the form `x ↦ a · x + c`. -/
def IsAffineFun {n : ℕ} (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (c : ℝ), ∀ x, g x = (∑ j, a j * x j) + c

/-- A set `P ⊆ ℝ^n` is a (closed) polyhedron iff it is a finite intersection of
closed affine half-spaces `{x | a · x ≤ b}`. -/
def IsPolyhedron {n : ℕ} (P : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ),
    P = { x | ∀ i, (∑ j, A i j * x j) ≤ b i }

/-- `CPWL n`: the continuous piecewise-linear functions `ℝ^n → ℝ`.
A function `f` is CPWL iff it is continuous and there is a *finite* polyhedral
subdivision of `ℝ^n` (finitely many polyhedral pieces covering `ℝ^n`) on each
piece of which `f` coincides with some affine function. This is a genuine
piecewise-linearity condition: it is neither "representable by some ReLU
network" nor a max-of-affine normal form. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (P : Fin m → Set (Fin n → ℝ)) (g : Fin m → (Fin n → ℝ) → ℝ),
          (∀ i, IsPolyhedron (P i)) ∧
          (∀ i, IsAffineFun (g i)) ∧
          (⋃ i, P i) = Set.univ ∧
          (∀ i, ∀ x ∈ P i, f x = g i x) }

/-- The depth bound `⌈log_3(n-1)⌉ + 1` hidden layers from Theorem 2, using the
real logarithm base 3 and the natural-number ceiling. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, the CPWL functions on `ℝ^n` coincide exactly
with the functions representable by ReLU networks with (at most)
`⌈log_3(n-1)⌉ + 1` hidden layers. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent050

import Mathlib

namespace Agent083

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We encode `ℝ^n` concretely as `Fin n → ℝ`.

## Modelling choices (see summary at the end of the task for more detail)

* Vectors: `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is given by a matrix `A : Matrix (Fin b) (Fin a) ℝ`
  together with a bias vector `c : Fin b → ℝ`, applied as `x ↦ A.mulVec x + c`.
* A ReLU network with `k` hidden layers and input dimension `n` is modelled by the inductive
  family `ReLUNet n k`, which is literally the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper: the base case `output` is a single
  affine map `ℝ^n → ℝ^1` (0 hidden layers), and `layer` prepends one affine map followed by a
  `ReLU`, increasing the hidden-layer count by one. The hidden widths `n_1, …, n_k` are existentially
  quantified (arbitrary natural numbers), matching the informal definition.
* `ReLUn n k` is the set of functions representable with **at most** `k` hidden layers (i.e. by
  some `ReLUNet n j` with `j ≤ k`). This is the reading that makes Theorem 2 a faithful
  "sufficiency + necessity of depth `⌈log_3(n-1)⌉+1`" statement: `ReLUn n k` is monotone in `k`
  by construction, matching the standard convention in the depth-separation literature (a
  network realizable with fewer hidden layers is certainly realizable with at most `k` for any
  larger `k`, since the definition itself quantifies over `j ≤ k`).
* `CPWL n` requires continuity together with a genuine finite polyhedral-type subdivision: a
  finite family of convex, closed pieces covering `ℝ^n` on each of which `f` agrees with some
  affine function.
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined using `Real.logb 3` and `Nat.ceil` (`⌈·⌉₊`)
  applied to the real number `(n : ℝ) - 1`.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias vector. -/
structure AffineTransform (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- The function `ℝ^a → ℝ^b` computed by an affine transformation: `x ↦ A * x + c`. -/
def AffineTransform.apply {a b : ℕ} (T : AffineTransform a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- A ReLU network with input dimension `n` and exactly `k` hidden layers, modelled as the
literal alternating composition `T^(k+1) ∘ ReLU ∘ ⋯ ∘ ReLU ∘ T^(1)`.
The hidden widths are existentially present as the (arbitrary) indices `m` occurring in `layer`. -/
inductive ReLUNet : ℕ → ℕ → Type where
  /-- `k = 0` hidden layers: a single affine map `ℝ^n → ℝ^1` (no ReLU applied). -/
  | output {n : ℕ} (T : AffineTransform n 1) : ReLUNet n 0
  /-- Prepend one affine map `ℝ^n → ℝ^m` followed by a ReLU, then continue with a network
  that has `k` further hidden layers and input dimension `m`. -/
  | layer {n m k : ℕ} (T : AffineTransform n m) (rest : ReLUNet m k) : ReLUNet n (k + 1)

/-- The function `ℝ^n → ℝ` computed by a ReLU network, i.e.
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`. -/
def ReLUNet.eval {n k : ℕ} (net : ReLUNet n k) (x : Fin n → ℝ) : ℝ :=
  match net with
  | ReLUNet.output T => T.apply x 0
  | ReLUNet.layer T rest => rest.eval (reluVec (T.apply x))

/-- A function is representable with *exactly* `k` hidden layers if it is computed by some
`ReLUNet n k`. -/
def IsRepresentableExact (n k : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ net : ReLUNet n k, ∀ x, f x = net.eval x

/-- `ReLUn n k`: the set of functions `ℝ^n → ℝ` representable with **at most** `k` hidden
layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ j ≤ k, IsRepresentableExact n j f}

/-- A function `ℝ^n → ℝ` is affine if it has the form `x ↦ ⟨a, x⟩ + b`. -/
def IsAffineMap (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x, f x = (∑ i, a i * x i) + b

/-- `CPWL n`: continuous functions `ℝ^n → ℝ` that admit a finite subdivision of `ℝ^n` into
convex, closed pieces covering all of `ℝ^n`, on each of which `f` agrees with an affine
function. This is a genuine piecewise-linearity condition (a finite polyhedral-type
subdivision), not a "representable by some ReLU network" or "max of affine functions"
definition. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (pieces : Fin m → Set (Fin n → ℝ)) (affines : Fin m → ((Fin n → ℝ) → ℝ)),
      (∀ i, IsAffineMap n (affines i)) ∧
      (∀ i, Convex ℝ (pieces i)) ∧
      (∀ i, IsClosed (pieces i)) ∧
      (⋃ i, pieces i) = Set.univ ∧
      (∀ i, ∀ x ∈ pieces i, f x = affines i x)}

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so `n - 1 ≥ 2` as a real
number). -/
def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL n = ReLUn n (⌈log_3(n-1)⌉ + 1)`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent083

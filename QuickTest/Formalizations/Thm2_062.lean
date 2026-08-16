import Mathlib

namespace Agent062

/-
  Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network
  Expressivity: Subdividing the Simplex"):

    For n ≥ 3,  CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}.

  Modelling choices (see summary at the bottom / final chat message):
  * ℝ^n is encoded as `Fin n → ℝ`.
  * Affine maps `ℝ^a → ℝ^b` are encoded concretely as `x ↦ A * x + bias`
    for a matrix `A` and vector `bias`.
  * A ReLU network with exactly `k` hidden layers computing `f` is defined
    by structural recursion on `k` via the inductive predicate `NetComputes`,
    mirroring the alternating composition
      T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)
    from the paper. The hidden widths `n_1, …, n_k` are existentially
    quantified (they are unconstrained parameters of the network).
  * `ReLUn n k` is taken to be the set of functions representable with
    *at most* `k` hidden layers. This is the reading under which Theorem 2
    is a meaningful (non-monotone-trivial) equality: `ReLUn n k` is then
    manifestly monotone in `k`, matching the standard convention in the
    depth-separation literature (extra layers can always simulate fewer,
    e.g. by using an affine layer that acts as the identity).
  * `CPWL n` is defined genuinely: `f` is continuous, and there is a finite
    polyhedral subdivision of `ℝ^n` (each piece cut out by finitely many
    linear inequalities) together with a finite family of affine functions,
    one per piece, that `f` agrees with on that piece.
  * The depth bound `⌈log_3(n-1)⌉ + 1` is encoded literally using
    `Real.logb 3` and `Nat.ceil`.
-/

/-- The scalar ReLU function. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ :=
  fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias vector. -/
structure Affine (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  bias : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def Affine.eval {a b : ℕ} (T : Affine a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.bias

/--
  `NetComputes n k f` means: `f : ℝ^n → ℝ` is computed by a ReLU network with
  exactly `k` hidden layers, i.e. by an alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine
  transformations with pointwise ReLU in between. The base case `k = 0` is a
  single affine transformation `ℝ^n → ℝ` (no hidden layer, no ReLU). The
  hidden-layer widths are implicit existential parameters of the network.
-/
inductive NetComputes : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | zero {n : ℕ} (T : Affine n 1) :
      NetComputes n 0 (fun x => T.eval x 0)
  | succ {n m k : ℕ} (T : Affine n m) (g : (Fin m → ℝ) → ℝ)
      (hg : NetComputes m k g) :
      NetComputes n (k + 1) (fun x => g (reluVec (T.eval x)))

/--
  `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU
  network with *at most* `k` hidden layers (see the discussion above for why
  this, rather than "exactly `k`", is the reading used here).
-/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, NetComputes n k' f }

/-- An affine (real-valued) function `ℝ^n → ℝ`, given via its coefficients and constant term. -/
def IsAffineFun {n : ℕ} (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (c : ℝ), ∀ x, g x = (∑ i, a i * x i) + c

/--
  A polyhedron in `ℝ^n`: the solution set of finitely many linear
  inequalities `⟨L j, x⟩ ≤ b j`.
-/
def IsPolyhedron {n : ℕ} (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (L : Fin m → (Fin n → ℝ)) (b : Fin m → ℝ),
    S = { x | ∀ j, (∑ i, L j i * x i) ≤ b j }

/--
  `CPWL n`: the continuous, piecewise-linear functions `ℝ^n → ℝ`. A function
  `f` belongs to this set iff it is continuous and there is a finite
  polyhedral subdivision of `ℝ^n` (finitely many polyhedral pieces covering
  all of `ℝ^n`) together with a matching finite family of affine functions,
  one per piece, such that `f` agrees with the corresponding affine function
  on each piece.
-/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (S : Fin m → Set (Fin n → ℝ)) (g : Fin m → (Fin n → ℝ) → ℝ),
          (∀ i, IsPolyhedron (S i)) ∧
          (∀ i, IsAffineFun (g i)) ∧
          (⋃ i, S i) = Set.univ ∧
          (∀ i x, x ∈ S i → f x = g i x) }

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from Theorem 2, for `n ≥ 3`. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent062

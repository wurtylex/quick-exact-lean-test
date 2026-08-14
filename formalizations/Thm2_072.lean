import Mathlib

namespace Agent072

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

  "Better Neural Network Expressivity: Subdividing the Simplex"
  (Bakaev, Brunck, Hertrich, Stade, Yehudayoff)

Theorem 2. For n ≥ 3, we have CPWL_n = ReLU_{n, ⌈log_3(n−1)⌉ + 1}.

## Modelling choices

* Vectors `ℝ^n` are encoded as `Fin n → ℝ` (with its Pi topology / module structure).
* An affine transformation `ℝ^a → ℝ^b` is modelled concretely as a pair `(A, c)` of a
  matrix `A : Matrix (Fin b) (Fin a) ℝ` and a bias vector `c : Fin b → ℝ`, evaluated as
  `x ↦ A.mulVec x + c`.
* "Computed by a ReLU network with `k` hidden layers" is defined by structural recursion
  on `k`, directly mirroring the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper: a 0-hidden-layer network is
  a single affine map to `ℝ^1`; a `(k+1)`-hidden-layer network first applies an affine map
  `T : ℝ^n → ℝ^m`, then componentwise ReLU, then feeds the result into a `k`-hidden-layer
  network.
* `ReLUn n k` is taken to be the set of functions representable with **at most** `k`
  hidden layers (`∃ k' ≤ k, …`), not *exactly* `k`. This is the reading under which
  Theorem 2 is true: the right-hand side must be monotone in `k` (any function computable
  with fewer layers is in particular computable with more, e.g. by the standard
  `x = ReLU(x) − ReLU(−x)` identity-padding trick), and the "exactly `n` hidden layers"
  reading would generally fail to contain all of `CPWL_n` at the boundary value `n`, or
  would fail to be well-behaved as `n` increases, without extra padding lemmas.
* `CPWL n` is defined genuinely: `f` is continuous **and** there is a finite polyhedral
  subdivision of `ℝ^n` (each piece cut out by finitely many affine inequalities) together
  with an affine functional per piece that `f` agrees with on that piece. This is a real
  piecewise-linearity condition, independent of the ReLU-network machinery.
* The depth bound `⌈log_3(n−1)⌉ + 1` is defined using the real logarithm `Real.logb 3`
  composed with `Nat.ceil` (written `⌈·⌉₊`), exactly matching the informal statement,
  rather than via `Nat.clog`.
-/

/-- The scalar ReLU function. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^n`. -/
def reluV {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias
vector: `x ↦ A * x + c`. -/
structure AffineT (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def AffineT.eval {a b : ℕ} (T : AffineT a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `IsReLUNet n k f` means `f : ℝ^n → ℝ` is computed by a ReLU network with `k` hidden
layers, i.e. by an alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`
of `k + 1` affine transformations with `k` interleaved componentwise ReLUs. Defined by
recursion on `k`, peeling off the first affine map / ReLU pair from the input side. -/
def IsReLUNet : (n : ℕ) → (k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : AffineT n 1, f = fun x => T.eval x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : AffineT n m) (g : (Fin m → ℝ) → ℝ),
        IsReLUNet m k g ∧ f = fun x => g (reluV (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, IsReLUNet n k' f }

/-- A subset of `ℝ^n` is a (closed) polyhedron if it is a finite intersection of
halfspaces `{x | a_i · x ≤ b_i}`. -/
def isPolyhedron (n : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (a : Fin m → Fin n → ℝ) (b : Fin m → ℝ),
    S = {x | ∀ i, (∑ j, a i j * x j) ≤ b i}

/-- An affine functional `ℝ^n → ℝ`, i.e. `x ↦ c · x + d`. -/
def isAffineFunctional (n : ℕ) (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (c : Fin n → ℝ) (d : ℝ), g = fun x => (∑ j, c j * x j) + d

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: continuous
functions admitting a finite polyhedral subdivision of `ℝ^n` on each piece of which the
function agrees with some affine functional. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
      ∃ (m : ℕ) (P : Fin m → Set (Fin n → ℝ)) (g : Fin m → (Fin n → ℝ) → ℝ),
        (∀ i, isPolyhedron n (P i)) ∧
        (∀ i, isAffineFunctional n (g i)) ∧
        (⋃ i, P i) = Set.univ ∧
        (∀ i, ∀ x ∈ P i, f x = g i x) }

/-- The depth bound `⌈log_3(n − 1)⌉ + 1` from the paper. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n−1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent072

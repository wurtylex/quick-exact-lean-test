import Mathlib

namespace Agent081

/-!
# Theorem 2 of arXiv:2505.14338 (Bakaev–Brunck–Hertrich–Stade–Yehudayoff)

We formalize the *statement* of Theorem 2: for `n ≥ 3`,
`CPWL n = ReLUn n (⌈log_3 (n - 1)⌉ + 1)`.

## Modelling choices

* Vectors in `ℝ^n` are encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is encoded concretely as a pair `(A, c)` with
  `A : Matrix (Fin b) (Fin a) ℝ` and `c : Fin b → ℝ`, acting by `x ↦ A.mulVec x + c`.
* A ReLU network with `k` hidden layers computing `f : (Fin n → ℝ) → ℝ` is encoded
  *recursively* on `k`: with `0` hidden layers, `f` itself must be an affine map
  `ℝ^n → ℝ`; with `k + 1` hidden layers, there is some hidden width `m`, an affine map
  `T : ℝ^n → ℝ^m`, and a function `g : ℝ^m → ℝ` computed by a network with `k` hidden
  layers, such that `f x = g (relu (T x))`. This directly mirrors the alternating
  composition `T^(k+1) ∘ ReLU ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper, with `k + 1` affine
  transformations total.
* `ReLUn n k` is read as *at most* `k` hidden layers (functions representable with some
  `k' ≤ k` hidden layers). This is the reading under which the depth-hierarchy statement
  `CPWL_n = ReLU_{n,d(n)}` is the natural one: the paper's informal restatement says
  "every CPWL function ... can be represented with `⌈log_3(n-1)⌉+1` hidden layers", i.e.
  that many hidden layers *suffice*, which is exactly the "at most k" reading. (Under an
  "exactly k" reading the statement would additionally need every CPWL function to
  require *at least* that many layers, which is not claimed.)
* `CPWL n` is defined mathematically as: `f` is continuous, and there is a *finite*
  cover of `ℝ^n` by closed halfspace-polyhedra on each of which `f` agrees with some
  affine function. This is a genuine piecewise-linearity condition, independent of the
  notion of ReLU-representability, and not phrased as a max-of-affine normal form.
* The depth bound `⌈log_3 (n-1)⌉ + 1` is encoded with the real logarithm `Real.logb 3`
  and `Nat.ceil`.
-/

/-- `relu` on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^n`. -/
def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a
translation vector, acting as `x ↦ A * x + c`. -/
structure Affine (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def Affine.eval {a b : ℕ} (T : Affine a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `NetworkComputes n k f` means `f : ℝ^n → ℝ` is computed by *some* ReLU network with
exactly `k` hidden layers, i.e. by an alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations with
componentwise ReLU applied after each of the first `k` of them. We define this by
recursion on `k`: with `0` hidden layers `f` is itself an affine map (just `T^(1)`);
with `k + 1` hidden layers, the first affine map `T^(1) : ℝ^n → ℝ^m` (for some hidden
width `m`) followed by `ReLU` feeds into a network with `k` hidden layers computing the
rest (`T^(2), …, T^(k+2)`). -/
def NetworkComputes : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : Affine n 1, ∀ x, f x = T.eval x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : Affine n m) (g : (Fin m → ℝ) → ℝ),
        NetworkComputes m k g ∧ ∀ x, f x = g (reluVec (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers (see the discussion above for why "at most" is the reading
that makes Theorem 2 true). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, NetworkComputes n k' f}

/-- A subset of `ℝ^n` cut out by finitely many affine (non-strict) inequalities, i.e. a
closed halfspace-polyhedron. -/
def IsHalfspacePolyhedron {n : ℕ} (P : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (a : Fin m → Fin n → ℝ) (b : Fin m → ℝ),
    P = {x | ∀ j, ∑ i, a j i * x i ≤ b j}

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: those that
are continuous and admit a finite cover of `ℝ^n` by closed halfspace-polyhedra, on each
of which the function agrees with some affine function. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (P : Fin m → Set (Fin n → ℝ)) (g : Fin m → Affine n 1),
      (⋃ i, P i) = Set.univ ∧
      (∀ i, IsHalfspacePolyhedron (P i)) ∧
      ∀ i, ∀ x ∈ P i, f x = (g i).eval x 0}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so `n - 1 ≥ 2`). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉+1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent081

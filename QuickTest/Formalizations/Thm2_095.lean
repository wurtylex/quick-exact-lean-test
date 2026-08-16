import Mathlib

namespace Agent095

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We encode `ℝ^n` as `Fin n → ℝ`.

* `relu` / `reluVec` : the scalar and componentwise ReLU.
* `Affine a b` : an affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a
  bias vector, `x ↦ A *ᵥ x + c`.
* `HiddenLayers k f` : an inductive judgement saying that the vector-valued function `f`
  is computed by an alternating composition of `k + 1` affine maps and `k` interleaved
  (componentwise) ReLUs, i.e. by a ReLU network with `k` hidden layers, following the
  definition
      T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1).
  The `base` constructor is the case of a single affine map (0 hidden layers, depth 1);
  `step` prepends one more affine-then-ReLU layer.
* `ComputedByReLUNetwork n k f` : a real-valued `f : ℝ^n → ℝ` is computed by some
  `HiddenLayers k` network whose 1-dimensional output is read off as a scalar.
* `ReLUn n k` : functions computed with **at most** `k` hidden layers. We choose "at most"
  rather than "exactly", since a network with `k` hidden layers can always be padded to
  `k' ≥ k` hidden layers computing the very same function (each extra layer can implement
  the identity on ℝ via `relu(x) - relu(-x) = x`, using two neurons per coordinate). Hence
  the classes `ReLU_{n,k}` are increasing in `k`, and reading Theorem 2's `ReLU_{n,d(n)}`
  as "at most `d(n)` hidden layers" is the reading under which the equality
  `CPWL_n = ReLU_{n,d(n)}` can hold (it says `d(n)` hidden layers suffice, and no CPWL_n
  function needs more).
* `CPWL n` : continuous functions `ℝ^n → ℝ` that are affine on each piece of a finite cover
  of `ℝ^n` by closed convex sets (a genuine finite polyhedral-type subdivision condition,
  not defined via ReLU-representability or a max-of-affine normal form).
* `depthBound n` : the quantity `⌈log_3 (n - 1)⌉ + 1`, using the real logarithm
  `Real.logb 3` and `Nat.ceil`.
-/

/-- The scalar ReLU function. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix `A` and bias `c`,
computing `x ↦ A *ᵥ x + c`. -/
structure Affine (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def Affine.eval {a b : ℕ} (T : Affine a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `HiddenLayers k f` means the vector-valued function `f : ℝ^n → ℝ^m` is computed by a
ReLU network with `k` hidden layers, i.e. by the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations. -/
inductive HiddenLayers : (k : ℕ) → {n m : ℕ} → ((Fin n → ℝ) → (Fin m → ℝ)) → Prop
  | base {n m : ℕ} (T : Affine n m) : HiddenLayers 0 T.eval
  | step {n m p : ℕ} (k : ℕ) (T : Affine n m) (g : (Fin m → ℝ) → (Fin p → ℝ))
      (hg : HiddenLayers k g) :
      HiddenLayers (k + 1) (fun x => g (reluVec (T.eval x)))

/-- A real-valued function `f : ℝ^n → ℝ` is computed by a ReLU network with `k` hidden
layers if it arises as the (unique) output coordinate of some `HiddenLayers k` network
with output dimension `1`. -/
def ComputedByReLUNetwork (n k : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ g : (Fin n → ℝ) → (Fin 1 → ℝ), HiddenLayers k g ∧ ∀ x, f x = g x 0

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
**at most** `k` hidden layers (see the module docstring for why "at most" is the right
reading here). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, ComputedByReLUNetwork n k' f}

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: those that are
continuous and admit a finite cover of `ℝ^n` by closed convex pieces on each of which the
function agrees with some affine function. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (a : Fin m → (Fin n → ℝ)) (b : Fin m → ℝ) (S : Fin m → Set (Fin n → ℝ)),
      (⋃ j, S j) = Set.univ ∧
      (∀ j, IsClosed (S j)) ∧
      (∀ j, Convex ℝ (S j)) ∧
      ∀ j, ∀ x ∈ S j, f x = (∑ i, a j i * x i) + b j}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, using the real logarithm to base
`3` and `Nat.ceil`. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n - 1 : ℕ) : ℝ)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3 (n - 1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent095

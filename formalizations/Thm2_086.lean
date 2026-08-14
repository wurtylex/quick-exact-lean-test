import Mathlib

namespace Agent086

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):

  For n ≥ 3,  CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}.

Modelling choices (see summary at the end of the task report):
  * `ℝ^n` is encoded as `Fin n → ℝ`.
  * Affine transformations `ℝ^a → ℝ^b` are encoded concretely via a matrix `A : Fin b →
    Fin a → ℝ` and bias `c : Fin b → ℝ`, through the predicate `IsAffine`.
  * "Computed by a ReLU network with exactly k hidden layers" is defined recursively via
    `NetComputes`, mirroring the alternating composition
    `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper.
  * `ReLUn n k` is taken to mean *at most* `k` hidden layers (a union over `k' ≤ k` of the
    "exactly `k'`" sets), which is the reading under which Theorem 2 is a true statement
    (and is in any case equivalent to "exactly k, for k large enough" since extra layers
    can always be padded out using `ReLU(x) - ReLU(-x) = x`).
  * `CPWL n` is defined as: continuous, and admitting a finite polyhedral subdivision of
    `ℝ^n` (each piece cut out by finitely many affine inequalities) on each piece of which
    `f` agrees with an affine formula. This is a genuine piecewise-linearity condition, not
    a restatement of ReLU-representability and not a max-of-affine normal form.
  * The depth bound `⌈log_3(n-1)⌉ + 1` is encoded literally using `Real.logb 3` and
    `Nat.ceil`.
-/

/-- The ReLU function on `ℝ`. -/
def reluR (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `reluR` to a vector `ℝ^p`. -/
def reluVec {p : ℕ} (v : Fin p → ℝ) : Fin p → ℝ := fun i => reluR (v i)

/-- `f : ℝ^n → ℝ^m` is an affine transformation, i.e. `f x = A x + c` for some matrix `A`
and bias vector `c`. -/
def IsAffine (n m : ℕ) (f : (Fin n → ℝ) → (Fin m → ℝ)) : Prop :=
  ∃ (A : Fin m → Fin n → ℝ) (c : Fin m → ℝ),
    ∀ (x : Fin n → ℝ) (j : Fin m),
      f x j = Finset.sum Finset.univ (fun i => A j i * x i) + c j

/-- `NetComputes k n m f` means that `f : ℝ^n → ℝ^m` is computed by a ReLU network with
input dimension `n`, output dimension `m`, and *exactly* `k` hidden layers, i.e. `f` is the
alternating composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine
transformations with componentwise ReLU applications in between, as in Section 1 of the
paper. Defined by recursion on `k`. -/
def NetComputes : (k n m : ℕ) → ((Fin n → ℝ) → (Fin m → ℝ)) → Prop
  | 0, n, m, f => IsAffine n m f
  | k + 1, n, m, f =>
      ∃ (h : ℕ) (T : (Fin n → ℝ) → (Fin h → ℝ)) (g : (Fin h → ℝ) → (Fin m → ℝ)),
        IsAffine n h T ∧ NetComputes k h m g ∧ f = fun x => g (reluVec (T x))

/-- The set of functions `ℝ^n → ℝ` representable by a ReLU network with *exactly* `k`
hidden layers. Output dimension is `1`; we read off the single coordinate. -/
def ReLUnExact (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | NetComputes k n 1 (fun x (_ : Fin 1) => f x) }

/-- `ReLUn n k`, the set of functions `ℝ^n → ℝ` representable with *at most* `k` hidden
layers (a network with fewer hidden layers can always be extended to one with more, by
inserting identity layers realized as `ReLU(x) - ReLU(-x) = x`; taking the "at most"
reading is what makes the equality in Theorem 2 correct). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, f ∈ ReLUnExact n k' }

/-- A polyhedral subset of `ℝ^n`: the solution set of finitely many affine inequalities. -/
def IsPolyhedralSet (n : ℕ) (P : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (A : Fin m → Fin n → ℝ) (c : Fin m → ℝ),
    P = { x : Fin n → ℝ | ∀ j, Finset.sum Finset.univ (fun i => A j i * x i) ≤ c j }

/-- `CPWL n`: the continuous, piecewise linear functions `ℝ^n → ℝ`, i.e. those that are
continuous and admit a finite polyhedral subdivision of `ℝ^n` on each piece of which the
function agrees with an affine formula. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (ι : ℕ) (P : Fin ι → Set (Fin n → ℝ)) (A : Fin ι → Fin n → ℝ) (b : Fin ι → ℝ),
          (∀ j, IsPolyhedralSet n (P j)) ∧
          (⋃ j, P j) = Set.univ ∧
          (∀ j, ∀ x ∈ P j, f x = Finset.sum Finset.univ (fun i => A j i * x i) + b j) }

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from Theorem 2, encoded via the real logarithm
`Real.logb 3` and `Nat.ceil`. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉+1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent086

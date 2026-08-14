import Mathlib

namespace Agent003

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

  Theorem 2. For n ≥ 3, we have CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}.

## Modelling choices

* Vectors `ℝ^n` are encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is encoded concretely as a pair `(A, c)` of a
  weight matrix `A : Matrix (Fin b) (Fin a) ℝ` and a bias vector `c : Fin b → ℝ`, evaluated
  as `x ↦ A *ᵥ x + c`.
* A "ReLU network with `k` hidden layers computing `f : ℝ^n → ℝ`" is encoded by structural
  recursion on `k`: with `0` hidden layers, `f` is literally an affine map `ℝ^n → ℝ`
  (i.e. `T^{(1)}`, no ReLU applied); with `k+1` hidden layers, `f` factors as
  `f x = g (relu (T x))` where `T : ℝ^n → ℝ^m` is affine (this is `T^{(1)}`), `relu` is
  applied componentwise, and `g : ℝ^m → ℝ` is computed by a ReLU network with `k` hidden
  layers. Unwinding the recursion literally reproduces the alternating composition
  `T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}` from the paper.
* `ReLUn n k` (the set `ReLU_{n,k}`) is taken to mean representable with **at most** `k`
  hidden layers (`∃ k' ≤ k, ...`), not exactly `k`. This is the reading that makes
  Theorem 2 true: extra hidden layers never hurt (one can always pad with an
  affine "identity-like" layer), so the classes `ReLUnExact n k'` are increasing in `k'`
  up to representability, and the "at most k" reading is the standard one for
  expressivity results of this kind.
* `CPWL n` is defined mathematically (not via ReLU networks and not as a max-of-affine
  normal form): `f` is CPWL iff `f` is continuous and there is a *finite* family of affine
  functions `g_1, ..., g_m : ℝ^n → ℝ` such that every point `x` has a neighborhood on which
  `f` coincides with one of the `g_i`. This is the "locally agrees with a finite family of
  affine pieces" characterization of continuous piecewise-linear functions.
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined using the real logarithm `Real.logb 3` and
  `Nat.ceil`, exactly mirroring the real-valued ceiling in the paper.
-/

/-- The scalar ReLU function `max 0 ·` on `ℝ`. -/
def relu (t : ℝ) : ℝ := max 0 t

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a weight matrix and a bias
vector, as `x ↦ A x + c`. -/
def AffineMap (a b : ℕ) : Type := Matrix (Fin b) (Fin a) ℝ × (Fin b → ℝ)

/-- Evaluate an affine transformation `x ↦ A x + c`. -/
def AffineMap.eval {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.1.mulVec x + T.2

/-- A real-valued affine function `ℝ^n → ℝ`, i.e. `x ↦ ⟨a, x⟩ + c`. -/
def IsAffineFun {n : ℕ} (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (c : ℝ), ∀ x, g x = (∑ i, a i * x i) + c

/-- The functions `ℝ^n → ℝ` computed by a ReLU network with *exactly* `k` hidden layers,
i.e. by the alternating composition
`T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}`
of `k + 1` affine transformations `T^{(1)}, ..., T^{(k+1)}` with `component-wise` ReLU
applied after each of the first `k` of them. Defined by structural recursion on `k`. -/
def ReLUnExact : (n : ℕ) → (k : ℕ) → Set ((Fin n → ℝ) → ℝ)
  | n, 0 => { f | ∃ T : AffineMap n 1, f = fun x => AffineMap.eval T x 0 }
  | n, (k + 1) =>
      { f | ∃ (m : ℕ) (T : AffineMap n m) (g : (Fin m → ℝ) → ℝ),
            g ∈ ReLUnExact m k ∧ f = fun x => g (reluVec (AffineMap.eval T x)) }

/-- `ReLUn n k`, the set of functions `ℝ^n → ℝ` representable with at most `k` hidden
layers (see the module docstring for why "at most" is the right reading here). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, f ∈ ReLUnExact n k' }

/-- `CPWL n`, the space of continuous piecewise-linear functions `ℝ^n → ℝ`: `f` is
continuous, and there is a finite family of affine functions such that `f` locally agrees
with (at least) one member of the family at every point. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ), (∀ i, IsAffineFun (g i)) ∧
          ∀ x : Fin n → ℝ, ∃ i, Filter.Eventually (fun y => f y = g i y) (nhds x) }

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so `n - 1 ≥ 2 > 0`). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) : CPWL n = ReLUn n (depthBound n) := sorry

end Agent003

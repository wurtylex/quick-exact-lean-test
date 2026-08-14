import Mathlib

namespace Agent007

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We encode `ℝ^n` as `Fin n → ℝ`. Affine transformations `ℝ^a → ℝ^b` are encoded
concretely as `x ↦ A.mulVec x + c` for a matrix `A` and bias vector `c`. A ReLU
network with `k` hidden layers is a `k+1`-fold alternating composition of such
affine transformations with the componentwise ReLU nonlinearity, encoded by the
recursive predicate `RepresentableVec` below. `ReLUn n k` is the set of scalar
functions `ℝ^n → ℝ` representable by *some* ReLU network with *at most* `k`
hidden layers (this is the reading of `ReLU_{n,k}` under which Theorem 2 is
true: since a ReLU network with `j ≤ k` hidden layers can always be padded, via
the identity trick `x ↦ ReLU(x) - ReLU(-x) = x`, into a network with exactly
`k` hidden layers computing the same function, the "at most k" and "exactly k"
readings of the class actually coincide as sets, but "at most" is the more
standard and directly usable reading). `CPWL n` is defined independently, via
continuity together with local agreement with a finite family of affine
functions (a genuine piecewise-affine condition, not a max-of-affine normal
form and not "representable by a ReLU network").
-/

/-- The ReLU activation function on `ℝ`. -/
noncomputable def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^n`. -/
noncomputable def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => relu (x i)

/-- The affine transformation `ℝ^a → ℝ^b` given by matrix `A` and bias `c`,
namely `x ↦ A x + c`. -/
noncomputable def affineEval {a b : ℕ} (A : Matrix (Fin b) (Fin a) ℝ) (c : Fin b → ℝ)
    (x : Fin a → ℝ) : Fin b → ℝ :=
  A.mulVec x + c

/-- `RepresentableVec n k b f` : the vector-valued function `f : ℝ^n → ℝ^b` is
computed by a ReLU network with `k` hidden layers and output dimension `b`,
i.e. there are affine transformations `T^(1), ..., T^(k+1)` (with `T^(k+1)`
landing in `ℝ^b`) such that
`f = T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`.
The base case `k = 0` is a single affine transformation (no ReLU at all,
i.e. depth 1, 0 hidden layers); the successor case peels off the *outermost*
affine map `T^(k+1)` (with an arbitrary hidden width `m` for the preceding
layer) and applies ReLU before it. -/
def RepresentableVec : (n k b : ℕ) → ((Fin n → ℝ) → (Fin b → ℝ)) → Prop
  | n, 0, b, f =>
      ∃ (A : Matrix (Fin b) (Fin n) ℝ) (c : Fin b → ℝ), f = affineEval A c
  | n, (k + 1), b, f =>
      ∃ (m : ℕ) (g : (Fin n → ℝ) → (Fin m → ℝ))
        (A : Matrix (Fin b) (Fin m) ℝ) (c : Fin b → ℝ),
        RepresentableVec n k m g ∧ f = fun x => affineEval A c (reluVec (g x))

/-- The scalar function `f : ℝ^n → ℝ` is computed by a ReLU network with
exactly `k` hidden layers. -/
def Representable (n k : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  RepresentableVec n k 1 (fun x _ => f x)

/-- `ReLUn n k` : the set of functions `ℝ^n → ℝ` representable by a ReLU
network with *at most* `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ j ≤ k, Representable n j f}

/-- An affine function `ℝ^n → ℝ`, given by a weight vector `w` and bias `b`,
namely `x ↦ ∑ i, w i * x i + b`. -/
def AffineFun (n : ℕ) := (Fin n → ℝ) × ℝ

/-- Evaluation of an affine function. -/
noncomputable def AffineFun.eval {n : ℕ} (a : AffineFun n) (x : Fin n → ℝ) : ℝ :=
  (∑ i, a.1 i * x i) + a.2

/-- `CPWL n` : the set of continuous, piecewise-linear functions `ℝ^n → ℝ`,
i.e. continuous functions that agree, on a neighborhood of every point, with
one of finitely many globally-fixed affine functions. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧ ∃ S : Finset (AffineFun n),
        ∀ x : Fin n → ℝ, ∃ a ∈ S, ∃ U : Set (Fin n → ℝ),
          IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, f y = a.eval y}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, as a natural number. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent007

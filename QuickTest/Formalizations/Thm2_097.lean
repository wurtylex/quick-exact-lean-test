import Mathlib

namespace Agent097

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):

  For n ≥ 3, CPWL_n = ReLU_{n, ⌈log_3 (n-1)⌉ + 1}.

We encode `ℝ^n` as `Fin n → ℝ`.
-/

/-- The scalar ReLU function `x ↦ max 0 x`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`, encoded as `Fin m → ℝ`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- `T : ℝ^a → ℝ^b` is an affine transformation if it has the form `x ↦ A * x + c`
for some matrix `A` and vector `c`. -/
def IsAffineTransformation (a b : ℕ) (T : (Fin a → ℝ) → (Fin b → ℝ)) : Prop :=
  ∃ (A : Matrix (Fin b) (Fin a) ℝ) (c : Fin b → ℝ), ∀ x, T x = A.mulVec x + c

/-- `f : ℝ^n → ℝ` is computed by a ReLU network with exactly `k` hidden layers if there
is a chain of affine transformations `T^(1), ..., T^(k+1)` with intermediate widths
`n_1, ..., n_k` such that

  `f = T^(k+1) ∘ ReLU ∘ T^(k) ∘ ... ∘ ReLU ∘ T^(1)`.

This is defined by recursion on `k`, peeling off the *first* affine map / ReLU pair each
time: with `k+1` hidden layers, we first apply an affine map `T : ℝ^n → ℝ^m` followed by
`ReLU`, and the remaining computation on `ℝ^m` is a `k`-hidden-layer network. The base
case `k = 0` is a network with no hidden layers, i.e. `f` itself is affine
(a single affine output transformation `T^(1) : ℝ^n → ℝ^1`). -/
def ComputesWithHiddenLayers : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f =>
      ∃ T : (Fin n → ℝ) → (Fin 1 → ℝ),
        IsAffineTransformation n 1 T ∧ ∀ x, f x = T x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : (Fin n → ℝ) → (Fin m → ℝ)) (g : (Fin m → ℝ) → ℝ),
        IsAffineTransformation n m T ∧
        ComputesWithHiddenLayers m k g ∧
        ∀ x, f x = g (reluVec (T x))

/-- `ReLUn n k`: the functions `ℝ^n → ℝ` representable by a ReLU network with *at most*
`k` hidden layers. (We use "at most", the standard reading in the depth-separation
literature: since it need not be true that every `k`-layer-representable function is also
representable with *exactly* `k+1` layers, taking `ReLUn n k` to mean "exactly k" would
make it non-monotone in `k`, which is not the intended reading and would not match how
the class `ReLU_{n,k}` is used in the statement of Theorem 2.) -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ j ≤ k, ComputesWithHiddenLayers n j f}

/-- `f : ℝ^n → ℝ` is continuous and piecewise linear if it is continuous and there is a
finite family of affine functions `x ↦ ⟪A i, x⟫ + b i` such that `f` agrees with one of
them on a neighborhood of every point (a genuine local piecewise-affine condition, not a
"max of affine" normal form and not a reference to ReLU networks). -/
def IsCPWL (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  Continuous f ∧
  ∃ (m : ℕ) (A : Fin m → (Fin n → ℝ)) (b : Fin m → ℝ),
    ∀ x : Fin n → ℝ, ∃ i : Fin m, ∀ᶠ y in nhds x, f y = (∑ j, A i j * y j) + b i

/-- `CPWL n`: the space of continuous piecewise linear functions `ℝ^n → ℝ`. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) := {f | IsCPWL n f}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1`, using the real logarithm base 3 and the
natural-number ceiling. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent097

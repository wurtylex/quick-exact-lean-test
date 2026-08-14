import Mathlib

namespace Agent065

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):  for `n ≥ 3`,  `CPWL n = ReLUn n (⌈log_3 (n-1)⌉ + 1)`.

Modelling choices (see the summary at the end of the accompanying report):
* `ℝ^n` is encoded as `Fin n → ℝ`.
* `ReLUn n k` is the set of functions representable by a network with *exactly* `k`
  hidden layers (matching the paper's literal definition of `ReLU_{n,k}`).
* `CPWL n` is defined via continuity plus a genuine finite local-affine-pieces
  condition, independent of the network machinery.
-/

/-- The ReLU activation function on `ℝ`. -/
noncomputable def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^n`. -/
noncomputable def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias
vector: `x ↦ A x + bias`. -/
structure Affine (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  bias : Fin b → ℝ

/-- The function `ℝ^a → ℝ^b` computed by an affine transformation. -/
def Affine.apply {a b : ℕ} (T : Affine a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.bias

/-- A ReLU network with input dimension `n` and `k` hidden layers, i.e. `k + 1`
affine transformations `T^(1), ..., T^(k+1)` of matching consecutive dimensions
`dims 0 = n, dims 1, ..., dims k, dims (k+1) = 1`.  `layer i` is `T^(i+1)`,
the affine map from layer `i` to layer `i + 1`. -/
structure ReLUNetwork (n k : ℕ) where
  dims : ℕ → ℕ
  dims_zero : dims 0 = n
  dims_last : dims (k + 1) = 1
  layer : (i : ℕ) → Affine (dims i) (dims (i + 1))

/-- The activation vector at layer `i` of the network on input `x` (for `i ≤ k+1`):
the input at `i = 0`, and otherwise the affine transformation of the previous layer's
activations, followed by ReLU unless this is the final (output) layer `k+1` — this
implements the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`. -/
noncomputable def ReLUNetwork.forward {n k : ℕ} (N : ReLUNetwork n k) :
    (i : ℕ) → (Fin n → ℝ) → (Fin (N.dims i) → ℝ)
  | 0, x => fun j => x (Fin.cast N.dims_zero j)
  | i + 1, x =>
      let out := (N.layer i).apply (N.forward i x)
      if i + 1 = k + 1 then out else reluVec out

/-- The scalar output of the network on input `x` (the network's final layer has
width 1). -/
noncomputable def ReLUNetwork.output {n k : ℕ} (N : ReLUNetwork n k) (x : Fin n → ℝ) :
    ℝ :=
  N.forward (k + 1) x (Fin.cast N.dims_last.symm (0 : Fin 1))

/-- A network `N` with `k` hidden layers *computes* / *represents* `f : ℝ^n → ℝ` if
its output agrees with `f` on every input. -/
def ReLUNetwork.computes {n k : ℕ} (N : ReLUNetwork n k) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x, N.output x = f x

/-- `ReLUn n k`: the functions `ℝ^n → ℝ` representable by a ReLU network with
*exactly* `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ N : ReLUNetwork n k, N.computes f}

/-- An affine (degree-1 polynomial) function `ℝ^n → ℝ`. -/
def IsAffineFun {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x, f x = (∑ i, a i * x i) + b

/-- `CPWL n`: the continuous piecewise-linear functions `ℝ^n → ℝ`, i.e. continuous
functions that, near every point, agree with one of a finite family of affine
functions. This is the genuine geometric definition (a finite collection of affine
"pieces" covering `ℝ^n`, matching `f` locally), independent of ReLU networks and not
phrased as a max-of-affine normal form. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ),
      (∀ i, IsAffineFun (g i)) ∧ ∀ x, ∃ i, ∀ᶠ y in nhds x, f y = g i y}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, as a natural number, using
the real logarithm `Real.logb 3` and `Nat.ceil`. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL n = ReLUn n (⌈log_3 (n - 1)⌉ + 1)`. -/
theorem theorem2 : ∀ n : ℕ, n ≥ 3 → CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent065

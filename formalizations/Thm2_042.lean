import Mathlib

namespace Agent042

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We model vectors `ℝ^n` as `Fin n → ℝ`.

* An **affine layer** `ℝ^a → ℝ^b` is given concretely by a matrix `A : Matrix (Fin b) (Fin a) ℝ`
  and a vector `c : Fin b → ℝ`, computing `x ↦ A.mulVec x + c`.
* A **ReLU network with `k` hidden layers** is a list of `k + 1` affine layers of matching
  dimensions (input dimension `n`, output dimension `1`), computed by applying `ReLU`
  componentwise after every layer *except* the last one (matching the alternating
  composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper).
* `ReLUn n k` is the set of functions `ℝ^n → ℝ` computed by *some* network with **exactly**
  `k` hidden layers (the literal reading of "representable with `k` hidden layers"). Note
  that padding a network with extra "identity" hidden layers (via
  `ReLU(x) - ReLU(-x) = x`, doubling the width) shows `ReLUn n k ⊆ ReLUn n (k+1)`, so this
  choice agrees with the "at most `k`" reading for the purposes of Theorem 2.
* `CPWL n` is defined directly and honestly: continuous functions that are affine on each
  piece of a *finite* subdivision of `ℝ^n` into (closed, convex) polyhedra, each polyhedron
  itself cut out by finitely many affine inequalities. This is independent of the ReLU
  network model and does not assume a max-of-affine normal form.
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined via `Real.logb 3` and `Nat.ceil`.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^inDim → ℝ^outDim`, given concretely by a matrix and a
translation vector: `x ↦ A * x + c`. -/
structure AffineLayer where
  inDim  : ℕ
  outDim : ℕ
  A : Matrix (Fin outDim) (Fin inDim) ℝ
  c : Fin outDim → ℝ

/-- Evaluate an affine layer on a dimension-tagged vector, provided the dimensions match;
otherwise the input is returned unchanged (this branch never occurs for well-formed
networks, see `NetworkComputes`). -/
def AffineLayer.evalSig (T : AffineLayer) (v : Σ m : ℕ, Fin m → ℝ) : Σ m : ℕ, Fin m → ℝ :=
  if h : v.1 = T.inDim then
    ⟨T.outDim, T.A.mulVec (v.2 ∘ Fin.cast h.symm) + T.c⟩
  else
    v

/-- Componentwise `relu` on a dimension-tagged vector. -/
def reluVecSig (v : Σ m : ℕ, Fin m → ℝ) : Σ m : ℕ, Fin m → ℝ := ⟨v.1, reluVec v.2⟩

/-- The forward pass of a ReLU network given as a list of affine layers: apply each layer,
inserting a componentwise `ReLU` between consecutive layers but *not* after the final layer
(matching `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`). -/
def runLayers : List AffineLayer → (Σ m : ℕ, Fin m → ℝ) → (Σ m : ℕ, Fin m → ℝ)
  | [], v => v
  | [T], v => T.evalSig v
  | T :: rest, v => runLayers rest (reluVecSig (T.evalSig v))

/-- `NetworkComputes n layers f` means: `layers` is a well-formed ReLU network with input
dimension `n` and output dimension `1` (consecutive layers have matching dimensions), and
its forward pass computes `f`. -/
def NetworkComputes (n : ℕ) (layers : List AffineLayer) (f : (Fin n → ℝ) → ℝ) : Prop :=
  (layers.head?.map (·.inDim) = some n) ∧
  (layers.getLast?.map (·.outDim) = some 1) ∧
  (List.Chain' (fun T1 T2 => T1.outDim = T2.inDim) layers) ∧
  (∀ x : Fin n → ℝ, ∃ y : Fin 1 → ℝ, runLayers layers ⟨n, x⟩ = ⟨1, y⟩ ∧ f x = y 0)

/-- The set of functions `ℝ^n → ℝ` representable by a ReLU network with **exactly** `k`
hidden layers, i.e. `k + 1` affine transformations. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ layers : List AffineLayer, layers.length = k + 1 ∧ NetworkComputes n layers f}

/-- A polyhedron in `ℝ^n`: the solution set of a finite system of affine inequalities
`⟨a_j, x⟩ ≤ b_j`. -/
def IsPolyhedron {n : ℕ} (P : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (a : Fin m → (Fin n → ℝ)) (b : Fin m → ℝ),
    P = {x : Fin n → ℝ | ∀ j : Fin m, (∑ i, a j i * x i) ≤ b j}

/-- `CPWL n`: continuous functions `ℝ^n → ℝ` that admit a finite subdivision of `ℝ^n` into
polyhedral pieces, on each of which the function agrees with some affine function. This is
a genuine piecewise-linearity condition, independent of the ReLU network model. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
       ∃ (m : ℕ) (P : Fin m → Set (Fin n → ℝ)) (A : Fin m → (Fin n → ℝ)) (c : Fin m → ℝ),
         (∀ i, IsPolyhedron (P i)) ∧
         (⋃ i, P i) = Set.univ ∧
         (∀ i, ∀ x ∈ P i, f x = (∑ k, A i k * x k) + c i)}

noncomputable section

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from Theorem 2, as the number of hidden layers. -/
def depthBound (n : ℕ) : ℕ := ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

end

/-- **Theorem 2.** For `n ≥ 3`, the class of continuous piecewise-linear functions on `ℝ^n`
coincides with the class of functions representable by a ReLU network with
`⌈log_3(n - 1)⌉ + 1` hidden layers. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent042

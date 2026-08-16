import Mathlib

/-
Formalization of Theorem 2 of arXiv:2505.14338
("Better Neural Network Expressivity: Subdividing the Simplex")

Modelling choices (agent 066):
* Vectors ℝ^n are encoded as `Fin n → ℝ`.
* Affine maps ℝ^a → ℝ^b are encoded concretely as a matrix `A : Matrix (Fin b) (Fin a) ℝ`
  together with a bias vector `b : Fin b → ℝ`, evaluated via `A.mulVec x + b`.
* "Computed by a ReLU network with k hidden layers" is formalized by recursion on k:
  a depth-1 network (0 hidden layers) is a single affine map into `Fin 1 → ℝ` (we read off
  its unique coordinate); a network with `k+1` hidden layers first applies an affine map
  into some hidden width `m`, then componentwise ReLU, and then continues as a network
  with `k` hidden layers computing `ℝ^m → ℝ`. This exactly mirrors the alternating
  composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ... ∘ ReLU ∘ T^(1)` from the paper.
* `ReLUn n k` is taken to mean representable with **at most** `k` hidden layers (not
  exactly `k`). This is the standard reading and the one that makes Theorem 2 true: since
  a `k`-hidden-layer function can always be re-expressed with `k+1` hidden layers (e.g. by
  using an extra layer computing `x ↦ ReLU(x) - ReLU(-x) = x` componentwise before
  continuing), the classes `ReLUn n k` are monotone increasing in `k`, and the theorem's
  equality is with the class of functions using at most the stated number of layers.
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of affine maps
  `g : Fin m → (ℝ^n →ᵃ[ℝ] ℝ)` such that `f` agrees with some `g i` on a neighborhood of
  every point `x`. This is a genuine local-piecewise-affine condition (not a max-of-affine
  normal form, and not "representable by some ReLU network"), matching the standard
  definition of continuous piecewise linear functions via a finite family of affine pieces.
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined directly via `Real.logb 3` and `Nat.ceil`.
-/

namespace Agent066

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (v : Fin m → ℝ) : Fin m → ℝ := fun i => relu (v i)

/-- `ReLUComputable n k f` means: `f : ℝ^n → ℝ` is computed by a ReLU network with `k`
hidden layers, i.e. by the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ... ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations
`T^(1) : ℝ^n → ℝ^{n_1}, ..., T^(k+1) : ℝ^{n_k} → ℝ`, with componentwise ReLU applied after
each of the first `k` affine maps. We recurse on `k`: the base case `k = 0` is a single
affine map `ℝ^n → ℝ` (depth 1, no hidden layers); the successor case peels off the first
affine map (into some hidden width `m`), applies ReLU, and recurses with `k` hidden
layers on the resulting `ℝ^m → ℝ` network. -/
def ReLUComputable : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f =>
      ∃ (A : Matrix (Fin 1) (Fin n) ℝ) (b : Fin 1 → ℝ),
        ∀ x : Fin n → ℝ, f x = (A.mulVec x + b) 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (g : (Fin m → ℝ) → ℝ),
        ReLUComputable m k g ∧
        ∀ x : Fin n → ℝ, f x = g (reluVec (A.mulVec x + b))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers (see the module docstring for why "at most" is the reading
that makes Theorem 2 true). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, ReLUComputable n k' f}

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: those that
are continuous and agree, in a neighborhood of every point, with one member of some fixed
*finite* family of affine functions. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
        ∃ (m : ℕ) (g : Fin m → ((Fin n → ℝ) →ᵃ[ℝ] ℝ)),
          ∀ x : Fin n → ℝ, ∃ i : Fin m, f =ᶠ[nhds x] (g i)}

/-- The depth bound from Theorem 2: `⌈log_3(n - 1)⌉ + 1` hidden layers. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL n = ReLUn n (⌈log_3(n-1)⌉ + 1)`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent066

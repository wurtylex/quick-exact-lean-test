import Mathlib

namespace Agent073

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):

  For n ≥ 3,  CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}.

Modelling choices (see summary at the end of the file):
* Vectors `ℝ^n` are encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is encoded concretely by a matrix and a bias
  vector, `x ↦ A * x + c`.
* "Computed by a ReLU network with `k` hidden layers" is encoded by the recursive
  predicate `IsReLURep`, unwinding exactly the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper.
* `ReLUn n k` uses *exactly* `k` hidden layers (matching the literal recursive
  unwinding of the definition of `ReLU_{n,k}` in the paper).
* `CPWL n` is defined by continuity together with local agreement, at every point,
  with one of finitely many affine functions -- a genuine piecewise-linearity
  condition that does not presuppose any max-of-affine normal form or ReLU
  representability.
-/

/-- The ReLU function on `ℝ`. -/
noncomputable def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`, encoded as `Fin m → ℝ`. -/
noncomputable def reluVec {m : ℕ} (v : Fin m → ℝ) : Fin m → ℝ := fun i => relu (v i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix `A` and a bias
vector `c`, computing `x ↦ A * x + c`. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def AffineMap.eval {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `IsReLURep n m k f` means the function `f : ℝ^n → ℝ^m` is computed by a ReLU
network with `k` hidden layers, i.e. by the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations
`T^(1), …, T^(k+1)` (with `T^(1) : ℝ^n → ℝ^{n_1}`, …, `T^(k+1) : ℝ^{n_k} → ℝ^m` for
some sequence of intermediate widths `n_1, …, n_k`).

The base case `k = 0` (depth `1`, no hidden layers) is a single affine map. The
recursive case peels off the first affine map `T^(1) : ℝ^n → ℝ^p` and the ReLU applied
to it, leaving a network with `k` hidden layers computing the rest. -/
noncomputable def IsReLURep : (n m k : ℕ) → ((Fin n → ℝ) → (Fin m → ℝ)) → Prop
  | n, m, 0, f => ∃ T : AffineMap n m, f = T.eval
  | n, m, (k + 1), f =>
      ∃ (p : ℕ) (T : AffineMap n p) (g : (Fin p → ℝ) → (Fin m → ℝ)),
        IsReLURep p m k g ∧ f = g ∘ (reluVec ∘ T.eval)

/-- `ReLUn n k`: the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*exactly* `k` hidden layers. We view `f : ℝ^n → ℝ` as the `ℝ^1`-valued function
`x ↦ (fun _ => f x)`. -/
noncomputable def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | IsReLURep n 1 k (fun x (_ : Fin 1) => f x) }

/-- `CPWL n`: the continuous piecewise-linear functions `ℝ^n → ℝ`. We say `f` is CPWL
if it is continuous and there is a *finite* set of affine functions `ℝ^n → ℝ` such that
every point of `ℝ^n` has a neighbourhood on which `f` coincides with one of them. -/
noncomputable def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ S : Finset (AffineMap n 1),
          ∀ x : Fin n → ℝ, ∃ T ∈ S, ∃ U ∈ nhds x, ∀ y ∈ U, f y = T.eval y 0 }

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from Theorem 2, with `log_3` the real
logarithm to base `3` and `⌈·⌉` the natural-number ceiling of a real number. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent073

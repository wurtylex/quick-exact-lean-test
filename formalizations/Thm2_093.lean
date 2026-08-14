import Mathlib

namespace Agent093

/-! ## Basic building blocks -/

/-- The ReLU activation on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `Fin m → ℝ`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias
vector: `x ↦ A x + c`. -/
def AffineMap' (a b : ℕ) := (Fin b → Fin a → ℝ) × (Fin b → ℝ)

/-- Evaluate an affine transformation. -/
def AffineMap'.apply {a b : ℕ} (T : AffineMap' a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, T.1 i j * x j) + T.2 i

/-- An affine *functional* `ℝ^n → ℝ`, i.e. an affine map into `ℝ^1`. -/
def AffFun (n : ℕ) := AffineMap' n 1

/-- Evaluate an affine functional. -/
def AffFun.eval {n : ℕ} (L : AffFun n) (x : Fin n → ℝ) : ℝ := AffineMap'.apply L x 0

/-! ## ReLU networks -/

/--
`Layers a ws b` encodes the data of a chain of affine transformations, alternating with
ReLU, that takes `ℝ^a` to `ℝ^b` and passes through hidden layers whose widths are listed
(in order) in `ws`. This is exactly the data of a ReLU network
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` with `k = ws.length` hidden layers, as in the
paper's definition of a ReLU network of depth `k + 1`.
-/
inductive Layers : ℕ → List ℕ → ℕ → Type
  | last {a b : ℕ} (T : AffineMap' a b) : Layers a [] b
  | cons {a b : ℕ} {ws : List ℕ} (m : ℕ) (T : AffineMap' a m) (rest : Layers m ws b) :
      Layers a (m :: ws) b

/-- The function `ℝ^a → ℝ^b` computed by a chain of layers: the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`. -/
def Layers.apply {a b : ℕ} {ws : List ℕ} : Layers a ws b → (Fin a → ℝ) → (Fin b → ℝ)
  | .last T, x => T.apply x
  | .cons _ T rest, x => rest.apply (reluVec (T.apply x))

/--
`f : ℝ^n → ℝ` is computed by a ReLU network with *at most* `k` hidden layers if there is a
list of hidden-layer widths of length `≤ k` and a matching chain of affine
transformations, alternating componentwise with ReLU, whose composition (followed by
reading off the single real output coordinate) equals `f`.

Modelling choice: we use *at most* `k` hidden layers rather than *exactly* `k`. Adding
extra hidden layers can never shrink the class of representable functions (one can always
insert an identity-computing hidden layer, e.g. via `x ↦ (x, -x) ↦ ReLU(x, -x) ↦ x`), so
`ReLU_{n,k}` is monotone increasing in `k`; this is the reading under which an *equality*
`CPWL_n = ReLU_{n,k}` with a specific value of `k` (rather than only `⊆`) is a meaningful,
nontrivial statement, and is the standard reading in this literature.
-/
def IsReLUComputable (n k : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ ws : List ℕ, ws.length ≤ k ∧ ∃ L : Layers n ws 1, f = fun x => L.apply x 0

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with at
most `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) := {f | IsReLUComputable n k f}

/-! ## Continuous piecewise linear functions -/

/-- A closed, convex polyhedral subset of `ℝ^n`, cut out by finitely many affine
inequalities `(H i).eval x ≤ 0`. -/
def IsPolyhedron (n : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (H : Fin m → AffFun n), S = {x | ∀ i, (H i).eval x ≤ 0}

/--
`CPWL n` is the set of continuous, piecewise linear functions `ℝ^n → ℝ`: functions `f`
that are continuous and admit a finite polyhedral subdivision of `ℝ^n` (finitely many
polyhedral pieces whose union is all of `ℝ^n`) on each piece of which `f` agrees with some
affine function. This is a genuine geometric piecewise-linearity condition, not simply
"expressible by some ReLU network" nor a max-of-affine-functions normal form.
-/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (S : Fin m → Set (Fin n → ℝ)) (L : Fin m → AffFun n),
      (⋃ i, S i) = Set.univ ∧
      (∀ i, IsPolyhedron n (S i)) ∧
      (∀ i, ∀ x ∈ S i, f x = (L i).eval x)}

/-! ## The depth bound `⌈log_3 (n - 1)⌉ + 1` -/

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2 (meaningful for `n ≥ 3`, so that
`n - 1 ≥ 2 > 0`). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-! ## Theorem 2 -/

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent093

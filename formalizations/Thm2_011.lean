import Mathlib

namespace Agent011

/- ================================================================
   Vector encoding: we represent ℝ^n as `Fin n → ℝ`.
   ================================================================ -/

/-- The ReLU activation on a single real number. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on a vector `Fin m → ℝ`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/- ================================================================
   Affine transformations `ℝ^a → ℝ^b`, given concretely by a matrix
   and a bias vector: `x ↦ A.mulVec x + c`.
   ================================================================ -/

/-- An affine transformation `ℝ^a → ℝ^b`, given by a matrix `A` and bias `c`. -/
structure Layer (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluate an affine layer at a point. -/
def Layer.apply {a b : ℕ} (L : Layer a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  L.A.mulVec x + L.c

/-- An affine functional `ℝ^n → ℝ` (i.e. a `Layer n 1` evaluated at the unique output
    coordinate). Used below to phrase "piecewise affine". -/
def IsAffineFun (n : ℕ) (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x : Fin n → ℝ, g x = (∑ i : Fin n, a i * x i) + b

/- ================================================================
   ReLU networks with exactly `k` hidden layers, from input dimension
   `a` down to scalar output, given as an inductively-built chain of
   affine layers with ReLU nonlinearities interleaved:

       T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)

   `NetLayers a k` packages exactly this data: `k` hidden layers means
   `k + 1` affine transformations `T^(1), …, T^(k+1)`, with a ReLU
   applied after each of the first `k` of them.
   ================================================================ -/

/-- `NetLayers a k` : the data of a ReLU network with input dimension `a`,
    scalar output, and exactly `k` hidden layers (i.e. `k + 1` affine maps,
    with ReLU applied between consecutive ones). -/
inductive NetLayers : ℕ → ℕ → Type
  | last {a : ℕ} (L : Layer a 1) : NetLayers a 0
  | cons {a b k : ℕ} (L : Layer a b) (rest : NetLayers b k) : NetLayers a (k + 1)

/-- The scalar function `ℝ^a → ℝ` computed by a `NetLayers a k` network. -/
def NetLayers.eval : {a k : ℕ} → NetLayers a k → (Fin a → ℝ) → ℝ
  | _, _, NetLayers.last L, x => L.apply x 0
  | _, _, NetLayers.cons L rest, x => rest.eval (reluVec (L.apply x))

/-- `ReLUn n k` : the CPWL functions `ℝ^n → ℝ` representable by a ReLU network
    with **at most** `k` hidden layers. (We use "at most `k`" rather than
    "exactly `k`": extra hidden layers never lose expressivity — an extra
    layer can always implement the identity via `x ↦ relu x - relu (-x)` —
    so this is the reading under which the increasing family `ReLUn n k`
    stabilizes at `CPWL n`, matching Theorem 2 as an equality of sets.) -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ j ≤ k, ∃ net : NetLayers n j, f = net.eval }

/- ================================================================
   Continuous piecewise-linear (CPWL) functions `ℝ^n → ℝ`: continuous
   functions that locally agree with one of finitely many affine
   functionals around every point (a genuine local-affine / polyhedral-
   subdivision style definition, not "max of affine" and not
   "representable by a ReLU network").
   ================================================================ -/

/-- `CPWL n` : continuous functions `ℝ^n → ℝ` that, near every point, coincide
    with one of a fixed finite family of affine functionals. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (g : Fin m → ((Fin n → ℝ) → ℝ)),
          (∀ i, IsAffineFun n (g i)) ∧
          ∀ x : Fin n → ℝ, ∃ i : Fin m, ∃ U ∈ nhds x, Set.EqOn f (g i) U }

/- ================================================================
   The depth bound `⌈log_3 (n - 1)⌉ + 1`, using the real logarithm
   `Real.logb 3` and `Nat.ceil`.
   ================================================================ -/

/-- The hidden-layer bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2. -/
def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/- ================================================================
   Theorem 2.
   ================================================================ -/

theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent011

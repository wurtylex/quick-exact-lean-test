import Mathlib

namespace Agent035

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

  "Better Neural Network Expressivity: Subdividing the Simplex"
  (Bakaev, Brunck, Hertrich, Stade, Yehudayoff)

  Theorem 2. For n ≥ 3, we have CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}.

## Modelling choices

* Vectors `ℝ^n` are encoded as `Fin n → ℝ`.
* An affine map `ℝ^a → ℝ^b` is encoded concretely as a matrix `A : Matrix (Fin b) (Fin a) ℝ`
  together with a bias vector `b : Fin b → ℝ`, acting via `x ↦ A.mulVec x + b`.
* A ReLU network with exactly `k` hidden layers, input dimension `a` and output dimension `c`
  is encoded as a dependent inductive family `NetLayers k a c` of `k + 1` affine layers, with
  a `relu` (componentwise) applied after every layer except the last (output) one. This
  literally mirrors the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper.
* `ReLUn n k` is taken to be the set of functions representable with **at most** `k` hidden
  layers (rather than *exactly* `k`): a network with `k'` hidden layers for any `k' ≤ k`
  witnesses membership. This is the standard reading in the neural-network-depth literature
  (adding hidden layers can only help, e.g. via layer padding), and it is also the reading
  under which the stated equality `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉+1}` is meaningful as a
  *sufficiency* statement for that specific depth (rather than requiring the depth to be
  simultaneously necessary at exactly that value for every single CPWL function).
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of affine
  functions `ℝ^n → ℝ` such that `f` locally agrees (in a neighbourhood of every point) with
  one of them. This is a genuine piecewise-linearity condition (not defined via ReLU
  networks, and not a max-of-affine normal form).
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded using the real logarithm `Real.logb 3` and
  `Nat.ceil` (`⌈·⌉₊`), matching the paper's real-valued ceiling of `log_3`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector in `ℝ^n`. -/
def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias vector. -/
structure AffineMap' (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  bias : Fin b → ℝ

/-- The function `ℝ^a → ℝ^b` computed by an affine transformation. -/
def AffineMap'.apply {a b : ℕ} (T : AffineMap' a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.bias

/-- A ReLU network with exactly `k` hidden layers, input dimension `a`, output dimension `c`,
given as a chain of `k + 1` affine transformations, each (except the last) followed by a
componentwise ReLU. This directly encodes the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper: the `last` constructor is the
final affine map `T^(k+1)` (no `k` hidden layers, i.e. depth 1), and `cons` prepends a new
affine map `T^(1)` together with the ReLU applied right after it, incrementing the hidden
layer count by one. -/
inductive NetLayers : ℕ → ℕ → ℕ → Type
  | last {a b : ℕ} (T : AffineMap' a b) : NetLayers 0 a b
  | cons {a b c : ℕ} {k : ℕ} (T : AffineMap' a b) (rest : NetLayers k b c) :
      NetLayers (k + 1) a c

/-- The function `ℝ^a → ℝ^c` computed by a ReLU network. -/
def NetLayers.eval {k a c : ℕ} (net : NetLayers k a c) (x : Fin a → ℝ) : Fin c → ℝ :=
  match net with
  | .last T => T.apply x
  | .cons T rest => rest.eval (reluVec (T.apply x))

/-- A function `ℝ^n → ℝ` is computed by a ReLU network with exactly `k` hidden layers. -/
def NetworkComputes (n k : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ net : NetLayers k n 1, ∀ x : Fin n → ℝ, f x = net.eval x 0

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers (see the module docstring for why "at most" is the right
reading here). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' : ℕ, k' ≤ k ∧ NetworkComputes n k' f }

/-- `f : ℝ^n → ℝ` is continuous and piecewise linear: it is continuous, and there is a
finite family of affine functions such that `f` locally agrees with one of them at every
point. -/
def IsCPWL (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  Continuous f ∧
    ∃ (m : ℕ) (g : Fin m → AffineMap' n 1),
      ∀ x : Fin n → ℝ, ∃ i : Fin m, ∀ᶠ y in nhds x, f y = (g i).apply y 0

/-- `CPWL n` is the space of continuous piecewise linear functions `ℝ^n → ℝ`. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) := { f | IsCPWL n f }

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from the paper, as a number of hidden layers. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent035

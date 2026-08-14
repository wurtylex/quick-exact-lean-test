import Mathlib

namespace Agent096

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network
Expressivity: Subdividing the Simplex"):

  For n ≥ 3,  CPWL_n = ReLU_{n, ⌈log_3 (n-1)⌉ + 1}.

## Modelling choices

* Vectors `ℝ^n` are encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is a pair `(A, c)` of a matrix and a
  bias vector, applied as `x ↦ A.mulVec x + c` (`AffMap`).
* A ReLU network with `k` hidden layers and input/output dimensions `a`, `b`
  is encoded as an inductively-defined "typed list" `ReLUNet a b k` of `k + 1`
  affine maps, chained together with a componentwise ReLU after every layer
  except the last, matching the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper.
* `ReLUn n k` is read as *at most* `k` hidden layers (the union over
  `k' ≤ k` of functions computed by some `k'`-hidden-layer network). This is
  the standard convention: it makes `ReLUn n` monotone in `k`
  (`ReLUn n k ⊆ ReLUn n (k+1)`, since any network can be padded with extra
  layers), which is implicitly needed for statements like Theorem 2 to be
  meaningful as an equality at a *specific* depth bound, rather than merely
  the smallest depth at which equality first occurs.
* `CPWL n` is defined honestly as: `f` is continuous, and there is a finite
  family of affine functions such that every point has a neighborhood on
  which `f` coincides with one of them (a genuine local-affine-pieces
  condition, not "representable by a ReLU network" and not a global
  max-of-affine normal form).
* The depth bound `⌈log_3 (n - 1)⌉ + 1` is encoded with `Real.logb 3` and
  `Nat.ceil` (`⌈·⌉₊`), applied to the real number `(n : ℝ) - 1`.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^n`. -/
def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given by a matrix `A` and bias `c`,
computing `x ↦ A * x + c`. -/
structure AffMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def AffMap.eval {a b : ℕ} (T : AffMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- A ReLU network with input dimension `a`, output dimension `b`, and `k`
hidden layers, encoded as a chain of `k + 1` affine maps. `last T` is the
final (output) affine transformation with no ReLU applied afterwards;
`step T rest` prepends an affine transformation followed by a ReLU. -/
inductive ReLUNet : ℕ → ℕ → ℕ → Type
  | last {a b : ℕ} (T : AffMap a b) : ReLUNet a b 0
  | step {a b c k : ℕ} (T : AffMap a b) (rest : ReLUNet b c k) : ReLUNet a c (k + 1)

/-- The function `ℝ^a → ℝ^b` computed by a ReLU network, i.e. the alternating
composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`. -/
def ReLUNet.eval {a b k : ℕ} (N : ReLUNet a b k) (x : Fin a → ℝ) : Fin b → ℝ :=
  match N with
  | .last T => T.eval x
  | .step T rest => rest.eval (reluVec (T.eval x))

/-- `f : ℝ^n → ℝ` is computed by *some* ReLU network with *exactly* `k`
hidden layers. -/
def NetComputesExact (n k : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ N : ReLUNet n 1 k, ∀ x : Fin n → ℝ, f x = N.eval x 0

/-- `ReLUn n k`: the CPWL functions `ℝ^n → ℝ` representable by a ReLU network
with *at most* `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, NetComputesExact n k' f }

/-- `CPWL n`: the continuous, piecewise-linear functions `ℝ^n → ℝ`. A
function is CPWL if it is continuous and there is a finite family of affine
functions such that every point of `ℝ^n` has a neighborhood on which `f`
agrees with one member of the family. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (g : Fin m → AffMap n 1),
          ∀ x : Fin n → ℝ, ∃ i : Fin m, ∀ᶠ y in nhds x, f y = (g i).eval y 0 }

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from the paper, as a natural
number: `Nat.ceil` of the real logarithm base `3` of `(n : ℝ) - 1`, plus
one hidden layer accounting for the "+1" in "⌈log_3(n-1)⌉ + 1". -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 : ∀ n : ℕ, n ≥ 3 → CPWL n = ReLUn n (depthBound n) := sorry

end Agent096

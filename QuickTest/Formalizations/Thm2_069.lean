import Mathlib

namespace Agent069

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely as `x ↦ A * x + c`. -/
structure AffineMap' (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def AffineMap'.apply {a b : ℕ} (T : AffineMap' a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/--
A ReLU network from `ℝ^a` to `ℝ^b` with `k` hidden layers, encoded as the alternating
composition of `k + 1` affine transformations `T^(1), ..., T^(k+1)` with a ReLU applied
componentwise after each of the first `k` of them, and no ReLU after the last one. This
matches the definition of "depth `k + 1`" / "`k` hidden layers" from Section 1 of the
paper: `ReLUNet a b 0` is a single affine map (depth 1, 0 hidden layers), and
`ReLUNet.cons T rest` prepends one affine map `T` followed by a ReLU to a network `rest`
with one fewer hidden layer than the whole.
-/
inductive ReLUNet : ℕ → ℕ → ℕ → Type
  | last {a b : ℕ} (T : AffineMap' a b) : ReLUNet a b 0
  | cons {a b c k : ℕ} (T : AffineMap' a b) (rest : ReLUNet b c k) : ReLUNet a c (k + 1)

/-- The function `ℝ^a → ℝ^b` computed by a ReLU network. -/
def ReLUNet.eval : {a b k : ℕ} → ReLUNet a b k → (Fin a → ℝ) → (Fin b → ℝ)
  | _, _, _, ReLUNet.last T, x => T.apply x
  | _, _, _, ReLUNet.cons T rest, x => rest.eval (reluVec (T.apply x))

/--
`ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers (rather than *exactly* `k`). We choose "at most" because
the classes are monotone in `k`: a network with `k` hidden layers can always be padded
to `k + 1` hidden layers computing the same function, e.g. by widening a layer with an
extra pair of neurons computing `relu(x)` and `relu(-x)` for a coordinate `x` and having
the next affine map recombine them as `relu(x) - relu(-x) = x` before continuing as
before. Under the "exactly `k`" reading, `ReLUn n k` and `ReLUn n (k+1)` need not be
comparable and the set equality in Theorem 2 would generally fail; under "at most `k`"
the theorem correctly expresses that `⌈log_3(n-1)⌉ + 1` hidden layers are both
necessary and sufficient to represent every function in `CPWL_n`.
-/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, ∃ net : ReLUNet n 1 k', ∀ x, f x = net.eval x 0}

/-- An affine function `ℝ^n → ℝ`, i.e. `x ↦ a ⬝ x + b`. -/
def IsAffineFunc {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x, f x = (∑ i, a i * x i) + b

/--
`CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: those that are
continuous and, near every point, agree with one of finitely many affine functions. This
is a genuine piecewise-linearity condition (local agreement with a finite family of
affine pieces), not a statement about ReLU-representability or a max-of-affine normal
form.
-/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ), (∀ i, IsAffineFunc (g i)) ∧
      ∀ x, ∃ i, ∀ᶠ y in nhds x, f y = g i y}

/-- The depth bound `⌈log_3(n-1)⌉ + 1` appearing in Theorem 2. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉+1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent069

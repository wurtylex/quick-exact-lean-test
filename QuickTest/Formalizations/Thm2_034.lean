import Mathlib

namespace Agent034

/-! ### Basic building blocks -/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^n`, encoded as `Fin n → ℝ`. -/
def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix `A` and a
translation vector `c`, acting as `x ↦ A * x + c`. -/
structure AffineMapRB (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def AffineMapRB.eval {a b : ℕ} (T : AffineMapRB a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, T.A i j * x j) + T.c i

/-- A function `ℝ^n → ℝ` is *affine* if it has the form `x ↦ ⟨w, x⟩ + b`. -/
def IsAffineFun {n : ℕ} (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (w : Fin n → ℝ) (b : ℝ), ∀ x, g x = (∑ i, w i * x i) + b

/-! ### ReLU networks -/

/-- `ReLUNet a b k` is (the data of) a ReLU network with input dimension `a`, output
dimension `b`, and `k` hidden layers, i.e. `k + 1` affine transformations
`T^(1), …, T^(k+1) : ℝ^{n_0} → ℝ^{n_1} → ⋯ → ℝ^{n_{k+1}}` (with `n_0 = a`,
`n_{k+1} = b`) composed with `ReLU` in between:
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`.
The `zero` constructor is a single affine transformation (`0` hidden layers,
depth `1`); the `succ` constructor prepends one more affine transformation
`T : ℝ^a → ℝ^m` followed by a `ReLU`, then continues with a network with one
fewer hidden layer from `ℝ^m` to `ℝ^b`. -/
inductive ReLUNet : ℕ → ℕ → ℕ → Type
  | zero {a b : ℕ} (T : AffineMapRB a b) : ReLUNet a b 0
  | succ {a m b k : ℕ} (T : AffineMapRB a m) (rest : ReLUNet m b k) : ReLUNet a b (k + 1)

/-- The function `ℝ^a → ℝ^b` computed by a ReLU network, obtained by unfolding the
alternating composition `T^(k+1) ∘ ReLU ∘ ⋯ ∘ ReLU ∘ T^(1)`. -/
def ReLUNet.eval {a b k : ℕ} (net : ReLUNet a b k) (x : Fin a → ℝ) : Fin b → ℝ :=
  match net with
  | ReLUNet.zero T => T.eval x
  | ReLUNet.succ T rest => rest.eval (reluVec (T.eval x))

/-- `ReLUn n k`: the functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers (output dimension `1`).

**Modelling choice (exactly-`k` vs at-most-`k`).** We use "at most `k`" rather
than "exactly `k`". A ReLU network with `k` hidden layers can always be
converted into one with `k + 1` hidden layers computing the *same* function
(e.g. prepend an extra affine layer `T = (I, 0)` acting as the identity on
`ℝ^{n_1}`, followed by a `ReLU` that changes nothing once one more coordinate
is added and subtracted back out by the following affine map); consequently
`ReLU_{n,k}` is monotone increasing in `k` under this reading. This monotonicity
is essential for Theorem 2 to be a meaningful equality: `CPWL n` is the
increasing union `⋃ k, ReLU_{n,k}` (by the discussion after Theorem 1, *every*
CPWL function needs only finitely many layers), and Theorem 2 pins down the
exact number of layers `⌈log_3(n-1)⌉ + 1` at which this union has already
stabilized to all of `CPWL n`. Under an "exactly `k`" reading the two sides of
the theorem could easily be unequal simply because some CPWL functions need
strictly *fewer* than the stated number of layers, which is not the intended
content of the theorem. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, ∃ net : ReLUNet n 1 k', ∀ x, f x = net.eval x 0}

/-! ### CPWL functions -/

/-- A function `f : ℝ^n → ℝ` is CPWL if it is continuous and there is a finite
subdivision of `ℝ^n` into polyhedral pieces `P 0, …, P (m-1)` — each piece cut
out by finitely many affine inequalities `⟨w, x⟩ + b ≤ 0` — covering `ℝ^n`, on
each of which `f` agrees with some affine function. This is a genuine
"continuous and piecewise affine on a finite polyhedral complex" definition:
it is *not* the same as "continuous and expressible as a max of finitely many
affine functions" (which would trivialize / assume the ReLU representation
result), and it does *not* refer to ReLU networks at all. -/
def IsCPWL {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  Continuous f ∧
  ∃ (m : ℕ) (P : Fin m → Set (Fin n → ℝ)) (A : Fin m → ((Fin n → ℝ) → ℝ)),
    (⋃ i, P i) = Set.univ ∧
    (∀ i, ∃ (ι : ℕ) (w : Fin ι → Fin n → ℝ) (b : Fin ι → ℝ),
        P i = {x | ∀ j, (∑ l, w j l * x l) + b j ≤ 0}) ∧
    (∀ i, IsAffineFun (A i)) ∧
    (∀ i, ∀ x ∈ P i, f x = A i x)

/-- `CPWL n`: the set of continuous piecewise-linear functions `ℝ^n → ℝ`. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) := {f | IsCPWL f}

/-! ### The depth bound `⌈log_3(n - 1)⌉ + 1` -/

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from Theorem 2. We use the genuine real
logarithm `Real.logb 3` together with `Nat.ceil` (notation `⌈·⌉₊`), which for a
nonnegative real argument computes exactly the mathematical ceiling; for
`n ≥ 3` we have `(n : ℝ) - 1 ≥ 2 > 0`, so this is well-behaved. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-! ### Theorem 2 -/

/-- **Theorem 2.** For `n ≥ 3`,
`CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`,
i.e. the continuous piecewise-linear functions on `ℝ^n` are exactly those
representable by a ReLU network with at most `⌈log_3(n-1)⌉ + 1` hidden layers. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent034

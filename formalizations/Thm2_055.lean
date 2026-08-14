import Mathlib

namespace Agent055

/-- ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on vectors, encoding `ℝ^m` as `Fin m → ℝ`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias
vector, in the style `x ↦ A * x + c`. -/
structure AffMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation: `x ↦ A * x + c`. -/
def AffMap.eval {a b : ℕ} (T : AffMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, T.A i j * x j) + T.c i

/-- A scalar-valued function `ℝ^n → ℝ` is affine if it has the form `x ↦ a ⬝ x + b`
for some fixed vector `a` and scalar `b`. -/
def IsAffineFun {n : ℕ} (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x, g x = (∑ j, a j * x j) + b

/--
`ComputedByReLUNet n k f` means that `f : ℝ^n → ℝ` is computed by a ReLU network with
*exactly* `k` hidden layers, i.e. by the alternating composition
`T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}`
of `k + 1` affine transformations `T^{(1)}, …, T^{(k+1)}` (with `ReLU` applied
componentwise between consecutive affine transformations), as in the paper's
definition of a ReLU network of depth `k + 1`. The base case `k = 0` (depth `1`,
no hidden layers) is a single affine transformation `ℝ^n → ℝ`, with no ReLU applied.
The recursive case peels off the first affine transformation `T^{(1)} : ℝ^n → ℝ^m`,
applies `ReLU` componentwise, and requires the remainder to be computed by a network
with `k` hidden layers on the intermediate dimension `m`.
-/
def ComputedByReLUNet : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => IsAffineFun f
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : AffMap n m) (g : (Fin m → ℝ) → ℝ),
        ComputedByReLUNet m k g ∧ ∀ x, f x = g (reluVec (T.eval x))

/--
`ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers. We choose the "at most" reading: a network with `j`
hidden layers can always be padded to `j + 1` hidden layers computing the same
function (insert an extra affine transformation that is the identity, preceded by
`ReLU`, using the identity `x = ReLU(x) - ReLU(-x)`), so the exactly-`j` classes
for `j ≤ k` are nested increasingly in `j` and their union is the natural notion of
"representable with `k` hidden layers available", matching the depth-hierarchy
statement of Theorem 2.
-/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ j ≤ k, ComputedByReLUNet n j f}

/--
`CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: those
functions that are continuous, and additionally, at every point, locally agree with
one of finitely many affine functions drawn from a single fixed finite family. This
is a genuine piecewise-linearity condition (finitely many affine "pieces" covering
`ℝ^n`, glued continuously), not a definition in terms of ReLU networks and not a
max-of-affine normal form.
-/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
       ∃ (m : ℕ) (g : Fin m → ((Fin n → ℝ) → ℝ)), (∀ i, IsAffineFun (g i)) ∧
         ∀ x : Fin n → ℝ, ∃ i, ∃ U ∈ nhds x, Set.EqOn f (g i) U}

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so that
`n - 1 ≥ 2`, as a natural number before casting to `ℝ`). -/
def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n - 1 : ℕ) : ℝ)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 : ∀ n : ℕ, n ≥ 3 → CPWL n = ReLUn n (depthBound n) := sorry

end Agent055

import Mathlib

namespace Agent012

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):  for `n ≥ 3`,  `CPWL n = ReLUn n (⌈log₃(n-1)⌉ + 1)`.

## Modelling choices

* Vectors `ℝ^n` are encoded as `Fin n → ℝ`.
* An affine map `ℝ^a → ℝ^b` is encoded concretely as a pair `(A, bias)` with
  `A : Matrix (Fin b) (Fin a) ℝ` and `bias : Fin b → ℝ`, evaluated as
  `x ↦ A.mulVec x + bias`.
* "Computed by a network with exactly `k` hidden layers" is defined by recursion on
  `k`: for `k = 0` the function itself must be affine (this is the single affine map
  `T^(1) : ℝ^n → ℝ`, i.e. depth 1, 0 hidden layers); for `k + 1`, `f` factors as
  `g ∘ reluVec ∘ (affine map ℝ^n → ℝ^m)` where `g` is computed with `k` hidden layers
  on `ℝ^m`, for some intermediate width `m`. Unwinding the recursion recovers exactly
  the alternating composition `T^(k+1) ∘ ReLU ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper.
* `ReLUn n k` is taken to mean *at most* `k` hidden layers (`∃ j ≤ k, …`), not
  *exactly* `k`. This is the reading under which Theorem 2 can be true: `CPWL n`
  contains affine functions (0 hidden layers), which must still lie in
  `ReLUn n (⌈log₃(n-1)⌉+1)` for the stated equality of sets to hold, so the class at
  depth `k` must be closed under "using fewer than `k` hidden layers".
* `CPWL n` is defined as: `f` is continuous, and there is a *finite family* of affine
  functions such that every point `x` has a neighbourhood on which `f` agrees with one
  member of the family. This is a genuine local piecewise-linearity condition; it is
  neither "representable by a ReLU network" nor a global max-of-affine-functions normal
  form.
* The depth bound is `⌈Real.logb 3 (n - 1)⌉₊ + 1`, using the real logarithm and
  `Nat.ceil`, matching the paper's `⌈log₃(n−1)⌉ + 1` literally.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine function `ℝ^n → ℝ` (a single linear functional plus a constant). -/
def IsAffine {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ a : Fin n → ℝ, ∃ b : ℝ, ∀ x : Fin n → ℝ, f x = (∑ i, a i * x i) + b

/--
`IsReLUNetExact n k f` means `f : ℝ^n → ℝ` is computed by a ReLU network with input
dimension `n` and **exactly** `k` hidden layers, i.e. by an alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations
`T^(i) : ℝ^{n_{i-1}} → ℝ^{n_i}` (with `n_0 = n`, `n_{k+1} = 1`) and componentwise ReLU.

The recursion peels off the first affine map `T^(1) : ℝ^n → ℝ^m` together with the
following ReLU; the remainder of the network is a `k`-hidden-layer network on `ℝ^m`.
-/
def IsReLUNetExact : (n : ℕ) → (k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => IsAffine f
  | n, (k + 1), f =>
      ∃ m : ℕ, ∃ A : Matrix (Fin m) (Fin n) ℝ, ∃ bias : Fin m → ℝ,
        ∃ g : (Fin m → ℝ) → ℝ,
          IsReLUNetExact m k g ∧
          ∀ x : Fin n → ℝ, f x = g (reluVec (A.mulVec x + bias))

/--
`ReLUn n k`: the CPWL functions `ℝ^n → ℝ` representable by a ReLU network with
**at most** `k` hidden layers. (See the module docstring for why "at most", rather
than "exactly", is the reading that makes Theorem 2 a true statement.)
-/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ j ≤ k, IsReLUNetExact n j f }

/--
`CPWL n`: continuous, piecewise-linear functions `ℝ^n → ℝ`, i.e. continuous functions
that locally, near every point, agree with one of finitely many affine functions.
-/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (g : Fin m → ((Fin n → ℝ) → ℝ)),
          (∀ i, IsAffine (g i)) ∧
          ∀ x : Fin n → ℝ, ∃ i, Filter.EventuallyEq (nhds x) f (g i) }

/-- The depth bound `⌈log₃(n − 1)⌉ + 1` from the paper, `n − 1` cast to `ℝ`. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log₃(n−1)⌉+1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent012

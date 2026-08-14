import Mathlib

namespace Agent004

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):  for `n ≥ 3`,  `CPWL n = ReLUn n (⌈log_3 (n-1)⌉ + 1)`.

## Modelling choices

* Vectors `ℝ^m` are encoded as `Fin m → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is modelled concretely as `x ↦ A.mulVec x + c`
  for a matrix `A` and a translation vector `c` (structure `AffMap`).
* A ReLU network with `k` hidden layers, input dimension `n` and output dimension `1`
  is modelled as an inductive family `ReLUNet n k`: either a single affine map
  `n → 1` (the `k = 0` case, i.e. depth-1 network, no hidden layer), or an affine map
  `n → m` followed by componentwise ReLU and then a network with `k` further hidden
  layers on the resulting `m`-dimensional space (the `k + 1` case). This is literally
  the alternating composition `T^(k+1) ∘ ReLU ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper.
* `ReLUn n k` is taken to be the functions representable with **at most** `k` hidden
  layers (`∃ j ≤ k`), not exactly `k`. This is the standard reading in this literature:
  any network with `j` hidden layers can be simulated with `j' ≥ j` hidden layers (pad
  with extra affine+ReLU layers implementing the identity via `relu(x) - relu(-x) = x`
  on each coordinate), so the two readings describe the same monotone family of sets,
  and only the "at most" reading makes an equality like Theorem 2 meaningful as a
  statement about the *minimal* sufficient depth.
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of affine
  functionals `g_1, …, g_m : ℝ^n → ℝ` such that every point `x` has a neighbourhood on
  which `f` coincides with some `g_i`. This is a genuine piecewise-linearity condition
  (finitely many affine pieces glued continuously), not a "representable by a ReLU
  network" tautology and not a max-of-affine normal form.
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded using `Real.logb 3` and `Nat.ceil`.
-/

/-- The ReLU activation function on `ℝ`. -/
noncomputable def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector `ℝ^m`. -/
noncomputable def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ :=
  fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix `A` and a
translation vector `c`, computing `x ↦ A * x + c`. -/
structure AffMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
noncomputable def AffMap.eval {a b : ℕ} (T : AffMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- An affine *functional* `ℝ^n → ℝ`, i.e. `x ↦ ⟨a, x⟩ + c`. Used to describe the
"pieces" of a CPWL function. -/
structure AffFunctional (n : ℕ) where
  a : Fin n → ℝ
  c : ℝ

/-- Evaluation of an affine functional. -/
noncomputable def AffFunctional.eval {n : ℕ} (g : AffFunctional n) (x : Fin n → ℝ) : ℝ :=
  (∑ i, g.a i * x i) + g.c

/-- A ReLU network with input dimension `n` and `k` hidden layers, computing a
real-valued function `ℝ^n → ℝ`. This is literally the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper:

* `last T` is the base case `k = 0`: a single affine map `T^(1) : ℝ^n → ℝ` with *no*
  ReLU applied afterwards (a depth-1 network, i.e. `0` hidden layers).
* `step T rest` prepends one affine map `T : ℝ^n → ℝ^m` followed by a componentwise
  ReLU (this is one hidden layer of width `m`), then continues with a `k`-hidden-layer
  network `rest` on the resulting `m`-dimensional space, for a total of `k + 1` hidden
  layers. -/
inductive ReLUNet : (n : ℕ) → (k : ℕ) → Type where
  | last {n : ℕ} (T : AffMap n 1) : ReLUNet n 0
  | step {n m k : ℕ} (T : AffMap n m) (rest : ReLUNet m k) : ReLUNet n (k + 1)

/-- The function `ℝ^n → ℝ` computed by a ReLU network. -/
noncomputable def ReLUNet.eval : {n k : ℕ} → ReLUNet n k → (Fin n → ℝ) → ℝ
  | _, _, ReLUNet.last T, x => T.eval x 0
  | _, _, ReLUNet.step T rest, x => rest.eval (reluVec (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
**at most** `k` hidden layers (see the discussion above for why "at most" rather than
"exactly" is the right reading here). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ j ≤ k, ∃ net : ReLUNet n j, f = net.eval }

/-- `CPWL n` is the set of continuous, piecewise-linear (in the genuine sense: finitely
many affine pieces glued continuously) functions `ℝ^n → ℝ`. A function `f` belongs to
`CPWL n` if it is continuous and there is a *finite* family of affine functionals such
that every point has a neighbourhood on which `f` agrees with one member of the
family. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (g : Fin m → AffFunctional n),
          ∀ x : Fin n → ℝ, ∃ i : Fin m, ∀ᶠ y in nhds x, f y = (g i).eval y }

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from Theorem 2, as a natural number. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL n = ReLUn n (⌈log_3(n-1)⌉ + 1)`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent004

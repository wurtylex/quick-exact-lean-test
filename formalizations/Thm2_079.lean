import Mathlib

namespace Agent079

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

"For n ≥ 3, we have CPWL_n = ReLU_{n, ⌈log_3(n−1)⌉ + 1}."

## Modelling choices (see final summary as well)

* Vectors `ℝ^n` are modelled as `Fin n → ℝ`.
* A ReLU network with `k` hidden layers is modelled as an inductive family
  `ReLUNet n k` of "layered" affine transformations with `ReLU` applied
  componentwise after every layer except the final (output) one.
* `ReLUn n k` is taken to mean *at most* `k` hidden layers (i.e. we existentially
  quantify over `k' ≤ k`). This is the reading under which `ReLUn n k` is monotone
  in `k` (adding more layers never removes representable functions, since one can
  always pad with an extra affine layer), which is the natural reading making the
  set-equality of Theorem 2 meaningful: every CPWL function needs *at most* the
  stated number of layers, and everything representable with at most that many
  layers is CPWL.
* `CPWL n` is defined honestly as: `f` is continuous, and there is a *finite*
  family of affine functions such that `f` locally agrees with one member of the
  family at every point (a genuine local-affine-piece / polyhedral-subdivision
  style definition), not as "representable by a ReLU network" and not as a
  max-of-affine normal form.
* The depth bound `⌈log_3(n−1)⌉ + 1` is encoded with the real logarithm
  `Real.logb 3` and `Nat.ceil` (`⌈·⌉₊`).
-/

/-- The scalar ReLU function `x ↦ max 0 x`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `Fin n → ℝ`. -/
def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a
bias vector: `x ↦ A * x + c`. -/
structure AffineTransform (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def AffineTransform.eval {a b : ℕ} (T : AffineTransform a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- A `k`-hidden-layer ReLU network with input dimension `n` and output
dimension `1`, presented as an alternating stack of affine transformations and
componentwise ReLUs:

`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`.

`ReLUNet.output` is the final affine map `T^(k+1) : ℝ^n → ℝ` (no hidden layers
left), and `ReLUNet.layer` prepends one more affine map `T^(1) : ℝ^n → ℝ^m`
followed by a componentwise ReLU, then continues with a `k`-hidden-layer network
on `ℝ^m`. -/
inductive ReLUNet : ℕ → ℕ → Type
  | output (n : ℕ) (T : AffineTransform n 1) : ReLUNet n 0
  | layer (n m k : ℕ) (T : AffineTransform n m) (rest : ReLUNet m k) : ReLUNet n (k + 1)

/-- The real-valued function on `ℝ^n` computed by a ReLU network. -/
def ReLUNet.eval : {n k : ℕ} → ReLUNet n k → (Fin n → ℝ) → ℝ
  | _, _, ReLUNet.output _ T, x => T.eval x ⟨0, Nat.one_pos⟩
  | _, _, ReLUNet.layer _ _ _ T rest, x => ReLUNet.eval rest (reluVec (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU
network with *at most* `k` hidden layers (see the discussion at the top of the
file for why "at most" rather than "exactly" is the appropriate reading here). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, ∃ net : ReLUNet n k', ∀ x, f x = net.eval x }

/-- A function `ℝ^n → ℝ` is affine if it has the form `x ↦ ⟨a, x⟩ + b`. -/
def IsAffine (n : ℕ) (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x, g x = (∑ i, a i * x i) + b

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`:
those functions that are continuous and that, at every point, locally agree
with one member of some fixed *finite* family of affine functions. This is a
genuine polyhedral-subdivision-style definition, not a max-of-affine normal
form and not "representable by a ReLU network". -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
      ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ),
        (∀ i, IsAffine n (g i)) ∧
        ∀ x : Fin n → ℝ, ∃ i : Fin m, ∃ ε > 0, ∀ y, dist y x < ε → f y = g i y }

/-- The depth bound `⌈log_3(n − 1)⌉ + 1` from the theorem statement, using the
real logarithm to base 3 and `Nat.ceil`. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n−1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent079

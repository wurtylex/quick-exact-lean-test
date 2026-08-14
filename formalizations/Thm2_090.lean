import Mathlib

namespace Agent090

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We encode `ℝ^n` as `Fin n → ℝ`.

* A ReLU network with `k` hidden layers is encoded as an inductive family `Network n k`,
  which is literally the data of `k + 1` affine transformations
  `T^(1) : ℝ^n → ℝ^{n_1}`, ..., `T^(k+1) : ℝ^{n_k} → ℝ^1`, together with the alternating
  composition with `ReLU` prescribed by the paper. `Network.eval` computes the represented
  function.
* `ReLUn n k` is the set of functions representable by *some* network with **at most** `k`
  hidden layers (see the note below on this modelling choice).
* `CPWL n` is defined mathematically, independently of ReLU networks: a function is CPWL if
  it is continuous and there is a finite polyhedral subdivision of `ℝ^n` (each piece cut out
  by finitely many affine inequalities) on each piece of which `f` agrees with some affine
  function.
* The depth bound `⌈log_3 (n-1)⌉ + 1` is encoded literally using `Real.logb` and `Nat.ceil`.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^n`. -/
def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely as `x ↦ A * x + c`. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def AffineMap.eval {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/--
A ReLU network `ℝ^n → ℝ` with exactly `k` hidden layers, encoded as the data of the
`k + 1` affine transformations `T^(1), ..., T^(k+1)` from the paper's definition, built up
recursively: `output T` is the depth-1 (0 hidden layer) network computing `T`, and
`cons T rest` prepends the affine map `T` followed by a `ReLU`, in front of a network `rest`
with one fewer hidden layer required.
-/
inductive Network : ℕ → ℕ → Type where
  | output {n : ℕ} (T : AffineMap n 1) : Network n 0
  | cons {n m k : ℕ} (T : AffineMap n m) (rest : Network m k) : Network n (k + 1)

/-- The function `ℝ^n → ℝ` computed by a ReLU network, via the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ... ∘ ReLU ∘ T^(1)`. -/
def Network.eval : {n k : ℕ} → Network n k → (Fin n → ℝ) → ℝ
  | _, _, .output T, x => T.eval x 0
  | _, _, .cons T rest, x => rest.eval (reluVec (T.eval x))

/--
`ReLUn n k`: the functions `ℝ^n → ℝ` representable by a ReLU network with **at most** `k`
hidden layers.

Modelling choice: we read "representable with `k` hidden layers" as "at most `k`" rather
than "exactly `k`". This is the reading under which Theorem 2 (an equality of sets) can be
true: a network with `j < k` hidden layers can always be padded to a network with exactly
`k` hidden layers computing the same function (e.g. by inserting extra affine layers that
implement the identity map, using `x = ReLU(x) - ReLU(-x)`), so the "exactly k" and
"at most k" families of representable functions coincide up to this padding, and taking
"at most k" is the natural, non-decreasing-in-`k` reading matching the paper's informal use
of `ReLU_{n,k}` as an increasing filtration of `CPWL_n`.
-/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ j ≤ k, ∃ N : Network n j, ∀ x, f x = N.eval x}

/-- An affine function `ℝ^n → ℝ`. -/
def IsAffine {n : ℕ} (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x, g x = (∑ i, a i * x i) + b

/-- A halfspace `{x | a ⬝ x ≤ b}` of `ℝ^n`. -/
structure Halfspace (n : ℕ) where
  a : Fin n → ℝ
  b : ℝ

/-- Membership of a point in a halfspace. -/
def Halfspace.mem {n : ℕ} (H : Halfspace n) (x : Fin n → ℝ) : Prop :=
  (∑ i, H.a i * x i) ≤ H.b

/-- A (closed convex) polyhedron of `ℝ^n`, given as a finite intersection of halfspaces. -/
abbrev Polyhedron (n : ℕ) := List (Halfspace n)

/-- Membership of a point in a polyhedron (intersection of its halfspaces). -/
def Polyhedron.mem {n : ℕ} (P : Polyhedron n) (x : Fin n → ℝ) : Prop :=
  ∀ H ∈ P, H.mem x

/--
`CPWL n`: the continuous, piecewise-linear functions `ℝ^n → ℝ`. A function `f` is CPWL if it
is continuous and there is a *finite* family of polyhedra `P 1, ..., P m` covering `ℝ^n`,
together with affine functions `g 1, ..., g m`, such that `f` agrees with `g j` on `P j` for
every `j`. This is a genuine geometric piecewise-linearity condition (a finite polyhedral
subdivision on each piece of which `f` is affine); it is *not* defined via ReLU-network
representability, and it is *not* stated as a max-of-affine-functions normal form.
-/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
        ∃ (m : ℕ) (P : Fin m → Polyhedron n) (g : Fin m → (Fin n → ℝ) → ℝ),
          (∀ j, IsAffine (g j)) ∧
          (∀ x : Fin n → ℝ, ∃ j, (P j).mem x) ∧
          (∀ j, ∀ x, (P j).mem x → f x = g j x)}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, encoded literally with the real
logarithm to base 3 and the natural-number ceiling. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉+1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent090

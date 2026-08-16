import Mathlib

namespace Agent043

/-!
Formalization of Theorem 2 of arXiv:2505.14338
("Better Neural Network Expressivity: Subdividing the Simplex").

Theorem 2. For n ≥ 3, CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}.

## Modelling choices (see summary at the end of the file too)

* Vectors `ℝ^n` are encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is encoded concretely as a matrix/vector pair
  `(A, c)` acting by `x ↦ A.mulVec x + c`.
* A ReLU network with `k` hidden layers is encoded *recursively* on `k`: with `0` hidden
  layers it is a single affine map; with `k+1` hidden layers it is an affine map into some
  intermediate width `p`, followed by (componentwise) ReLU, followed by a network with `k`
  hidden layers from `p` to the output. This exactly mirrors the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` built up starting from the input side.
* `ReLUn n k` is taken to mean representable with **at most** `k` hidden layers (the
  standard convention in the expressivity literature, since padding a network with extra
  affine identity-like layers costs no expressive power and makes the classes monotone in
  `k`; this is also the reading under which the theorem, an *equality* of sets, is the
  natural one to state).
* `CPWL n` is defined honestly as: `f` is continuous, and there is a *finite* family of
  affine functions such that every point of `ℝ^n` has a neighbourhood on which `f`
  coincides with one member of the family (a genuine local piecewise-affine condition, not
  "representable by a ReLU network" and not a global max-of-affine normal form).
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded with the real logarithm `Real.logb` and
  `Nat.ceil`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias vector. -/
structure AffineT (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- The function computed by an affine transformation. -/
def AffineT.eval {a b : ℕ} (T : AffineT a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/--
`NetworkComputes m k n f` means: the function `f : ℝ^n → ℝ^m` is computed by a ReLU network
with input dimension `n`, output dimension `m`, and exactly `k` hidden layers, i.e. `f` is
the alternating composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine
transformations with `k` interleaved componentwise applications of ReLU.

Recursion is on `k`:
* `k = 0`: the network is a single affine transformation `T^(1) : ℝ^n → ℝ^m` (no hidden
  layers, depth 1).
* `k + 1`: peel off the first affine transformation `T^(1) : ℝ^n → ℝ^p` (into some hidden
  width `p`) and the first ReLU, leaving a network with `k` hidden layers computing
  `ℝ^p → ℝ^m`.
-/
def NetworkComputes : (m k n : ℕ) → ((Fin n → ℝ) → (Fin m → ℝ)) → Prop
  | m, 0, n, f => ∃ T : AffineT n m, f = T.eval
  | m, k + 1, n, f =>
      ∃ (p : ℕ) (T : AffineT n p) (g : (Fin p → ℝ) → (Fin m → ℝ)),
        NetworkComputes m k p g ∧ f = fun x => g (reluVec (T.eval x))

/--
`ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with **at
most** `k` hidden layers (scalar output is encoded as output dimension `1`). This is the
standard "at most `k`" convention: the classes `ReLUn n k` are monotone increasing in `k`,
since one can always pad a network with more (trivial) layers without losing expressive
power.
-/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, NetworkComputes 1 k' n (fun x _ => f x) }

/--
`CPWL n` is the set of continuous piecewise-linear functions `ℝ^n → ℝ`: `f` is continuous,
and there is a finite family of affine functions (indexed by `Fin N`) such that every point
of `ℝ^n` has a neighbourhood on which `f` agrees with one member of the family.
-/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
      ∃ (N : ℕ) (A : Fin N → (Fin n → ℝ)) (c : Fin N → ℝ),
        ∀ x : Fin n → ℝ, ∃ r > 0, ∃ i : Fin N, ∀ y : Fin n → ℝ,
          dist y x < r → f y = (∑ j, A i j * y j) + c i }

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from Theorem 2, for `n ≥ 3`. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent043

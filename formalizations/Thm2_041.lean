import Mathlib

namespace Agent041

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):

  For n ≥ 3, CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}.

## Modelling choices

* Vectors `ℝ^m` are encoded as `Fin m → ℝ`.
* An affine map `ℝ^a → ℝ^b` is `x ↦ A.mulVec x + c` for a matrix `A` and a vector `c`
  (`IsAffineMap`). A scalar-valued affine map `ℝ^n → ℝ` is `x ↦ (∑ i, a i * x i) + c`
  (`IsAffineScalar`).
* `relu` is `max 0` on `ℝ`, and `reluVec` applies it componentwise.
* A ReLU network with `k` hidden layers computing a function `ℝ^m → ℝ^w` is captured by
  the recursive predicate `NetFunc k m w f`, mirroring the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`: the base case `k = 0` is a single affine
  map (`T^(1)`, no hidden layer), and the successor case appends one more affine map
  after componentwise ReLU on top of a `k`-hidden-layer network.
* `ReLUn n k` is the set of `ℝ^n → ℝ` functions representable with **at most** `k`
  hidden layers (existential over `k' ≤ k`). This is the standard reading of `ReLU_{n,k}`
  in this literature; note that thanks to the classical "identity emulation" trick
  (`x ↦ (relu x, relu (-x))` then `(u, v) ↦ u - v`), a network with exactly `k'` hidden
  layers can always be padded to exactly `k' + 1` hidden layers computing the same
  function, so the "exactly k" and "at most k" families are increasing and in fact
  coincide as far as the equality in Theorem 2 is concerned.
* `CPWL n` is the set of continuous functions `ℝ^n → ℝ` that, at every point, agree with
  one of finitely many globally-defined affine functions (a genuine finite-affine-pieces
  condition, not a max-of-affine normal form and not "representable by a ReLU network").
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded with `Real.logb 3` and `Nat.ceil`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector in `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- `f : ℝ^a → ℝ^b` is an affine transformation: `f x = A * x + c` for some matrix `A`
and vector `c`. -/
def IsAffineMap {a b : ℕ} (f : (Fin a → ℝ) → (Fin b → ℝ)) : Prop :=
  ∃ (A : Matrix (Fin b) (Fin a) ℝ) (c : Fin b → ℝ), ∀ x, f x = A.mulVec x + c

/-- `g : ℝ^n → ℝ` is affine: `g x = ⟨a, x⟩ + c` for some coefficient vector `a` and
constant `c`. -/
def IsAffineScalar {n : ℕ} (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (c : ℝ), ∀ x, g x = (∑ i, a i * x i) + c

/-- `NetFunc k m w f` holds when `f : ℝ^m → ℝ^w` is computed by a ReLU network with
exactly `k` hidden layers, i.e. `f` is the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations
`T^(1), …, T^(k+1)` with componentwise ReLU applied after each of the first `k` of
them. The input dimension `m` (= `n_0`) stays fixed through the recursion; the output
dimension `w` (= `n_k`) is the width of the last layer. -/
def NetFunc : (k : ℕ) → (m w : ℕ) → ((Fin m → ℝ) → (Fin w → ℝ)) → Prop
  | 0, _, _, f => IsAffineMap f
  | (k + 1), m, w, f =>
      ∃ (w' : ℕ) (g : (Fin m → ℝ) → (Fin w' → ℝ)) (T : (Fin w' → ℝ) → (Fin w → ℝ)),
        NetFunc k m w' g ∧ IsAffineMap T ∧ f = fun x => T (reluVec (g x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
at most `k` hidden layers (output dimension `n_{k+1} = 1`). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, ∃ F : (Fin n → ℝ) → (Fin 1 → ℝ), NetFunc k' n 1 F ∧ f = fun x => F x 0 }

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: those which
are continuous and, at every point, agree with one of finitely many globally-defined
affine functions. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ),
          (∀ j, IsAffineScalar (g j)) ∧ ∀ x, ∃ j, f x = g j x }

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so `n - 1 ≥ 2`). -/
def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n - 1 : ℕ) : ℝ)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent041

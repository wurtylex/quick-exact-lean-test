import Mathlib

namespace Agent029

/-
# Modelling choices

* Vectors `ℝ^m` are encoded as `Fin m → ℝ` for the *external* interface (inputs of the
  network, points of `CPWL n`), which is the natural type to match `CPWL n`,
  `ReLUn n k : Set ((Fin n → ℝ) → ℝ)`.

* Internally, the hidden/output representations flowing through a network are encoded
  as `ℕ → ℝ` (an ambient sequence type): the width of a layer is tracked as separate
  numerical data (`widths : Fin (k+2) → ℕ`) rather than baked into the *type* of the
  intermediate vector. This sidesteps painful dependent-type bookkeeping when composing
  layers of different widths, while still faithfully recording every width `n_0, ..., n_{k+1}`
  from the paper's definition, and every affine map `A * x + b` explicit as a matrix/bias
  pair together with the domain dimension it is evaluated at.

* An affine transformation `ℝ^a → ℝ^b` is given concretely by a matrix `A : ℕ → ℕ → ℝ`
  and bias `c : ℕ → ℝ` (only entries with row/col below `b`/`a` are semantically relevant),
  evaluated as `x ↦ c + A * x` where the matrix-vector product sums only over
  `Finset.range a` (the actual input dimension).

* `ReLUn n k` is defined as functions representable by a network with *exactly* `k`
  hidden layers (`k` is literally the structure's `Network n k` parameter). We do not
  additionally require "at most k": as is standard for ReLU networks, one can always pad
  a network computing a function with fewer than `k` hidden layers up to exactly `k`
  hidden layers without changing the represented function, so the "exactly k" and
  "at most k" readings of `ReLUn n k` coincide as sets; we take the definitionally
  simpler "exactly k" reading.

* `CPWL n` is defined the genuine way: `f` is continuous **and** there is a finite cover
  of `ℝ^n` by (closed, convex) polyhedra — each cut out by finitely many affine
  inequalities `⟨a_i, x⟩ ≤ b_i` — on each of which `f` agrees with some affine function.
  This is *not* the same as "f is a finite max of affine functions" (that special form
  only captures *convex* CPWL functions), and it is *not* "representable by some ReLU
  network" (that would make the theorem statement circular/trivial).

* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded directly via the real logarithm
  `Real.logb 3 (n - 1)` and `Nat.ceil` (`⌈·⌉₊`), avoiding any need to separately justify
  that some natural-number surrogate (e.g. `Nat.clog`) matches the intended real ceiling.
-/

noncomputable section

/-- The ReLU activation function on `ℝ`. -/
def relu (t : ℝ) : ℝ := max 0 t

/-- Componentwise ReLU on a `Fin m`-indexed vector. -/
def reluVec {m : ℕ} (v : Fin m → ℝ) : Fin m → ℝ := fun i => relu (v i)

/-- Componentwise ReLU on the ambient `ℕ`-indexed sequence type used internally to
represent the values flowing through the hidden layers of a network. -/
def reluSeq (v : ℕ → ℝ) : ℕ → ℝ := fun i => relu (v i)

/-- An affine transformation, given concretely by a matrix and a bias vector, both
represented as functions on `ℕ` (only the entries within the relevant domain/codomain
range are semantically used; this range is supplied separately at evaluation time,
see `Affine.eval`). This models an affine map `ℝ^a → ℝ^b` for whichever `a, b` it is
used with. -/
structure Affine where
  A : ℕ → ℕ → ℝ
  c : ℕ → ℝ

/-- Evaluate an affine transformation `x ↦ c + A * x`, where `a` is the (declared) input
dimension: the matrix-vector product only sums the first `a` coordinates of `x`. -/
def Affine.eval (T : Affine) (a : ℕ) (x : ℕ → ℝ) : ℕ → ℝ :=
  fun i => T.c i + ∑ j ∈ Finset.range a, T.A i j * x j

/-- A ReLU network with `n` inputs, `k` hidden layers, and a single real output, given
as in the paper by `k + 1` affine transformations `T^(1), ..., T^(k+1)` together with
the sequence of layer widths `n_0 = n, n_1, ..., n_k, n_{k+1} = 1`. -/
structure Network (n k : ℕ) where
  /-- The widths `n_0, n_1, ..., n_{k+1}` of all layers (input, hidden, output). -/
  widths : Fin (k + 2) → ℕ
  widths_zero : widths ⟨0, by omega⟩ = n
  widths_last : widths ⟨k + 1, by omega⟩ = 1
  /-- The `k + 1` affine transformations `T^(1), ..., T^(k+1)`. -/
  layers : Fin (k + 1) → Affine

/-- The forward pass of a network on an input `x`, i.e. the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ... ∘ ReLU ∘ T^(1)` applied to `x`, represented as an
`ℕ`-indexed sequence (of which only the first `N.widths (last index)` coordinates,
here just index `0` since the output width is `1`, are meaningful). ReLU is applied
after every layer except the final one. -/
def Network.forward {n k : ℕ} (N : Network n k) (x : Fin n → ℝ) : ℕ → ℝ :=
  (List.finRange (k + 1)).foldl
    (fun v i =>
      let out := (N.layers i).eval (N.widths i.castSucc) v
      if (i : ℕ) < k then reluSeq out else out)
    (fun j => if h : j < n then x ⟨j, h⟩ else 0)

/-- The real number computed by the network on input `x`. -/
def Network.output {n k : ℕ} (N : Network n k) (x : Fin n → ℝ) : ℝ := N.forward x 0

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` computed by some ReLU network with
`n` inputs and exactly `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ N : Network n k, ∀ x, f x = N.output x }

/-- A polyhedron in `ℝ^n`: the solution set of finitely many affine inequalities
`⟨a_i, x⟩ ≤ b_i`. -/
def IsPolyhedron {n : ℕ} (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (a : Fin m → (Fin n → ℝ)) (b : Fin m → ℝ),
    S = { x | ∀ i, (∑ j, a i j * x j) ≤ b i }

/-- `f` agrees with some affine function on the set `S`. -/
def IsAffineOn {n : ℕ} (f : (Fin n → ℝ) → ℝ) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (w : Fin n → ℝ) (c : ℝ), ∀ x ∈ S, f x = (∑ j, w j * x j) + c

/-- `CPWL n`: the continuous, piecewise-linear (affine) functions `ℝ^n → ℝ`. A function
is CPWL if it is continuous and there is a finite cover of `ℝ^n` by polyhedra, on each
of which `f` agrees with an affine function. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (P : Fin m → Set (Fin n → ℝ)),
          (∀ i, IsPolyhedron (P i)) ∧
          (⋃ i, P i) = Set.univ ∧
          (∀ i, IsAffineOn f (P i)) }

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from Theorem 2, encoded via the real logarithm
and `Nat.ceil`. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end

end Agent029

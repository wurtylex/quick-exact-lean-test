import Mathlib

namespace Agent088

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

  "For n ≥ 3, we have CPWL_n = ReLU_{n, ⌈log_3(n−1)⌉ + 1}."

## Modelling choices

* Vectors `ℝ^n` are modelled as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is modelled concretely as
  `x ↦ A *ᵥ x + c` for a matrix `A : Matrix (Fin b) (Fin a) ℝ` and a bias
  vector `c : Fin b → ℝ`, written out with an explicit sum.
* A ReLU network with `k` hidden layers computing `f : ℝ^n → ℝ` is modelled
  by recursion on `k`: with `0` hidden layers it is a single affine
  transformation `ℝ^n → ℝ`; with `k+1` hidden layers it is an affine
  transformation `ℝ^n → ℝ^m` (the first hidden layer, of *some* width `m`),
  followed by a component-wise ReLU, followed by a function computed by a
  `k`-hidden-layer network on `ℝ^m`. This directly encodes the alternating
  composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ... ∘ ReLU ∘ T^(1)` from the paper.
* `ReLUn n k` is taken to be the functions representable with **at most**
  `k` hidden layers (not exactly `k`). This is the standard reading in the
  literature and is the one under which `ReLUn n` is monotone in `k`
  (you can always pad a shallower network with extra identity-like hidden
  layers), which is what makes an equality with `CPWL n` at a single depth
  bound `⌈log_3(n-1)⌉+1` a meaningful "sufficiency + this suffices"
  statement rather than an accidental coincidence at one exact depth.
* `CPWL n` is defined mathematically (not via ReLU networks!) as: `f` is
  continuous, and there is a finite family of closed polyhedra (each cut
  out by finitely many affine inequalities) whose union is all of `ℝ^n`,
  on each of which `f` agrees with some affine function.
* The depth bound `⌈log_3 (n-1)⌉ + 1` is encoded using `Real.logb 3` and
  `Nat.ceil`, applied to the real number `(n : ℝ) - 1`.
-/

/-- The scalar ReLU function. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ :=
  fun i => relu (x i)

/-- The affine transformation `ℝ^a → ℝ^b` given by matrix `A` and bias `c`,
applied to `x`, written out explicitly as `(A x)_i = Σ_j A i j * x j + c i`. -/
def affineApply {a b : ℕ} (A : Matrix (Fin b) (Fin a) ℝ) (c : Fin b → ℝ)
    (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, A i j * x j) + c i

/-- `IsComputedByReLUNetwork n k f` says that `f : ℝ^n → ℝ` is computed by a
ReLU network with `k` hidden layers, i.e. by an alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ... ∘ ReLU ∘ T^(1)` of `k + 1` affine
transformations with componentwise ReLU in between, as in Section 1 of the
paper. Defined by recursion on `k`: the base case `k = 0` is a single
affine transformation `ℝ^n → ℝ` (i.e. `T^(1)`, with no hidden layers at
all); the successor case peels off the first affine transformation
`T^(1) : ℝ^n → ℝ^m` (to some hidden width `m`) and the following ReLU,
and requires the remainder to be computed by a `k`-hidden-layer network on
`ℝ^m`. -/
def IsComputedByReLUNetwork : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f =>
      ∃ (a : Fin n → ℝ) (b : ℝ), f = fun x => (∑ i, a i * x i) + b
  | n, (k + 1), f =>
      ∃ (m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ)
        (g : (Fin m → ℝ) → ℝ),
        IsComputedByReLUNetwork m k g ∧
          f = fun x => g (reluVec (affineApply A c x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU
network with **at most** `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, IsComputedByReLUNetwork n k' f}

/-- `f` agrees with some affine function on the set `S`. -/
def IsAffineOn (n : ℕ) (f : (Fin n → ℝ) → ℝ) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x ∈ S, f x = (∑ i, a i * x i) + b

/-- A (closed) polyhedron in `ℝ^n`: the solution set of finitely many affine
inequalities `⟨a_j, x⟩ ≤ b_j`. -/
def IsPolyhedron (n : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (a : Fin m → Fin n → ℝ) (b : Fin m → ℝ),
    S = {x | ∀ j, (∑ i, a j i * x i) ≤ b j}

/-- `CPWL n` is the space of continuous, piecewise-linear functions
`ℝ^n → ℝ`: `f` is continuous, and there is a finite family of polyhedra
covering `ℝ^n` on each of which `f` agrees with an affine function. This is
a genuine geometric/analytic definition, independent of ReLU networks. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (P : Fin m → Set (Fin n → ℝ)),
      (∀ j, IsPolyhedron n (P j)) ∧
      (⋃ j, P j) = Set.univ ∧
      (∀ j, IsAffineOn n f (P j))}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, for `n ≥ 3`
(so that `(n : ℝ) - 1 ≥ 2`). -/
def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent088

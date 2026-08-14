import Mathlib

namespace Agent032

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

"Better Neural Network Expressivity: Subdividing the Simplex"
(Bakaev, Brunck, Hertrich, Stade, Yehudayoff)

Theorem 2. For n ≥ 3, we have CPWL_n = ReLU_{n, ⌈log_3(n−1)⌉ + 1}.

We encode ℝ^n as `Fin n → ℝ`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a
translation vector: `x ↦ A * x + c`. -/
structure AffineMap' (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def AffineMap'.eval {a b : ℕ} (T : AffineMap' a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, T.A i j * x j) + T.c i

/-- `ReLUComputable n k f` means the function `f : ℝ^n → ℝ` is computed by a ReLU
network with input dimension `n` and exactly `k` hidden layers, i.e. by the alternating
composition

    T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)

of `k + 1` affine transformations `T^(1), …, T^(k+1)` with componentwise ReLU applied
after each of the first `k` of them. The recursion peels off the first affine map and
first ReLU application, reducing the number of hidden layers by one and (possibly)
changing the working dimension to some intermediate width `m` (the layer width `n_1` in
the paper's notation). The base case `k = 0` is a bare affine map `ℝ^n → ℝ`
(a depth-1 network with no hidden layers). -/
def ReLUComputable : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : AffineMap' n 1, ∀ x, f x = T.eval x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : AffineMap' n m) (g : (Fin m → ℝ) → ℝ),
        ReLUComputable m k g ∧ ∀ x, f x = g (reluVec (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network
with **at most** `k` hidden layers. (This is the standard reading of `ReLU_{n,k}` in the
expressivity literature: the classes are nested, `ReLU_{n,k} ⊆ ReLU_{n,k+1}`, since one
can always pad a shallower network with extra layers that behave like the identity, e.g.
via `id(x) = relu(x) - relu(-x)`. This monotone reading is also the one under which
Theorem 2, stated as a *set equality* `CPWL_n = ReLU_{n,K}`, is a sensible and true
statement: `ReLU_{n,K}` is exactly the depth at which the *whole* of `CPWL_n` is first
reached and it stays reached for all greater depths, matching the "exactly-K" reading of
`⌈log_3(n−1)⌉+1` for the growth of the sequence, while the class `ReLU_{n,K}` itself is
"at most K hidden layers".) -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, ReLUComputable n k' f}

/-- A subset of `ℝ^n` is a (closed) polyhedron if it is cut out by finitely many affine
inequalities `⟨a_j, x⟩ ≤ b_j`. -/
def IsPolyhedron {n : ℕ} (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ),
    S = {x | ∀ j, (∑ i, A j i * x i) ≤ b j}

/-- `f` agrees with a single affine function on the set `S`. -/
def IsAffineOn {n : ℕ} (f : (Fin n → ℝ) → ℝ) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (A : Fin n → ℝ) (c : ℝ), ∀ x ∈ S, f x = (∑ i, A i * x i) + c

/-- `CPWL n` is the set of continuous, piecewise linear functions `ℝ^n → ℝ`: those that
are continuous and admit a finite polyhedral subdivision of `ℝ^n` such that `f` is affine
on each polyhedron of the subdivision. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (ι : Type) (_ : Finite ι) (P : ι → Set (Fin n → ℝ)),
      (∀ i, IsPolyhedron (P i)) ∧ (⋃ i, P i) = Set.univ ∧ ∀ i, IsAffineOn f (P i)}

/-- The depth bound `⌈log_3(n − 1)⌉ + 1` from Theorem 2, using the real base-3
logarithm and the natural-number ceiling. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n−1)⌉+1}`. -/
theorem theorem2 : ∀ n : ℕ, n ≥ 3 → CPWL n = ReLUn n (depthBound n) := sorry

end Agent032

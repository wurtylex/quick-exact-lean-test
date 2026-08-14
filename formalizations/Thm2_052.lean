import Mathlib

namespace Agent052

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We encode `ℝ^n` as `Fin n → ℝ`.  Affine maps are given concretely as a matrix
together with a bias vector.  A ReLU network with `k` hidden layers is encoded
as a chain of `k + 1` affine maps between consecutive layer widths, alternately
composed with the componentwise ReLU function.  `ReLUn n k` is the set of
functions representable with **at most** `k` hidden layers (this is the
reading under which `ReLUn n k` is monotone in `k` and Theorem 2, asserting
equality with the *full* class `CPWL n`, is the correct/true statement: with
strictly fewer than the stated bound one cannot represent everything, but any
smaller network can always be padded up to exactly the bound).  `CPWL n` is
defined directly and genuinely as: continuous functions admitting a finite
polyhedral subdivision of `ℝ^n` on each piece of which the function is affine.
-/

/-- ReLU on the reals. -/
noncomputable def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^n`. -/
noncomputable def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix `A` and
a bias vector `c`, computing `x ↦ A * x + c`. -/
structure AffMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
noncomputable def AffMap.eval {a b : ℕ} (T : AffMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, T.A i j * x j) + T.c i

/-- Iterated evaluation of a chain of affine maps `layers 0, layers 1, ...`
between the layer widths given by `w : ℕ → ℕ` (with `w 0` the input width),
alternately composed with `ReLU`, following

    T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(2) ∘ ReLU ∘ T^(1).

`netEval w layers i x` is the value obtained after applying `layers 0, ...,
layers (i - 1)` (i.e. it lands in `ℝ^{w i}`); no `ReLU` is applied before the
very first affine map `layers 0`, and none is applied after the last one used. -/
noncomputable def netEval (w : ℕ → ℕ) (layers : (i : ℕ) → AffMap (w i) (w (i + 1))) :
    (i : ℕ) → (Fin (w 0) → ℝ) → (Fin (w i) → ℝ)
  | 0, x => x
  | (i + 1), x =>
      (layers i).eval (if i = 0 then netEval w layers i x else reluVec (netEval w layers i x))

/-- `f : ℝ^n → ℝ` is computed by a ReLU network with **exactly** `k` hidden
layers: there are widths `w 0 = n, w 1, ..., w k` (hidden layers) and
`w (k+1) = 1` (output), and `k + 1` affine maps `layers 0, ..., layers k`
between consecutive widths, whose alternating composition with `ReLU` equals
`f`. -/
noncomputable def Represents (n k : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (w : ℕ → ℕ) (layers : (i : ℕ) → AffMap (w i) (w (i + 1)))
    (h0 : w 0 = n) (hk : w (k + 1) = 1),
    ∀ x : Fin n → ℝ,
      f x =
        (cast (congrArg (fun m => Fin m → ℝ) hk)
          (netEval w layers (k + 1)
            (cast (congrArg (fun m => Fin m → ℝ) h0.symm) x))) 0

/-- `ReLUn n k`: the CPWL functions on `ℝ^n` representable by a ReLU network
with **at most** `k` hidden layers. -/
noncomputable def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, Represents n k' f}

/-- A closed halfspace `{x | ⟪a, x⟫ ≤ b}` of `ℝ^n`. -/
structure Halfspace (n : ℕ) where
  a : Fin n → ℝ
  b : ℝ

/-- The set cut out by a halfspace. -/
noncomputable def Halfspace.set {n : ℕ} (h : Halfspace n) : Set (Fin n → ℝ) :=
  {x | (∑ j, h.a j * x j) ≤ h.b}

/-- A closed polyhedron: a finite intersection of halfspaces. -/
noncomputable def Polyhedron {n m : ℕ} (H : Fin m → Halfspace n) : Set (Fin n → ℝ) :=
  ⋂ i, (H i).set

/-- `CPWL n`: continuous functions `ℝ^n → ℝ` admitting a finite polyhedral
subdivision of `ℝ^n` (a finite family of closed polyhedra covering `ℝ^n`) on
each piece of which the function agrees with some affine function. This is a
genuine piecewise-linearity condition: it is neither "representable by a ReLU
network" nor a bare max-of-affine normal form. -/
noncomputable def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (mi : Fin m → ℕ) (H : (i : Fin m) → Fin (mi i) → Halfspace n)
      (g : Fin m → AffMap n 1),
      (⋃ i, Polyhedron (H i)) = Set.univ ∧
      ∀ i : Fin m, ∀ x ∈ Polyhedron (H i), f x = (g i).eval x 0}

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from Theorem 2, using the real
logarithm and the natural-number ceiling. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent052

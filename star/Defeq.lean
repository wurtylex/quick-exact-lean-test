import Mathlib
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

open Lean Elab Meta in
def dfCheck (ids : List String) : TermElabM Unit := do
  for i in ids do
    let mut row := ""
    for d in ["CPWL", "ReLUn", "depthBound"] do
      let a := ("Agent" ++ i ++ "." ++ d).toName
      let r := ("Ref." ++ d).toName
      let ok ←
        if ((← getEnv).find? a).isSome && ((← getEnv).find? r).isSome then
          try
            withOptions (fun o => o.setNat `maxHeartbeats 20000) <|
              Core.withCurrHeartbeats <| withNewMCtxDepth <|
                isDefEq (.const a []) (.const r [])
          catch _ => pure false
        else pure false
      row := row ++ " " ++ d ++ "=" ++ toString ok
    logInfo m!"@@DF {i}{row}"



/-!
# Reference formalization of Theorem 2

*Better Neural Network Expressivity: Subdividing the Simplex*, arXiv:2505.14338,
Bakaev–Brunck–Hertrich–Stade–Yehudayoff.

> **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log₃(n−1)⌉+1}`.

This is the hub of the star comparison: every sampled formalization is compared
against *this* file rather than against its neighbour, so that two agents which
both match it are equal to each other for free.

Two deliberate choices, both matching the paper:

* `ReLUn n k` is **at most `k`** hidden layers.  (The "exactly `k`" reading
  denotes the same set — pad with `x = relu x − relu (−x)` — but only as a
  theorem, not definitionally.)
* `CPWL n` is the honest piecewise-linearity condition: continuous, plus a
  finite polyhedral cover of `ℝⁿ` on each piece of which `f` agrees with an
  affine function.  It is *not* phrased as "representable by a ReLU network"
  (which would make Theorem 2 a tautology) and not as a max-of-affine normal
  form (which would assume the hard direction).
-/

namespace Ref

/-- The ReLU activation on `ℝ`. -/
noncomputable def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝⁿ`, encoded as `Fin n → ℝ`. -/
noncomputable def reluVec {n : ℕ} (v : Fin n → ℝ) : Fin n → ℝ := fun i => relu (v i)

/-- An affine map `ℝ^a → ℝ^b`, as a matrix together with a translation. -/
structure Aff (a b : ℕ) where
  M : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- `x ↦ M x + c`. -/
def Aff.eval {a b : ℕ} (T : Aff a b) (x : Fin a → ℝ) : Fin b → ℝ := T.M.mulVec x + T.c

/-- `ComputedBy n k f` : `f : ℝⁿ → ℝ` is computed by a ReLU network with
**exactly** `k` hidden layers, i.e. the alternating composition
`T⁽ᵏ⁺¹⁾ ∘ relu ∘ T⁽ᵏ⁾ ∘ ⋯ ∘ relu ∘ T⁽¹⁾` of `k+1` affine maps. -/
def ComputedBy : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0,     f => ∃ T : Aff n 1, ∀ x, f x = T.eval x 0
  | n, (k+1), f => ∃ (m : ℕ) (T : Aff n m) (g : (Fin m → ℝ) → ℝ),
      ComputedBy m k g ∧ ∀ x, f x = g (reluVec (T.eval x))

/-- `ReLU_{n,k}` : functions `ℝⁿ → ℝ` computed by a ReLU network with **at most**
`k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) := {f | ∃ j ≤ k, ComputedBy n j f}

/-- An affine functional `ℝⁿ → ℝ`. -/
def IsAffine {n : ℕ} (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x, g x = (∑ i, a i * x i) + b

/-- A closed affine halfspace of `ℝⁿ`. -/
def IsHalfspace (n : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), S = {x | (∑ i, a i * x i) ≤ b}

/-- A polyhedron of `ℝⁿ` : a finite intersection of halfspaces.  Note `m = 0`
gives `⋂ (i : Fin 0), _ = univ`, so `ℝⁿ` itself is a polyhedron. -/
def IsPolyhedron (n : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (H : Fin m → Set (Fin n → ℝ)), (∀ i, IsHalfspace n (H i)) ∧ S = ⋂ i, H i

/-- `IsCPWL n f` : `f` is continuous and there is a finite polyhedral cover of
`ℝⁿ` on each piece of which `f` agrees with an affine functional. -/
def IsCPWL (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  Continuous f ∧
    ∃ (m : ℕ) (P : Fin m → Set (Fin n → ℝ)) (g : Fin m → ((Fin n → ℝ) → ℝ)),
      (∀ i, IsPolyhedron n (P i)) ∧ (∀ i, IsAffine (g i)) ∧
        (⋃ i, P i) = Set.univ ∧ ∀ i, ∀ x ∈ P i, f x = g i x

/-- `CPWL_n` : the continuous piecewise-linear functions `ℝⁿ → ℝ`. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) := {f | IsCPWL n f}

/-- The depth bound `⌈log₃(n−1)⌉ + 1`. -/
noncomputable def depthBound (n : ℕ) : ℕ := ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log₃(n−1)⌉+1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) : CPWL n = ReLUn n (depthBound n) := sorry

end Ref


namespace Agent001

/-- The ReLU activation function on `ℝ`. -/
noncomputable def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on a vector in `ℝ^n`, encoded as `Fin n → ℝ`. -/
noncomputable def reluVec {n : ℕ} (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => relu (v i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix `A` and a
translation vector `c`, acting as `x ↦ A * x + c`. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def AffineMap.eval {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `IsReLUNet n k f` says that `f : ℝ^n → ℝ` is *computed* by a ReLU network with `n`
inputs and `k` hidden layers, i.e. `f` arises as the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations with
componentwise ReLU in between (so the network has depth `k + 1` and `k` hidden layers,
matching the paper's convention). We recurse on the *first* layer: with `0` hidden
layers the network is a single affine transformation `ℝ^n → ℝ^1`, i.e. `f` itself is an
affine functional on `ℝ^n`; with `k + 1` hidden layers, `f` is obtained by first
applying an affine map `T^(1) : ℝ^n → ℝ^m` to some hidden width `m`, then componentwise
ReLU, and then feeding the result into a network with `k` hidden layers computing
`ℝ^m → ℝ`. -/
def IsReLUNet : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x, f x = (∑ i, a i * x i) + b
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : AffineMap n m) (g : (Fin m → ℝ) → ℝ),
        IsReLUNet m k g ∧ ∀ x, f x = g (reluVec (T.eval x))

/-- `ReLUn n k`: the set of functions `ℝ^n → ℝ` representable by a ReLU network with
exactly `k` hidden layers, i.e. `ReLU_{n,k}` from the paper. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) := {f | IsReLUNet n k f}

/-- A closed affine halfspace of `ℝ^n`. -/
def IsHalfspace (n : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), S = {x | (∑ i, a i * x i) ≤ b}

/-- A (closed, convex) polyhedron of `ℝ^n`: a finite intersection of halfspaces. -/
def IsPolyhedron (n : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (H : Fin m → Set (Fin n → ℝ)), (∀ i, IsHalfspace n (H i)) ∧ S = ⋂ i, H i

/-- `IsCPWL n f`: `f : ℝ^n → ℝ` is continuous and piecewise linear, meaning there is a
finite polyhedral subdivision of `ℝ^n` (a finite family of polyhedra covering `ℝ^n`) on
each piece of which `f` agrees with some affine function. This is a genuine
piecewise-linearity condition, independent of any notion of ReLU-network
representability and not phrased as a max-of-affine normal form. -/
def IsCPWL (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  Continuous f ∧
    ∃ (m : ℕ) (P : Fin m → Set (Fin n → ℝ)) (a : Fin m → (Fin n → ℝ)) (b : Fin m → ℝ),
      (∀ i, IsPolyhedron n (P i)) ∧ (⋃ i, P i) = Set.univ ∧
        ∀ i, ∀ x ∈ P i, f x = (∑ j, a i j * x j) + b i

/-- `CPWL n`: the space of continuous piecewise-linear functions `ℝ^n → ℝ`. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) := {f | IsCPWL n f}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2. Here `n - 1` (with `n ≥ 3`,
so `n - 1 ≥ 2` as a natural number) is cast to `ℝ` before taking the base-3 real
logarithm and its ceiling. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n - 1 : ℕ) : ℝ)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent001


namespace Agent002

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

Modelling choices (see summary at the end of the task for more detail):
* Vectors `ℝ^n` are encoded as `Fin n → ℝ` (a finite Pi type), which already carries the
  Mathlib Pi (sup) metric/topology instances needed for continuity and locality below.
* Affine maps `ℝ^a → ℝ^b` are given concretely as a matrix `A` plus a bias vector `c`,
  `x ↦ A.mulVec x + c`.
* A ReLU network with `k` hidden layers is modelled by the recursively-defined predicate
  `ComputesWithHiddenLayers n k f`, unwinding exactly the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper, with **exactly** `k` ReLU
  layers (this is the literal reading of the paper's definition; padding with an extra
  layer computing the identity via `ReLU(x) - ReLU(-x) = x` shows `ReLUn n k ⊆ ReLUn n (k+1)`
  so the "exactly k" and "at most k" readings agree on which sets appear as `ReLUn n K`
  for `K` large enough, but "exactly k" is what the source text literally defines).
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of affine
  functions such that every point of `ℝ^n` has a neighbourhood on which `f` coincides with
  one member of the family (this is the "finite family of affine functions that `f`
  locally agrees with" option suggested by the task spec).
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined via the real logarithm `Real.logb 3` and
  `Nat.ceil`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on vectors `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ :=
  fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias vector. -/
structure Affine (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation: `x ↦ A x + c`. -/
def Affine.eval {a b : ℕ} (T : Affine a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/--
`ComputesWithHiddenLayers n k f` holds when `f : ℝ^n → ℝ` is computed by *some* ReLU
network with input dimension `n` and exactly `k` hidden layers, i.e. `f` is the alternating
composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`
of `k + 1` affine transformations `T^(1), …, T^(k+1)` (with componentwise ReLU applied after
each of the first `k` of them), where the final transformation lands in `ℝ^1`.

We define this by recursion on `k`: a `0`-hidden-layer network is a single affine map to
`ℝ^1`; a `(k+1)`-hidden-layer network peels off the first affine map `T^(1) : ℝ^n → ℝ^m`
(for some hidden width `m`), applies ReLU, and feeds the result into a `k`-hidden-layer
network `g : ℝ^m → ℝ`.
-/
def ComputesWithHiddenLayers : (n : ℕ) → (k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : Affine n 1, f = fun x => T.eval x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : Affine n m) (g : (Fin m → ℝ) → ℝ),
        ComputesWithHiddenLayers m k g ∧ f = g ∘ reluVec ∘ T.eval

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
exactly `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ComputesWithHiddenLayers n k f}

/--
`f : ℝ^n → ℝ` is continuous piecewise linear (CPWL) if it is continuous and there is a
*finite* family of affine functions `ℝ^n → ℝ` such that every point `x` has a neighbourhood
on which `f` coincides with one member of the family.
-/
def IsCPWL (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  Continuous f ∧
    ∃ (m : ℕ) (g : Fin m → Affine n 1),
      ∀ x : Fin n → ℝ, ∃ i : Fin m, ∃ ε > 0,
        ∀ y : Fin n → ℝ, dist y x < ε → f y = (g i).eval y 0

/-- `CPWL n` is the set of continuous piecewise linear functions `ℝ^n → ℝ`. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | IsCPWL n f}

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from the paper's Theorem 2. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent002


namespace Agent003

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

  Theorem 2. For n ≥ 3, we have CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}.

## Modelling choices

* Vectors `ℝ^n` are encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is encoded concretely as a pair `(A, c)` of a
  weight matrix `A : Matrix (Fin b) (Fin a) ℝ` and a bias vector `c : Fin b → ℝ`, evaluated
  as `x ↦ A *ᵥ x + c`.
* A "ReLU network with `k` hidden layers computing `f : ℝ^n → ℝ`" is encoded by structural
  recursion on `k`: with `0` hidden layers, `f` is literally an affine map `ℝ^n → ℝ`
  (i.e. `T^{(1)}`, no ReLU applied); with `k+1` hidden layers, `f` factors as
  `f x = g (relu (T x))` where `T : ℝ^n → ℝ^m` is affine (this is `T^{(1)}`), `relu` is
  applied componentwise, and `g : ℝ^m → ℝ` is computed by a ReLU network with `k` hidden
  layers. Unwinding the recursion literally reproduces the alternating composition
  `T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}` from the paper.
* `ReLUn n k` (the set `ReLU_{n,k}`) is taken to mean representable with **at most** `k`
  hidden layers (`∃ k' ≤ k, ...`), not exactly `k`. This is the reading that makes
  Theorem 2 true: extra hidden layers never hurt (one can always pad with an
  affine "identity-like" layer), so the classes `ReLUnExact n k'` are increasing in `k'`
  up to representability, and the "at most k" reading is the standard one for
  expressivity results of this kind.
* `CPWL n` is defined mathematically (not via ReLU networks and not as a max-of-affine
  normal form): `f` is CPWL iff `f` is continuous and there is a *finite* family of affine
  functions `g_1, ..., g_m : ℝ^n → ℝ` such that every point `x` has a neighborhood on which
  `f` coincides with one of the `g_i`. This is the "locally agrees with a finite family of
  affine pieces" characterization of continuous piecewise-linear functions.
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined using the real logarithm `Real.logb 3` and
  `Nat.ceil`, exactly mirroring the real-valued ceiling in the paper.
-/

/-- The scalar ReLU function `max 0 ·` on `ℝ`. -/
def relu (t : ℝ) : ℝ := max 0 t

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a weight matrix and a bias
vector, as `x ↦ A x + c`. -/
def AffineMap (a b : ℕ) : Type := Matrix (Fin b) (Fin a) ℝ × (Fin b → ℝ)

/-- Evaluate an affine transformation `x ↦ A x + c`. -/
def AffineMap.eval {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.1.mulVec x + T.2

/-- A real-valued affine function `ℝ^n → ℝ`, i.e. `x ↦ ⟨a, x⟩ + c`. -/
def IsAffineFun {n : ℕ} (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (c : ℝ), ∀ x, g x = (∑ i, a i * x i) + c

/-- The functions `ℝ^n → ℝ` computed by a ReLU network with *exactly* `k` hidden layers,
i.e. by the alternating composition
`T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}`
of `k + 1` affine transformations `T^{(1)}, ..., T^{(k+1)}` with `component-wise` ReLU
applied after each of the first `k` of them. Defined by structural recursion on `k`. -/
def ReLUnExact : (n : ℕ) → (k : ℕ) → Set ((Fin n → ℝ) → ℝ)
  | n, 0 => { f | ∃ T : AffineMap n 1, f = fun x => AffineMap.eval T x 0 }
  | n, (k + 1) =>
      { f | ∃ (m : ℕ) (T : AffineMap n m) (g : (Fin m → ℝ) → ℝ),
            g ∈ ReLUnExact m k ∧ f = fun x => g (reluVec (AffineMap.eval T x)) }

/-- `ReLUn n k`, the set of functions `ℝ^n → ℝ` representable with at most `k` hidden
layers (see the module docstring for why "at most" is the right reading here). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, f ∈ ReLUnExact n k' }

/-- `CPWL n`, the space of continuous piecewise-linear functions `ℝ^n → ℝ`: `f` is
continuous, and there is a finite family of affine functions such that `f` locally agrees
with (at least) one member of the family at every point. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ), (∀ i, IsAffineFun (g i)) ∧
          ∀ x : Fin n → ℝ, ∃ i, Filter.Eventually (fun y => f y = g i y) (nhds x) }

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so `n - 1 ≥ 2 > 0`). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) : CPWL n = ReLUn n (depthBound n) := sorry

end Agent003


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


namespace Agent005

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We model `ℝ^n` concretely as `Fin n → ℝ`.

## Modelling choices (see summary at the end)

* Affine maps `ℝ^a → ℝ^b` are modelled concretely by a matrix `A : Matrix (Fin b) (Fin a) ℝ`
  and a bias vector `c : Fin b → ℝ`, via `x ↦ A.mulVec x + c`.
* A ReLU network with `k` hidden layers computing `f : (Fin n → ℝ) → ℝ` is defined
  *recursively* on `k`: with `0` hidden layers, `f` is exactly one affine (scalar-valued)
  map; with `k+1` hidden layers, `f` factors as (some function computable with `k` hidden
  layers on `m` real inputs) composed with (an affine map `ℝ^n → ℝ^m` followed by
  componentwise ReLU).
* `ReLUn n k` is taken to be the set of functions representable with **at most** `k`
  hidden layers (i.e. `∃ k' ≤ k`), matching the usual convention that these expressivity
  classes are increasing in `k` (`ReLUn n k ⊆ ReLUn n (k+1)`), which is the reading under
  which the stated equality `CPWL n = ReLUn n (depthBound n)` is the correct/true
  statement of Theorem 2 (a function needing strictly fewer than the bound is still in the
  class).
* `CPWL n` is defined as: continuous functions `f` that agree, in a neighborhood of every
  point, with one of finitely many affine functions (a genuine local-piecewise-linearity
  condition, not simply "representable by a ReLU network" and not a max-of-affine normal
  form).
* The depth bound `⌈log_3 (n-1)⌉ + 1` is defined using the real logarithm `Real.logb 3`
  together with `Nat.ceil`.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (v : Fin m → ℝ) : Fin m → ℝ := fun i => relu (v i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias vector. -/
def affineComp {a b : ℕ} (A : Matrix (Fin b) (Fin a) ℝ) (c : Fin b → ℝ) (x : Fin a → ℝ) :
    Fin b → ℝ :=
  A.mulVec x + c

/-- A scalar-valued (i.e. `ℝ^a → ℝ`) affine map, given by a weight vector and a bias. -/
def affineScalar {a : ℕ} (w : Fin a → ℝ) (c : ℝ) (x : Fin a → ℝ) : ℝ :=
  (Finset.univ.sum fun i => w i * x i) + c

/-- `f` is affine, i.e. of the form `x ↦ ⟨w, x⟩ + c`. -/
def IsAffine {a : ℕ} (f : (Fin a → ℝ) → ℝ) : Prop :=
  ∃ (w : Fin a → ℝ) (c : ℝ), f = affineScalar w c

/-- `computesReLU k n f` means: `f : ℝ^n → ℝ` is *exactly* computed by a ReLU network with
`k` hidden layers, i.e. by an alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`
of `k + 1` affine transformations with componentwise ReLU applications in between.
Recursion is on the number of hidden layers: with `0` hidden layers the network is a
single affine map; with `k + 1` hidden layers, the first affine map `T^(1) : ℝ^n → ℝ^m`
followed by a ReLU is applied, and the remaining computation is a `k`-hidden-layer network
on the `m` resulting coordinates. -/
def computesReLU : ℕ → (n : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | 0, n, f => IsAffine f
  | (k + 1), n, f =>
      ∃ (m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ) (g : (Fin m → ℝ) → ℝ),
        computesReLU k m g ∧ f = g ∘ (fun x => reluVec (affineComp A c x))

/-- `ReLUn n k`: the set of functions `ℝ^n → ℝ` representable by a ReLU network with
**at most** `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, computesReLU k' n f}

/-- `CPWL n`: the continuous, piecewise-linear functions `ℝ^n → ℝ`. A function is CPWL if
it is continuous and, around every point, agrees with one of finitely many affine
functions (a genuine local piecewise-affineness condition). -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
      ∃ F : Finset ((Fin n → ℝ) → ℝ), (∀ g ∈ F, IsAffine g) ∧
        ∀ x : Fin n → ℝ, ∃ g ∈ F, ∃ U : Set (Fin n → ℝ), IsOpen U ∧ x ∈ U ∧ Set.EqOn f g U}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so `n - 1 ≥ 2`). -/
def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent005


namespace Agent006

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):  for `n ≥ 3`,  `CPWL n = ReLUn n (⌈log_3 (n-1)⌉ + 1)`.

## Modelling choices

* Vectors `ℝ^n` are encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is encoded concretely as a matrix `A` together
  with a bias vector `c`, evaluated as `x ↦ A.mulVec x + c`.
* A ReLU network with `k` hidden layers computing `f : ℝ^n → ℝ` is defined by recursion
  on `k`: with `0` hidden layers it is a single affine map `ℝ^n → ℝ^1`; with `k+1` hidden
  layers it is an affine map `ℝ^n → ℝ^m` into some hidden width `m`, followed by a
  component-wise ReLU, followed by a network with `k` hidden layers on the output.
  This mirrors the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper.
* `ReLUn n k` is taken to be functions representable with **at most** `k` hidden layers
  (not exactly `k`).  This is the reading under which Theorem 2 is true: extra hidden
  layers can only help (one can always pad a shallower network out to more layers), so
  `ReLUn n k` is monotone increasing in `k`, and the content of Theorem 2 is that
  `⌈log_3(n-1)⌉ + 1` hidden layers already suffice to reach all of `CPWL n` (and no fewer
  would, by Theorem 1's lower bound machinery) — an "exactly `k`" reading would make the
  two sides genuinely different sets for essentially every `k`, and the displayed equality
  would be false/ill-posed.
* `CPWL n` is defined directly (not via ReLU networks!) as: `f` is continuous, and there is
  a *finite* family of affine scalar functions on `ℝ^n` such that `f` locally agrees with
  (at least) one member of the family in a neighbourhood of every point. This is a genuine
  piecewise-linearity condition, not a max-of-affine normal form and not "representable by
  some network".
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined using the real logarithm `Real.logb 3` and
  `Nat.ceil`, applied to `(n : ℝ) - 1`.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias vector. -/
structure AffineTransform (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation: `x ↦ A x + c`. -/
def affineApply {a b : ℕ} (T : AffineTransform a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- An affine *scalar* function `ℝ^n → ℝ`, given by a coefficient vector and a constant. -/
structure AffineFunc (n : ℕ) where
  coeffs : Fin n → ℝ
  const : ℝ

/-- Evaluation of a scalar affine function: `x ↦ ⟨coeffs, x⟩ + const`. -/
def AffineFunc.eval {n : ℕ} (g : AffineFunc n) (x : Fin n → ℝ) : ℝ :=
  (∑ i, g.coeffs i * x i) + g.const

/-- `ComputesHidden n k f` holds iff `f : ℝ^n → ℝ` is computed by a ReLU network with
exactly `k` hidden layers, i.e. by the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations
`T^(1), …, T^(k+1)` with componentwise ReLU applications in between. Defined by recursion
on `k`: the base case `k = 0` is a single affine map into `ℝ^1`; the successor case peels
off the first affine map `T^(1) : ℝ^n → ℝ^m` and one ReLU, leaving a `k`-hidden-layer
network on the resulting `ℝ^m`. -/
def ComputesHidden : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : AffineTransform n 1, ∀ x, f x = affineApply T x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : AffineTransform n m) (g : (Fin m → ℝ) → ℝ),
        ComputesHidden m k g ∧ ∀ x, f x = g (reluVec (affineApply T x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
**at most** `k` hidden layers (see the modelling-choice discussion above for why "at most"
rather than "exactly `k`" is the reading that makes Theorem 2 true). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, ComputesHidden n k' f}

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: those that
are continuous and locally agree, near every point, with some member of a single *finite*
family of affine scalar functions. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
       ∃ (m : ℕ) (g : Fin m → AffineFunc n),
         ∀ x : Fin n → ℝ, ∃ i : Fin m, ∀ᶠ y in nhds x, f y = (g i).eval y}

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so `n - 1 ≥ 2`). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL n = ReLUn n (⌈log_3(n-1)⌉ + 1)`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent006


namespace Agent007

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We encode `ℝ^n` as `Fin n → ℝ`. Affine transformations `ℝ^a → ℝ^b` are encoded
concretely as `x ↦ A.mulVec x + c` for a matrix `A` and bias vector `c`. A ReLU
network with `k` hidden layers is a `k+1`-fold alternating composition of such
affine transformations with the componentwise ReLU nonlinearity, encoded by the
recursive predicate `RepresentableVec` below. `ReLUn n k` is the set of scalar
functions `ℝ^n → ℝ` representable by *some* ReLU network with *at most* `k`
hidden layers (this is the reading of `ReLU_{n,k}` under which Theorem 2 is
true: since a ReLU network with `j ≤ k` hidden layers can always be padded, via
the identity trick `x ↦ ReLU(x) - ReLU(-x) = x`, into a network with exactly
`k` hidden layers computing the same function, the "at most k" and "exactly k"
readings of the class actually coincide as sets, but "at most" is the more
standard and directly usable reading). `CPWL n` is defined independently, via
continuity together with local agreement with a finite family of affine
functions (a genuine piecewise-affine condition, not a max-of-affine normal
form and not "representable by a ReLU network").
-/

/-- The ReLU activation function on `ℝ`. -/
noncomputable def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^n`. -/
noncomputable def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => relu (x i)

/-- The affine transformation `ℝ^a → ℝ^b` given by matrix `A` and bias `c`,
namely `x ↦ A x + c`. -/
noncomputable def affineEval {a b : ℕ} (A : Matrix (Fin b) (Fin a) ℝ) (c : Fin b → ℝ)
    (x : Fin a → ℝ) : Fin b → ℝ :=
  A.mulVec x + c

/-- `RepresentableVec n k b f` : the vector-valued function `f : ℝ^n → ℝ^b` is
computed by a ReLU network with `k` hidden layers and output dimension `b`,
i.e. there are affine transformations `T^(1), ..., T^(k+1)` (with `T^(k+1)`
landing in `ℝ^b`) such that
`f = T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`.
The base case `k = 0` is a single affine transformation (no ReLU at all,
i.e. depth 1, 0 hidden layers); the successor case peels off the *outermost*
affine map `T^(k+1)` (with an arbitrary hidden width `m` for the preceding
layer) and applies ReLU before it. -/
def RepresentableVec : (n k b : ℕ) → ((Fin n → ℝ) → (Fin b → ℝ)) → Prop
  | n, 0, b, f =>
      ∃ (A : Matrix (Fin b) (Fin n) ℝ) (c : Fin b → ℝ), f = affineEval A c
  | n, (k + 1), b, f =>
      ∃ (m : ℕ) (g : (Fin n → ℝ) → (Fin m → ℝ))
        (A : Matrix (Fin b) (Fin m) ℝ) (c : Fin b → ℝ),
        RepresentableVec n k m g ∧ f = fun x => affineEval A c (reluVec (g x))

/-- The scalar function `f : ℝ^n → ℝ` is computed by a ReLU network with
exactly `k` hidden layers. -/
def Representable (n k : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  RepresentableVec n k 1 (fun x _ => f x)

/-- `ReLUn n k` : the set of functions `ℝ^n → ℝ` representable by a ReLU
network with *at most* `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ j ≤ k, Representable n j f}

/-- An affine function `ℝ^n → ℝ`, given by a weight vector `w` and bias `b`,
namely `x ↦ ∑ i, w i * x i + b`. -/
def AffineFun (n : ℕ) := (Fin n → ℝ) × ℝ

/-- Evaluation of an affine function. -/
noncomputable def AffineFun.eval {n : ℕ} (a : AffineFun n) (x : Fin n → ℝ) : ℝ :=
  (∑ i, a.1 i * x i) + a.2

/-- `CPWL n` : the set of continuous, piecewise-linear functions `ℝ^n → ℝ`,
i.e. continuous functions that agree, on a neighborhood of every point, with
one of finitely many globally-fixed affine functions. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧ ∃ S : Finset (AffineFun n),
        ∀ x : Fin n → ℝ, ∃ a ∈ S, ∃ U : Set (Fin n → ℝ),
          IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, f y = a.eval y}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, as a natural number. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent007


namespace Agent008

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We model `ℝ^n` as `Fin n → ℝ`.

Modelling choices (see summary at the end of the task):
* Affine maps `ℝ^a → ℝ^b` are given explicitly and concretely by a matrix and a bias
  vector, `x ↦ A * x + c`.
* A ReLU network with `k` hidden layers is captured by the inductive relation
  `NetworkComputes n k f`, which unwinds exactly the alternating composition
  `T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}` from the paper's definition.
* `ReLUn n k` is the set of functions computable with **at most** `k` hidden layers
  (an existential over `j ≤ k`). This is the reading under which `ReLU_{n,k}` is
  monotone increasing in `k` (extra hidden layers can never hurt, since one can always
  route a signal through an extra affine + ReLU layer without changing the represented
  function), which is the natural reading that makes Theorem 2 an *equality* of sets
  rather than a bare inclusion.
* `CPWL n` is defined genuinely: continuity, together with a finite polyhedral
  subdivision of `ℝ^n` (each piece cut out by finitely many affine inequality
  constraints, i.e. an intersection of closed half-spaces) on each piece of which `f`
  agrees with some affine function.
* The depth bound `⌈log_3 (n-1)⌉ + 1` is defined directly from `Real.logb` and
  `Nat.ceil`, matching the paper's real-valued ceiling-of-log expression verbatim.
-/

/-- The ReLU function on `ℝ`. -/
noncomputable def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^n = Fin n → ℝ`. -/
noncomputable def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given explicitly and concretely by a matrix
`A` and a bias (translation) vector `c`, acting as `x ↦ A * x + c`. -/
structure AffineMap' (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- The function `ℝ^a → ℝ^b` computed by an `AffineMap'`. -/
noncomputable def AffineMap'.apply {a b : ℕ} (T : AffineMap' a b) (x : Fin a → ℝ) :
    Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `NetworkComputes n k f` holds when `f : ℝ^n → ℝ` is computed by a ReLU network with
input dimension `n` and exactly `k` hidden layers, i.e. by some alternating composition
`T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}` of affine transformations `T^{(i)}`
with componentwise ReLU, as in the paper's definition of a depth-`(k+1)` ReLU network.

* `base` is the case `k = 0` (no hidden layers): the network is a single affine map
  `T^{(1)} : ℝ^n → ℝ`.
* `step` peels off the first affine map `T^{(1)} : ℝ^n → ℝ^m` and the first `ReLU`,
  leaving a network with `k` hidden layers computing `g : ℝ^m → ℝ`; together they
  compute `x ↦ g (ReLU (T^{(1)} x))`, a network with `k + 1` hidden layers on `ℝ^n`. -/
inductive NetworkComputes : (n : ℕ) → (k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | base {n : ℕ} (T : AffineMap' n 1) :
      NetworkComputes n 0 (fun x => T.apply x 0)
  | step {n m k : ℕ} (T : AffineMap' n m) {g : (Fin m → ℝ) → ℝ}
      (hg : NetworkComputes m k g) :
      NetworkComputes n (k + 1) (fun x => g (reluVec (T.apply x)))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
**at most** `k` hidden layers (see the module docstring for why "at most" is the right
reading here). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ j ≤ k, NetworkComputes n j f }

/-- A set `P ⊆ ℝ^n` is a polyhedron if it is a finite intersection of closed half-spaces,
i.e. cut out by finitely many affine inequality constraints `A x ≤ b`. -/
def IsPolyhedron {n : ℕ} (P : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ),
    P = { x | A.mulVec x ≤ b }

/-- `CPWL n` is the space of continuous, piecewise linear (really: piecewise affine)
functions `ℝ^n → ℝ`: those `f` that are continuous and admit a finite polyhedral
subdivision of `ℝ^n` into pieces `P i`, on each of which `f` agrees with some affine
function `g i`. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
      ∃ (m : ℕ) (P : Fin m → Set (Fin n → ℝ)) (g : Fin m → AffineMap' n 1),
        (∀ i, IsPolyhedron (P i)) ∧
        (⋃ i, P i) = Set.univ ∧
        ∀ i, ∀ x ∈ P i, f x = (g i).apply x 0 }

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, computed via the real
logarithm `Real.logb 3` and the natural-number ceiling. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL n = ReLUn n (⌈log_3 (n - 1)⌉ + 1)`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent008


namespace Agent009

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):

  For n ≥ 3,  CPWL_n = ReLU_{n, ⌈log_3 (n-1)⌉ + 1}.

## Modelling choices

* `ℝ^n` is encoded as `Fin n → ℝ`.
* An affine map `ℝ^a → ℝ^b` is encoded concretely as `x ↦ A * x + c` for a matrix
  `A : Matrix (Fin b) (Fin a) ℝ` and a bias vector `c : Fin b → ℝ`. An affine
  *functional* `ℝ^n → ℝ` is the special case `b = 1`, spelled out directly with a
  weight vector and a scalar bias.
* A ReLU network computing `f : ℝ^n → ℝ` with exactly `k` hidden layers is defined
  recursively: with `0` hidden layers, `f` itself must be affine; with `k+1` hidden
  layers, `f` factors as `g ∘ relu ∘ T` where `T : ℝ^n → ℝ^m` is affine (the first
  layer, into some hidden width `m`) and `g : ℝ^m → ℝ` is computed by a network with
  `k` hidden layers.
* `ReLUn n k` is taken to be functions representable with **at most** `k` hidden
  layers (not exactly `k`): a network with `k'` ≤ `k` hidden layers can always be
  padded to exactly `k` hidden layers by inserting extra affine "identity" layers
  (composed with `relu`, using two coordinates per padded dimension via
  `x ↦ relu(x) - relu(-x) = x`), so the two readings would in fact define the same
  sets; we use the "at most k" phrasing since it is definitionally the more natural
  one for which `ReLUn n` is monotone in `k`, matching the set-equality statement of
  the theorem.
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of affine
  functionals `g : Fin m → (ℝ^n → ℝ)` such that every point `x` has a neighbourhood on
  which `f` agrees with some `g i` (this is a genuine finite polyhedral-subdivision
  style piecewise-linearity condition, not a global max-of-affine formula and not
  "representable by some ReLU network").
* The depth bound `⌈log_3 (n-1)⌉ + 1` is encoded using the real logarithm
  `Real.logb 3` together with `Nat.ceil`.
-/

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => max 0 (x i)

/-- `T : ℝ^a → ℝ^b` is an affine map, i.e. `T x = A * x + c` for some matrix `A` and
bias vector `c`. -/
def IsAffineMap (a b : ℕ) (T : (Fin a → ℝ) → (Fin b → ℝ)) : Prop :=
  ∃ (A : Matrix (Fin b) (Fin a) ℝ) (c : Fin b → ℝ),
    ∀ x : Fin a → ℝ, ∀ i, T x i = (∑ j, A i j * x j) + c i

/-- `f : ℝ^n → ℝ` is an affine functional, i.e. `f x = ⟪a, x⟫ + c` for some weight
vector `a` and scalar bias `c`. -/
def IsAffineFunctional (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (c : ℝ), ∀ x : Fin n → ℝ, f x = (∑ j, a j * x j) + c

/-- `f : ℝ^n → ℝ` is computed by a ReLU network with exactly `k` hidden layers:
recursively, `0` hidden layers means `f` is itself affine, and `k+1` hidden layers
means `f = g ∘ relu ∘ T` where `T` is an affine "first layer" into some hidden
width `m`, and `g` is computed by a network with `k` hidden layers on that hidden
width. This directly reflects the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper. -/
def ComputesWithHiddenLayers : (k : ℕ) → (n : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | 0, n, f => IsAffineFunctional n f
  | (k + 1), n, f =>
      ∃ (m : ℕ) (T : (Fin n → ℝ) → (Fin m → ℝ)) (g : (Fin m → ℝ) → ℝ),
        IsAffineMap n m T ∧
        ComputesWithHiddenLayers k m g ∧
        (∀ x : Fin n → ℝ, f x = g (reluVec (T x)))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network
with *at most* `k` hidden layers (see the module docstring for why this reading is
used rather than "exactly `k`"). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, ComputesWithHiddenLayers k' n f }

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: those
that are continuous and, on a neighbourhood of every point, agree with one of
finitely many globally-fixed affine functionals. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ),
          (∀ i, IsAffineFunctional n (g i)) ∧
          (∀ x : Fin n → ℝ, ∃ i, ∀ᶠ y in nhds x, f y = g i y) }

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from the theorem statement. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 (↑(n - 1) : ℝ)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3 (n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent009


namespace Agent010

/-!
# Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity: Subdividing the Simplex")

We formalize `CPWL_n = ReLU_{n, ⌈log₃(n-1)⌉ + 1}` for `n ≥ 3`.

## Modelling choices

* `ℝ^n` is encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is encoded concretely as a pair `(A, c)` with
  `A : Matrix (Fin b) (Fin a) ℝ` and `c : Fin b → ℝ`, acting as `x ↦ A.mulVec x + c`.
* A ReLU network with exactly `k` hidden layers computing `f : ℝ^n → ℝ` is defined by
  recursion on `k`, mirroring the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper: the base case `k = 0` is a
  single affine map `ℝ^n → ℝ` (depth 1, no hidden layers), and the successor case peels off
  the first affine map `T^(1) : ℝ^n → ℝ^m` together with the following `ReLU`, leaving a
  network with `k` hidden layers computing the "tail" function `g : ℝ^m → ℝ`.
* `ReLUn n k` is taken to mean *at most* `k` hidden layers (`∃ k' ≤ k, ...`), not *exactly*
  `k`. This is the reading under which Theorem 2 (an equality with one specific `k`) can be
  true: the classes for exactly `k` hidden layers are not literally nested (a network with
  exactly `k` hidden layers cannot in general also be written with exactly `k+1`, unless one
  allows padding by identity layers), so the paper's `ReLU_{n,k}` is implicitly the
  "at most" / cumulative class, monotone in `k`, which is what makes an equality `CPWL_n =
  ReLU_{n,k}` for a single threshold `k` a meaningful and provable statement.
* `CPWL n` is defined mathematically (not via ReLU networks, and not as a max-of-affine
  normal form) as: `f` is continuous, and there is a *finite* family of affine functions
  `φ : Fin m → (ℝ^n → ℝ)` such that every point `x` has a neighborhood on which `f` agrees
  with (i.e. equals) some `φ i`. This is the standard "finite family of affine pieces,
  locally agreeing with `f`" formulation of continuous piecewise-linearity.
* The depth bound `⌈log₃(n-1)⌉ + 1` is defined using `Real.logb 3` and `Nat.ceil` (`⌈·⌉₊`)
  applied to the real number `(n : ℝ) - 1`, matching the paper's real-valued `log_3` and
  ceiling exactly.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a translation
vector, acting as `x ↦ A * x + c`. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an `AffineMap`. -/
def AffineMap.eval {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `NetComputes n k f` means `f : ℝ^n → ℝ` is computed by a ReLU network with exactly `k`
hidden layers, i.e. by an alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations with
componentwise ReLU. The base case `k = 0` is a bare affine map `ℝ^n → ℝ` (depth 1, no
hidden layers); the successor case peels off the first affine map into a hidden layer of
some width `m`, applies `ReLU`, and requires the remaining function `g : ℝ^m → ℝ` to be
computed by a network with `k` hidden layers. -/
def NetComputes : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : AffineMap n 1, ∀ x, f x = T.eval x 0
  | n, k + 1, f =>
      ∃ (m : ℕ) (T : AffineMap n m) (g : (Fin m → ℝ) → ℝ),
        NetComputes m k g ∧ f = fun x => g (reluVec (T.eval x))

/-- `ReLUn n k`, the set of functions `ℝ^n → ℝ` representable by a ReLU network with *at
most* `k` hidden layers (see the module docstring for why "at most" rather than "exactly"
is the reading that makes Theorem 2 true). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, NetComputes n k' f }

/-- `CPWL n`, the set of continuous piecewise-linear functions `ℝ^n → ℝ`: `f` is continuous,
and there is a finite family of affine functions such that every point has a neighborhood
on which `f` coincides with one member of the family. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
      ∃ (m : ℕ) (φ : Fin m → AffineMap n 1),
        ∀ x : Fin n → ℝ, ∃ i : Fin m, ∀ᶠ y in nhds x, f y = (φ i).eval y 0 }

/-- The depth bound `⌈log₃(n - 1)⌉ + 1` from the paper, with `log₃` the real logarithm to
base `3` and `⌈·⌉` the ceiling (as `Nat.ceil` of a real number). -/
def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log₃(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent010


namespace Agent011

/- ================================================================
   Vector encoding: we represent ℝ^n as `Fin n → ℝ`.
   ================================================================ -/

/-- The ReLU activation on a single real number. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on a vector `Fin m → ℝ`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/- ================================================================
   Affine transformations `ℝ^a → ℝ^b`, given concretely by a matrix
   and a bias vector: `x ↦ A.mulVec x + c`.
   ================================================================ -/

/-- An affine transformation `ℝ^a → ℝ^b`, given by a matrix `A` and bias `c`. -/
structure Layer (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluate an affine layer at a point. -/
def Layer.apply {a b : ℕ} (L : Layer a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  L.A.mulVec x + L.c

/-- An affine functional `ℝ^n → ℝ` (i.e. a `Layer n 1` evaluated at the unique output
    coordinate). Used below to phrase "piecewise affine". -/
def IsAffineFun (n : ℕ) (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x : Fin n → ℝ, g x = (∑ i : Fin n, a i * x i) + b

/- ================================================================
   ReLU networks with exactly `k` hidden layers, from input dimension
   `a` down to scalar output, given as an inductively-built chain of
   affine layers with ReLU nonlinearities interleaved:

       T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)

   `NetLayers a k` packages exactly this data: `k` hidden layers means
   `k + 1` affine transformations `T^(1), …, T^(k+1)`, with a ReLU
   applied after each of the first `k` of them.
   ================================================================ -/

/-- `NetLayers a k` : the data of a ReLU network with input dimension `a`,
    scalar output, and exactly `k` hidden layers (i.e. `k + 1` affine maps,
    with ReLU applied between consecutive ones). -/
inductive NetLayers : ℕ → ℕ → Type
  | last {a : ℕ} (L : Layer a 1) : NetLayers a 0
  | cons {a b k : ℕ} (L : Layer a b) (rest : NetLayers b k) : NetLayers a (k + 1)

/-- The scalar function `ℝ^a → ℝ` computed by a `NetLayers a k` network. -/
def NetLayers.eval : {a k : ℕ} → NetLayers a k → (Fin a → ℝ) → ℝ
  | _, _, NetLayers.last L, x => L.apply x 0
  | _, _, NetLayers.cons L rest, x => rest.eval (reluVec (L.apply x))

/-- `ReLUn n k` : the CPWL functions `ℝ^n → ℝ` representable by a ReLU network
    with **at most** `k` hidden layers. (We use "at most `k`" rather than
    "exactly `k`": extra hidden layers never lose expressivity — an extra
    layer can always implement the identity via `x ↦ relu x - relu (-x)` —
    so this is the reading under which the increasing family `ReLUn n k`
    stabilizes at `CPWL n`, matching Theorem 2 as an equality of sets.) -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ j ≤ k, ∃ net : NetLayers n j, f = net.eval }

/- ================================================================
   Continuous piecewise-linear (CPWL) functions `ℝ^n → ℝ`: continuous
   functions that locally agree with one of finitely many affine
   functionals around every point (a genuine local-affine / polyhedral-
   subdivision style definition, not "max of affine" and not
   "representable by a ReLU network").
   ================================================================ -/

/-- `CPWL n` : continuous functions `ℝ^n → ℝ` that, near every point, coincide
    with one of a fixed finite family of affine functionals. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (g : Fin m → ((Fin n → ℝ) → ℝ)),
          (∀ i, IsAffineFun n (g i)) ∧
          ∀ x : Fin n → ℝ, ∃ i : Fin m, ∃ U ∈ nhds x, Set.EqOn f (g i) U }

/- ================================================================
   The depth bound `⌈log_3 (n - 1)⌉ + 1`, using the real logarithm
   `Real.logb 3` and `Nat.ceil`.
   ================================================================ -/

/-- The hidden-layer bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2. -/
def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/- ================================================================
   Theorem 2.
   ================================================================ -/

theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent011


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


namespace Agent013

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):  for `n ≥ 3`,  `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`.

## Modelling choices

* Vectors `ℝ^n` are encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is encoded concretely as a matrix `A` together
  with a bias vector `c`, evaluated as `x ↦ A.mulVec x + c`.
* A ReLU network with `k` hidden layers is represented by exactly `k + 1` affine
  transformations, alternately composed with the (componentwise) ReLU function, matching
  the paper's convention that "depth k+1" = "k hidden layers". This is encoded by the
  recursively-defined predicate `IsReLURep n k f`.
* `ReLUn n k` is the set of functions representable with **at most** `k` hidden layers
  (rather than *exactly* `k`): this is the reading under which Theorem 2 is true, since a
  network with fewer hidden layers can always be padded (e.g. via the identity
  `x = ReLU(x) - ReLU(-x)`) into one with more hidden layers computing the same function,
  so `ReLU_{n,k} ⊆ ReLU_{n,k+1}` and the "exactly" and "at most" readings only differ by
  this monotonicity, with the "at most" reading being the standard and provable one.
* `CPWL n` is defined genuinely as: continuous, and locally agreeing at every point with
  one of finitely many affine functions (a genuine finite local-affine-pieces condition,
  not a max-of-affine normal form and not "representable by some ReLU network").
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded via `Real.logb 3` and `Nat.ceil`.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^n`. -/
def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias vector. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation: `x ↦ A x + c`. -/
def AffineMap.eval {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/--
`IsReLURep n k f` means `f : ℝ^n → ℝ` is computed by a ReLU network with `k` hidden
layers, i.e. by the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`
of `k + 1` affine transformations `T^(1), …, T^(k+1)` with componentwise ReLU.
Defined by recursion on `k`, peeling off the first affine transformation `T^(1)` (into
some hidden width `m`) and the first ReLU at each step.
-/
def IsReLURep : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : AffineMap n 1, f = fun x => (T.eval x) 0
  | n, k + 1, f =>
      ∃ (m : ℕ) (T : AffineMap n m) (g : (Fin m → ℝ) → ℝ),
        IsReLURep m k g ∧ f = fun x => g (reluVec (T.eval x))

/--
`ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with **at
most** `k` hidden layers (see the modelling-choice note above for why "at most" rather
than "exactly").
-/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, IsReLURep n k' f }

/--
A function `ℝ^n → ℝ` is piecewise linear if there is a finite family of affine functions
such that every point has a neighbourhood on which `f` agrees with one member of the
family. This is a genuine finite local-affine-pieces condition (not a max-of-affine
normal form).
-/
def IsPWL {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (r : ℕ) (g : Fin r → AffineMap n 1),
    ∀ x : Fin n → ℝ, ∃ i : Fin r, ∃ ε > 0, ∀ y : Fin n → ℝ, dist y x < ε → f y = (g i).eval y 0

/-- The space of continuous piecewise linear functions `ℝ^n → ℝ`. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧ IsPWL f }

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from the paper, for `n ≥ 3` (so `n - 1 ≥ 2`). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent013


namespace Agent014

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):  for `n ≥ 3`,  `CPWL n = ReLUn n (⌈log_3 (n-1)⌉ + 1)`.

## Modelling choices

* `ℝ^n` is encoded as `Fin n → ℝ`.
* Affine transformations `ℝ^a → ℝ^b` are modelled concretely as `x ↦ A * x + c` via the
  structure `AffineT`.
* A ReLU network with `k` hidden layers computing `f : (Fin n → ℝ) → ℝ` is modelled by the
  predicate `IsReLUNetFun n k f`, defined by recursion on `k`, which literally unfolds the
  alternating composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper: the
  base case `k = 0` is a single affine map `ℝ^n → ℝ` (no ReLU, i.e. depth 1, the last
  affine transform `T^(k+1)`), and the successor case peels off the first affine map
  `T^(1) : ℝ^n → ℝ^m`, applies `ReLU` componentwise, and recurses on a network with `k`
  fewer hidden layers computing the rest.  This reading takes `ReLUn n k` to mean
  "representable by a network with *exactly* `k` hidden layers" (matching the paper's
  literal phrasing "representable with `k` hidden layers"); this is harmless for the
  theorem because a network with `k` hidden layers can always be padded into one with
  `k+1` hidden layers (insert an extra affine layer that is the identity, followed by
  `ReLU` applied to an appropriately shifted/duplicated copy of the coordinates), so the
  classes `ReLUn n k` are increasing in `k` and the equality with `CPWL n` at the stated
  bound is the intended, faithful statement.
* `CPWL n` is defined honestly via a genuine finite polyhedral subdivision: `f` is CPWL if
  it is continuous and there is a finite family of "pieces", each given by an affine
  function together with a polyhedral region (a finite intersection of half-spaces
  `{x | ⟨normal, x⟩ ≤ bound}`), whose regions cover `ℝ^n` and on each of which `f` agrees
  with the piece's affine function.  This is *not* "representable by some ReLU network"
  and *not* a max-of-affine normal form.
* The depth bound `⌈log_3 (n-1)⌉ + 1` is defined using `Real.logb 3` and `Nat.ceil` (`⌈·⌉₊`).
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector in `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix `A` and a
translation vector `c`, computing `x ↦ A * x + c`. -/
structure AffineT (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def AffineT.eval {a b : ℕ} (T : AffineT a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `IsReLUNetFun n k f` means `f : ℝ^n → ℝ` is computed by a ReLU network with exactly `k`
hidden layers, i.e. `f` is the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations
`T^(1), …, T^(k+1)` interspersed with componentwise `ReLU`.  Defined by recursion on `k`:
the base case is a single affine map (the final transform `T^(k+1)`, no `ReLU`), and each
successor step peels off the first affine transform together with its following `ReLU`. -/
def IsReLUNetFun : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : AffineT n 1, ∀ x, f x = T.eval x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : AffineT n m) (g : (Fin m → ℝ) → ℝ),
        IsReLUNetFun m k g ∧ ∀ x, f x = g (reluVec (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
`k` hidden layers (i.e. depth `k + 1`). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) := {f | IsReLUNetFun n k f}

/-- A single piece of a piecewise-linear subdivision of `ℝ^n`: an affine function together
with a polyhedral region on which it is meant to agree with the global function, the
region being given as a finite intersection of half-spaces `⟨normal j, x⟩ ≤ bound j`. -/
structure PWLPiece (n : ℕ) where
  aff : AffineT n 1
  numConstraints : ℕ
  normal : Fin numConstraints → (Fin n → ℝ)
  bound : Fin numConstraints → ℝ

/-- The polyhedral region associated to a piece. -/
def PWLPiece.region {n : ℕ} (P : PWLPiece n) : Set (Fin n → ℝ) :=
  {x | ∀ j, (∑ i, P.normal j i * x i) ≤ P.bound j}

/-- `f : ℝ^n → ℝ` is continuous and piecewise linear: it is continuous, and there is a
finite family of pieces, each a polyhedral region together with an affine function, whose
regions cover all of `ℝ^n` and on each of which `f` agrees with the piece's affine
function. -/
def IsCPWL (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  Continuous f ∧
    ∃ (ι : Type) (_ : Fintype ι) (pieces : ι → PWLPiece n),
      (⋃ i, (pieces i).region) = Set.univ ∧
        ∀ i, ∀ x ∈ (pieces i).region, f x = (pieces i).aff.eval x 0

/-- `CPWL n` is the set of continuous piecewise-linear functions `ℝ^n → ℝ`. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) := {f | IsCPWL n f}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, using the real logarithm to base
`3` and the natural-number ceiling. -/
noncomputable def depthBound (n : ℕ) : ℕ := ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL n = ReLUn n (⌈log_3 (n - 1)⌉ + 1)`. -/
theorem theorem2 : ∀ n : ℕ, n ≥ 3 → CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent014


namespace Agent015

/- ================= Vectors and ReLU ================= -/

/-- We encode `ℝ^n` concretely as `Fin n → ℝ`. -/
abbrev Vec (n : ℕ) := Fin n → ℝ

/-- The scalar ReLU function `x ↦ max 0 x`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on vectors. -/
def reluVec {n : ℕ} (x : Vec n) : Vec n := fun i => relu (x i)

/- ================= Affine transformations ================= -/

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix `A` and a
bias vector `c`, computing `x ↦ A * x + c`. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Vec b

/-- The function computed by an affine transformation. -/
def AffineMap.toFun {a b : ℕ} (T : AffineMap a b) (x : Vec a) : Vec b :=
  T.A.mulVec x + T.c

/- ================= ReLU networks ================= -/

/-- `Represents n k f` holds when `f : ℝ^n → ℝ` is computed by *some* ReLU network
with input dimension `n`, exactly `k` hidden layers, and output dimension `1`, i.e.
`f` arises as the alternating composition

  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`

of `k + 1` affine transformations with componentwise ReLU applied between
consecutive affine transformations (and nowhere else). We build this up by
recursion on `k`, peeling off the *first* affine + ReLU layer at each step:
a network with `k + 1` hidden layers from `ℝ^n` is a first affine map
`T^(1) : ℝ^n → ℝ^m` followed by a ReLU, followed by a network with `k` hidden
layers from `ℝ^m`. The base case `k = 0` is a single affine map `ℝ^n → ℝ`
with no ReLU applied at all, matching the definition with `k + 1 = 1` affine
transformation and no hidden layers. -/
def Represents : (n : ℕ) → (k : ℕ) → (Vec n → ℝ) → Prop
  | n, 0, f => ∃ T : AffineMap n 1, ∀ x : Vec n, f x = T.toFun x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : AffineMap n m) (g : Vec m → ℝ),
        Represents m k g ∧ ∀ x : Vec n, f x = g (reluVec (T.toFun x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network
with **exactly** `k` hidden layers (this is the reading under which Theorem 2, an
equality of sets, is true: with "at most `k`" the right-hand side would be an
increasing union over depths and the displayed equality would not pin down the
exact value `⌈log_3(n-1)⌉ + 1`). -/
def ReLUn (n k : ℕ) : Set (Vec n → ℝ) := { f | Represents n k f }

/- ================= CPWL functions ================= -/

/-- `f : ℝ^n → ℝ` is continuous piecewise linear (CPWL) if it is continuous and
there is a *finite* family of affine functions `g_1, …, g_m : ℝ^n → ℝ` such that
around every point `x`, `f` coincides with one of the `g_i` on a whole
neighbourhood of `x` (a finite polyhedral-type subdivision on whose pieces `f`
is affine, phrased via local agreement rather than a global max-of-affine
normal form). -/
def IsCPWL (n : ℕ) (f : Vec n → ℝ) : Prop :=
  Continuous f ∧
    ∃ (m : ℕ) (g : Fin m → AffineMap n 1),
      ∀ x : Vec n, ∃ i : Fin m, ∃ ε > 0,
        ∀ y : Vec n, dist y x < ε → f y = (g i).toFun y 0

/-- `CPWL n` is the set of continuous piecewise linear functions `ℝ^n → ℝ`. -/
def CPWL (n : ℕ) : Set (Vec n → ℝ) := { f | IsCPWL n f }

/- ================= Depth bound ================= -/

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from the theorem statement, using the
real logarithm `Real.logb 3` and `Nat.ceil` for the ceiling. -/
def depthBound (n : ℕ) : ℕ := ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/- ================= Theorem 2 ================= -/

/-- **Theorem 2.** For `n ≥ 3`, `CPWL n = ReLUn n (⌈log_3(n-1)⌉ + 1)`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent015


namespace Agent016

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We formalize:

  Theorem 2. For n ≥ 3, CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}.

## Modelling choices (see summary at the end of the file / final chat reply)

* Vectors `ℝ^n` are modelled as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is modelled concretely as a pair `(A, c)` of a
  matrix `A : Matrix (Fin b) (Fin a) ℝ` and a bias vector `c : Fin b → ℝ`, applied as
  `x ↦ A.mulVec x + c`.
* "Computed by a ReLU network with `k` hidden layers" is defined by structural recursion
  on `k` (as an inductive predicate `ComputesHidden`), directly mirroring the alternating
  composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper: a network with
  `0` hidden layers is a single affine map to `ℝ^1`; a network with `k+1` hidden layers is
  an affine map into some intermediate width `m`, followed by a component-wise ReLU,
  followed by a network with `k` hidden layers on `ℝ^m`.
* `ReLUn n k` is the set of functions representable with **at most** `k` hidden layers
  (i.e. `∃ k' ≤ k`), not exactly `k`. This is the standard reading in the expressivity
  literature (adding hidden layers never hurts, since a network with fewer hidden layers
  can always be padded to a deeper one), and it is the reading that makes an equality
  `CPWL_n = ReLU_{n,k}` for a *specific* `k` a meaningful, non-vacuous statement (namely:
  `k` hidden layers suffice for *all* of `CPWL_n`, and no CPWL function needs more).
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of affine
  functions such that `f` locally agrees (in a neighbourhood of every point) with one
  member of the family. This is a genuine piecewise-linearity condition (not "representable
  by some ReLU network", and not a global max-of-affine normal form), following the spec.
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined using `Real.logb 3` and `Nat.ceil`.
-/

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias vector. -/
def AffineT (a b : ℕ) : Type := (Matrix (Fin b) (Fin a) ℝ) × (Fin b → ℝ)

/-- Evaluate an affine transformation: `x ↦ A * x + c`. -/
def applyAffine {a b : ℕ} (T : AffineT a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.1.mulVec x + T.2

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Component-wise application of ReLU to a vector. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- `ComputesHidden n k f` means the function `f : ℝ^n → ℝ` is computed by a ReLU network
with input dimension `n` and exactly `k` hidden layers, i.e. `f` is the alternating
composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations
with `k` component-wise applications of ReLU in between, ending in output dimension `1`. -/
inductive ComputesHidden : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | zero {n : ℕ} (T : AffineT n 1) :
      ComputesHidden n 0 (fun x => applyAffine T x 0)
  | succ {n m k : ℕ} (T : AffineT n m) {g : (Fin m → ℝ) → ℝ}
      (hg : ComputesHidden m k g) :
      ComputesHidden n (k + 1) (fun x => g (reluVec (applyAffine T x)))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, ComputesHidden n k' f }

/-- An affine function `ℝ^n → ℝ`, given as `x ↦ ⟨a, x⟩ + c` for some coefficient vector
`a` and constant `c`. -/
def IsAffineFun {n : ℕ} (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (c : ℝ), ∀ x, g x = (∑ i, a i * x i) + c

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: those that
are continuous and, at every point, locally agree with one member of some fixed finite
family of affine functions. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
      ∃ (m : ℕ) (g : Fin m → ((Fin n → ℝ) → ℝ)),
        (∀ i, IsAffineFun (g i)) ∧
        ∀ x : Fin n → ℝ, ∃ i, ∀ᶠ y in nhds x, f y = g i y }

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from Theorem 2. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, the CPWL functions on `ℝ^n` are exactly those representable
by a ReLU network with at most `⌈log_3(n - 1)⌉ + 1` hidden layers. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent016


namespace Agent017

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

"Better Neural Network Expressivity: Subdividing the Simplex"

Theorem 2. For n ≥ 3, we have CPWL_n = ReLU_{n, ⌈log_3(n−1)⌉ + 1}.

## Modelling choices

* Vectors ℝ^m are modelled as `Fin m → ℝ`.
* An affine transformation ℝ^a → ℝ^b is modelled concretely by the structure `Aff a b`,
  carrying a matrix `A : Matrix (Fin b) (Fin a) ℝ` and a bias vector `c : Fin b → ℝ`,
  evaluated as `x ↦ A *ᵥ x + c`.
* `relu : ℝ → ℝ` is `fun x => max 0 x`, and `reluV` is its componentwise application
  to vectors.
* "`f` is computed by a ReLU network with exactly `k` hidden layers" is captured by the
  recursive predicate `ComputesWithLayers n k f`: with `0` hidden layers `f` itself must
  be (the scalar output of) a single affine map `ℝ^n → ℝ`; with `k+1` hidden layers, `f`
  factors as `g ∘ reluV ∘ T` where `T : ℝ^n → ℝ^m` is affine and `g` is computable with
  `k` hidden layers from `ℝ^m`.
* `ReLUn n k` is read as **"at most k hidden layers"** (not exactly k): this is the
  standard convention in the expressivity literature, and it is the reading under which
  the stated equality can be true, since `ReLUn n k` is then monotone increasing in `k`
  and the theorem says it *saturates* to all of `CPWL n` once `k` reaches the stated
  bound. Under the "exactly k" reading, `ReLUn n k` need not even be a subset of
  `ReLUn n (k+1)` (padding a network with extra layers is not automatic), so the
  displayed equality of sets would generally fail.
* `CPWL n` is defined mathematically (not via ReLU networks, and not as a max-of-affine
  normal form) as: `f` is continuous, and there is a *finite* family of affine functions
  `Fin N → Aff n 1` such that every point `x` has a neighbourhood on which `f` agrees
  with (at least) one member of the family. This is the "finite family of affine
  functions that `f` locally agrees with" formulation suggested by the task spec.
* The depth bound `⌈log_3(n−1)⌉ + 1` is defined via the genuine real logarithm
  `Real.logb 3` composed with `Nat.ceil`, applied to the natural number `n - 1`
  (well-defined since the theorem only concerns `n ≥ 3`, so `n - 1 ≥ 2`).
-/

/-- `relu : ℝ → ℝ`, the scalar ReLU activation. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector `ℝ^m`. -/
def reluV {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias
vector, i.e. `x ↦ A *ᵥ x + c`. -/
structure Aff (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def Aff.eval {a b : ℕ} (T : Aff a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `ComputesWithLayers n k f` : the function `f : ℝ^n → ℝ` is computed by a ReLU
network with exactly `k` hidden layers, in the sense of the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of affine transformations `T^(i)`. -/
def ComputesWithLayers : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : Aff n 1, ∀ x, f x = (T.eval x) 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : Aff n m) (g : (Fin m → ℝ) → ℝ),
        ComputesWithLayers m k g ∧ ∀ x, f x = g (reluV (T.eval x))

/-- `ReLUn n k`, the set of functions `ℝ^n → ℝ` representable with **at most** `k`
hidden layers (see the modelling notes above for why "at most" rather than "exactly"
is the reading that makes the theorem true). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, ComputesWithLayers n k' f}

/-- `CPWL n`, the set of continuous piecewise-linear functions `ℝ^n → ℝ`: continuous
functions that, near every point, agree with one member of some fixed finite family of
affine functions. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
      ∃ (N : ℕ) (g : Fin N → Aff n 1),
        ∀ x : Fin n → ℝ, ∃ (U : Set (Fin n → ℝ)) (i : Fin N),
          U ∈ nhds x ∧ ∀ y ∈ U, f y = (g i).eval y 0}

/-- The depth bound `⌈log_3(n − 1)⌉ + 1` from the statement of Theorem 2. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n - 1 : ℕ) : ℝ)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL n = ReLUn n (⌈log_3(n−1)⌉ + 1)`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent017


namespace Agent018

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):  for `n ≥ 3`,  `CPWL n = ReLUn n (⌈log₃(n-1)⌉ + 1)`.

## Modelling choices

* Vectors `ℝ^m` are encoded as `Fin m → ℝ`.
* Affine transformations `ℝ^a → ℝ^b` are given concretely by a matrix `A : Matrix (Fin b)
  (Fin a) ℝ` together with a bias vector `c : Fin b → ℝ`, evaluated as `x ↦ A.mulVec x + c`.
* A ReLU network with `k` hidden layers and input dimension `n` is modelled by the inductive
  type `ReLUNet n k`: either a single affine map `ℝ^n → ℝ` (the `k = 0` case, i.e. depth `1`,
  no hidden layers), or an affine map `ℝ^n → ℝ^m` followed by componentwise ReLU and then a
  network with `k` hidden layers on `ℝ^m` (the `k + 1` case). This exactly encodes the
  alternating composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper.
* `ReLUn n k` is the set of functions representable by a network with **at most** `k` hidden
  layers (rather than *exactly* `k`). We choose this reading because it is the one that makes
  statements like Theorem 2 meaningful and true: representability is monotone in the number of
  hidden layers (a network with fewer layers can always be reproduced, via standard padding
  tricks, by one with more layers), so "the depth needed to represent all of `CPWL n`" should be
  read as a least upper bound, i.e. "representable with at most this many hidden layers".
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of scalar affine
  functions `g_1, …, g_m : ℝ^n → ℝ` such that every point `x` has a neighbourhood on which `f`
  coincides with (at least) one of the `g_i`. This is a genuine local-piecewise-affine condition
  (not defined as "representable by some ReLU network", and not a max-of-affine normal form).
* The depth bound `⌈log₃(n-1)⌉ + 1` is defined using the real logarithm `Real.logb 3` and
  `Nat.ceil`, matching the paper's real-valued ceiling of `log_3(n-1)`.
-/

/-- The ReLU function on `ℝ`. -/
noncomputable def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
noncomputable def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ :=
  fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias vector. -/
structure AffineMap' (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation: `x ↦ A x + c`. -/
def AffineMap'.eval {a b : ℕ} (T : AffineMap' a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- A ReLU network with input dimension `n` and `k` hidden layers, outputting a scalar.
`ReLUNet.output T` is a network with `0` hidden layers (just the affine map `T : ℝ^n → ℝ`,
i.e. `T^(1)` alone). `ReLUNet.layer T rest` prepends an affine map `T : ℝ^n → ℝ^m`
and a ReLU nonlinearity to a network `rest` with `k` hidden layers on `ℝ^m`, producing a
network with `k + 1` hidden layers on `ℝ^n`. This encodes exactly the alternating
composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`. -/
inductive ReLUNet : ℕ → ℕ → Type
  | output {n : ℕ} (T : AffineMap' n 1) : ReLUNet n 0
  | layer {n m k : ℕ} (T : AffineMap' n m) (rest : ReLUNet m k) : ReLUNet n (k + 1)

/-- The function `ℝ^n → ℝ` computed by a ReLU network. -/
noncomputable def ReLUNet.eval : ∀ {n k : ℕ}, ReLUNet n k → (Fin n → ℝ) → ℝ
  | _, _, ReLUNet.output T, x => T.eval x 0
  | _, _, ReLUNet.layer T rest, x => rest.eval (reluVec (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
**at most** `k` hidden layers (see the discussion above for why "at most" rather than
"exactly" is the reading that makes Theorem 2 correct). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ j ≤ k, ∃ N : ReLUNet n j, f = N.eval}

/-- A scalar affine function `ℝ^n → ℝ`, `x ↦ ⟨a, x⟩ + b`. -/
structure ScalarAffine (n : ℕ) where
  a : Fin n → ℝ
  b : ℝ

/-- Evaluation of a scalar affine function. -/
def ScalarAffine.eval {n : ℕ} (g : ScalarAffine n) (x : Fin n → ℝ) : ℝ :=
  (∑ i, g.a i * x i) + g.b

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: those that are
continuous and, at every point, locally agree with one of a finite family of scalar affine
functions. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (g : Fin m → ScalarAffine n),
      ∀ x : Fin n → ℝ, ∃ i : Fin m, ∀ᶠ y in nhds x, f y = (g i).eval y}

/-- The depth bound `⌈log₃(n - 1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so `n - 1 ≥ 2`). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL n = ReLUn n (⌈log₃(n-1)⌉ + 1)`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent018


namespace Agent019

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

Modelling choices (see final summary):
* Vectors `ℝ^n` are encoded as `Fin n → ℝ`.
* An affine map `ℝ^a → ℝ^b` is encoded concretely as a pair `(A, b)` with
  `A : Matrix (Fin b) (Fin a) ℝ` and `b : Fin b → ℝ`, acting by `x ↦ A.mulVec x + b`.
* A ReLU network with exactly `k` hidden layers is bundled as a structure
  `ReLUNetwork n k` carrying the sequence of layer widths (`widths 0 = n`,
  `widths (k+1) = 1`) together with the `k+1` affine maps `T^(1), …, T^(k+1)`
  between consecutive widths; `ReLUNetwork.eval` unfolds the alternating
  composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`.
* `ReLUn n k` is the set of functions representable with **at most** `k`
  hidden layers (the standard reading in the literature; it coincides with
  "exactly `k`" up to padding by trivial identity-computing layers, so either
  convention makes Theorem 2 true).
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of
  affine functions such that `f` locally agrees with (at least) one member of
  that family in a neighbourhood of every point. This is a genuine
  piecewise-linearity condition (finitely many affine "pieces" that patch
  together to a globally continuous function), not a max-of-affine normal
  form and not "representable by some ReLU network".
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined via `Real.logb 3` and
  `Nat.ceil` on the real number `(n : ℝ) - 1`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, encoded concretely as a matrix
together with a bias vector. -/
def AffineMap' (a b : ℕ) : Type := Matrix (Fin b) (Fin a) ℝ × (Fin b → ℝ)

/-- The function `ℝ^a → ℝ^b` computed by an affine transformation. -/
def AffineMap'.apply {a b : ℕ} (T : AffineMap' a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (Matrix.mulVec T.1 x) i + T.2 i

/-- A ReLU network with input dimension `n` and exactly `k` hidden layers:
a sequence of `k + 2` widths `widths 0 = n, widths 1, …, widths k, widths (k+1) = 1`
together with `k + 1` affine transformations `T^(i) : ℝ^{widths (i-1)} → ℝ^{widths i}`
for `i = 1, …, k + 1` (here indexed from `0` to `k`). -/
structure ReLUNetwork (n k : ℕ) where
  /-- The width of each layer, `0` (the input layer) through `k + 1` (the output layer). -/
  widths : ℕ → ℕ
  width_zero : widths 0 = n
  width_last : widths (k + 1) = 1
  /-- The affine transformation `T^(i+1) : ℝ^{widths i} → ℝ^{widths (i+1)}`, for `i ≤ k`. -/
  layer : (i : ℕ) → i < k + 1 → AffineMap' (widths i) (widths (i + 1))

/-- The vector produced at layer `i` (for `0 ≤ i ≤ k + 1`) when the network `net`
is run on input `x`. `ReLU` is applied after every layer except the last one,
matching the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`. -/
def ReLUNetwork.vecAt {n k : ℕ} (net : ReLUNetwork n k) (x : Fin n → ℝ) :
    (i : ℕ) → Fin (net.widths i) → ℝ
  | 0 => net.width_zero.symm ▸ x
  | i + 1 =>
      if h : i < k + 1 then
        let y := (net.layer i h).apply (net.vecAt x i)
        if i < k then reluVec y else y
      else
        fun _ => 0

/-- The real number computed by the network `net` on input `x`. -/
def ReLUNetwork.eval {n k : ℕ} (net : ReLUNetwork n k) (x : Fin n → ℝ) : ℝ :=
  (net.width_last ▸ net.vecAt x (k + 1)) ⟨0, by omega⟩

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network
with at most `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, ∃ net : ReLUNetwork n k', ∀ x, f x = net.eval x}

/-- An affine function `ℝ^n → ℝ`. -/
def IsAffineFun {n : ℕ} (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x, g x = (∑ i, a i * x i) + b

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`:
`f` is continuous, and there is a finite family of affine functions such that
`f` coincides with (at least) one member of that family on a neighbourhood
of every point. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ),
      (∀ j, IsAffineFun (g j)) ∧
      ∀ x : Fin n → ℝ, ∃ j, ∃ U ∈ nhds x, ∀ y ∈ U, f y = g j y}

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from Theorem 2. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL n = ReLUn n (⌈log₃(n-1)⌉ + 1)`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent019


namespace Agent021

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

"Better Neural Network Expressivity: Subdividing the Simplex"
(Bakaev, Brunck, Hertrich, Stade, Yehudayoff)

Theorem 2. For n ≥ 3, CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}.

## Modelling choices

* Vectors `ℝ^n` are encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^n → ℝ^m` is modelled concretely as a pair `(A, b)` with
  `A : Matrix (Fin m) (Fin n) ℝ` and `b : Fin m → ℝ`, acting by `x ↦ A.mulVec x + b`.
* A ReLU network with `k` hidden layers computing `f : ℝ^n → ℝ` is modelled by the
  inductive predicate `ComputesReLU n k f`, which unwinds exactly the alternating
  composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper: the base case
  `k = 0` is a single affine map to `ℝ^1`, and the inductive step prepends one affine map
  `ℝ^n → ℝ^m` followed by a componentwise ReLU to a network already computing a function
  of `k` hidden layers on `ℝ^m`.
* `ReLUn n k` is taken to be the functions representable with **at most** `k` hidden
  layers (not exactly `k`). This is the standard reading in the expressivity literature,
  and it is the reading under which `ReLUn n k ⊆ ReLUn n (k+1)` holds and Theorem 2 is a
  sensible equality (a network with more hidden layers can always simulate one with fewer,
  e.g. by inserting extra affine layers realizing the identity via `x = ReLU x - ReLU(-x)`
  composed appropriately; we do not prove this fact here, we only fix the convention).
* `CPWL n` is defined honestly: `f` is continuous, and there is a *finite* collection of
  polyhedra (each cut out as a finite intersection of affine half-spaces) covering `ℝ^n`,
  on each of which `f` agrees with some affine function. This is a genuine
  piecewise-linearity condition, independent of any notion of ReLU network.
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined via the real logarithm `Real.logb 3` and
  `Nat.ceil` (`⌈·⌉₊`), matching the statement verbatim.
-/

/-- The scalar ReLU function. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^n`. -/
def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^n → ℝ^m`, given concretely by a matrix and a bias vector. -/
structure AffineMap (n m : ℕ) where
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ

/-- The function `ℝ^n → ℝ^m` computed by an affine transformation. -/
def AffineMap.apply {n m : ℕ} (T : AffineMap n m) (x : Fin n → ℝ) : Fin m → ℝ :=
  T.A.mulVec x + T.b

/-- `ComputesReLU n k f` holds when `f : ℝ^n → ℝ` is computed by a ReLU network with
exactly `k` hidden layers, i.e. by the alternating composition of `k + 1` affine
transformations with componentwise ReLU applications in between, as in the paper:
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`.

* Base case (`k = 0`, depth 1, no hidden layers): a single affine map `ℝ^n → ℝ^1`.
* Step case: prepend an affine map `ℝ^n → ℝ^m` and a componentwise ReLU to a network
  already computing a function `g : ℝ^m → ℝ` with `k` hidden layers. -/
inductive ComputesReLU : ∀ (n k : ℕ), ((Fin n → ℝ) → ℝ) → Prop
  | base {n : ℕ} (T : AffineMap n 1) :
      ComputesReLU n 0 (fun x => T.apply x 0)
  | step {n m k : ℕ} (T : AffineMap n m) {g : (Fin m → ℝ) → ℝ} (hg : ComputesReLU m k g) :
      ComputesReLU n (k + 1) (fun x => g (reluVec (T.apply x)))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
**at most** `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, ComputesReLU n k' f }

/-- A subset of `ℝ^n` is a (closed) polyhedron if it is a finite intersection of affine
half-spaces `{x | ⟨c, x⟩ ≤ d}`. -/
def IsPolyhedron (n : ℕ) (P : Set (Fin n → ℝ)) : Prop :=
  ∃ (M : ℕ) (c : Fin M → Fin n → ℝ) (d : Fin M → ℝ),
    P = {x : Fin n → ℝ | ∀ l : Fin M, (∑ j, c l j * x j) ≤ d l}

/-- `CPWL n` is the space of continuous piecewise-linear functions `ℝ^n → ℝ`: those that
are continuous and admit a finite polyhedral subdivision of `ℝ^n` on each piece of which
the function agrees with some affine function. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (N : ℕ) (P : Fin N → Set (Fin n → ℝ)) (a : Fin N → (Fin n → ℝ)) (b : Fin N → ℝ),
          (∀ i, IsPolyhedron n (P i)) ∧
          (⋃ i, P i) = Set.univ ∧
          (∀ i, ∀ x ∈ P i, f x = (∑ j, a i j * x j) + b i) }

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from the theorem statement, for `n ≥ 3` (so that
`n - 1 ≥ 2 > 0` and the logarithm is well-behaved). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent021


namespace Agent022

/-!
Formalization of Theorem 2 of arXiv:2505.14338
("Better Neural Network Expressivity: Subdividing the Simplex").

Modelling choices:
* `ℝ^n` is encoded as `Fin n → ℝ`.
* An affine map `ℝ^a → ℝ^b` is encoded concretely as a matrix `A` together with a bias
  vector `c`, applied as `x ↦ A.mulVec x + c`.
* A ReLU network with *exactly* `k` hidden layers computing `f : ℝ^n → ℝ` is defined
  recursively: `k = 0` means `f` itself is affine (a single affine transform, the
  "depth 1 / 0 hidden layers" base case); `k+1` means `f` is obtained by first applying
  an affine transform `T : ℝ^n → ℝ^m`, then componentwise ReLU, then a function `g`
  computable with `k` hidden layers, i.e. `f = g ∘ reluVec ∘ T.apply`.
* `ReLUn n k` is taken to be functions representable with **at most** `k` hidden layers
  (the union over `j ≤ k` of "exactly `j`"), which is the standard reading in this
  literature: extra hidden layers can always simulate fewer, so `ReLU_{n,k}` naturally
  forms an increasing chain in `k`, and this is the reading under which Theorem 2 (an
  equality with a *specific* depth) is meaningful and true.
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family (indexed by
  `Fin m`) of affine functions (weight vector + bias) such that every point has a
  neighborhood on which `f` coincides with one of these affine functions. This is a
  genuine local piecewise-affinity condition (not a max/min-of-affine normal form, and
  not "representable by some ReLU network").
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded with `Real.logb 3` and `Nat.ceil`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias
vector. -/
structure AffineMap' (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def AffineMap'.apply {a b : ℕ} (T : AffineMap' a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `f : ℝ^n → ℝ` is computed by a ReLU network with **exactly** `k` hidden layers:
`k = 0` is a single affine transform (`T^(1)`, depth 1, 0 hidden layers); the step case
prepends an affine transform followed by a componentwise ReLU to a network with `k`
hidden layers computing the rest. -/
def ExactReLUComputable : ℕ → (n : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | 0, n, f => ∃ w : Fin n → ℝ, ∃ b : ℝ, ∀ x, f x = (∑ j, w j * x j) + b
  | (k + 1), n, f =>
      ∃ (m : ℕ) (T : AffineMap' n m) (g : (Fin m → ℝ) → ℝ),
        ExactReLUComputable k m g ∧ f = g ∘ reluVec ∘ T.apply

/-- `ReLUn n k`: functions `ℝ^n → ℝ` representable by a ReLU network with **at most**
`k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ j ≤ k, ExactReLUComputable j n f }

/-- `CPWL n`: continuous functions `ℝ^n → ℝ` that are, near every point, equal to one of
finitely many affine functions (a genuine local piecewise-linearity condition). -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
      ∃ (m : ℕ) (w : Fin m → Fin n → ℝ) (b : Fin m → ℝ),
        ∀ x : Fin n → ℝ, ∃ i : Fin m, ∃ U ∈ nhds x, ∀ y ∈ U, f y = (∑ j, w i j * y j) + b i }

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from the theorem statement. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent022


namespace Agent023

/-! ## ReLU activation -/

/-- The ReLU activation function on `ℝ`. -/
noncomputable def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU applied to a vector in `ℝ^m`, encoded as `Fin m → ℝ`. -/
noncomputable def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-! ## Affine transformations -/

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix `A` and a bias
    vector `c`, computing `x ↦ A * x + c`. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
noncomputable def AffineMap.eval {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- A function `ℝ^n → ℝ` is affine (scalar-valued affine transformation). -/
def IsAffineFun {n : ℕ} (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), g = fun x => (∑ i, a i * x i) + b

/-! ## Functions computed by a ReLU network -/

/-- `IsReLUNetworkFunc k n f` says that `f : ℝ^n → ℝ` is *computed* by a ReLU network
    with exactly `k` hidden layers, i.e. by the alternating composition
    `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`
    of `k + 1` affine transformations `T^(1), …, T^(k+1)`, with componentwise ReLU applied
    between consecutive affine transformations (and no ReLU after the last one, since the
    output is a single real number).

    We define this by recursion on `k`:
    * with `0` hidden layers, the network is just a single affine transformation
      `T^(1) : ℝ^n → ℝ` (a depth-1 network with no hidden layers);
    * with `k + 1` hidden layers, we first apply an affine transformation
      `T^(1) : ℝ^n → ℝ^m` to the input, then ReLU componentwise, and the remaining
      `k` hidden layers (given by `T^(2), …, T^(k+1)`) act on the `m`-dimensional result. -/
def IsReLUNetworkFunc : (k n : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | 0, _n, f => IsAffineFun f
  | (k + 1), n, f =>
      ∃ (m : ℕ) (T : AffineMap n m) (g : (Fin m → ℝ) → ℝ),
        IsReLUNetworkFunc k m g ∧ f = fun x => g (reluVec (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
    *at most* `k` hidden layers.

    Modelling choice: we read `ReLU_{n,k}` as "at most `k` hidden layers" rather than
    "exactly `k` hidden layers". This is the reading under which `ReLUn n k` is monotone
    in `k` (`ReLUn n k ⊆ ReLUn n (k+1)`, since one can always spend extra hidden layers
    without being forced to use them), which is the natural reading needed for
    `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉+1}` to assert that every CPWL function needs *at most*
    that many hidden layers (the content of Theorem 2), rather than the much stronger and
    false-looking claim that every CPWL function needs *exactly* that many. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, IsReLUNetworkFunc k' n f}

/-! ## Continuous piecewise-linear functions -/

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: those that
    are continuous, and for which there is a finite family of affine functions such that
    every point of `ℝ^n` has an open neighbourhood on which `f` agrees with one of them.
    This is a genuine local piecewise-affine condition, not a "max of affine functions"
    normal form and not a "representable by some ReLU network" reformulation. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
       ∃ (m : ℕ) (g : Fin m → ((Fin n → ℝ) → ℝ)),
         (∀ j, IsAffineFun (g j)) ∧
         ∀ x : Fin n → ℝ, ∃ j : Fin m, ∃ U : Set (Fin n → ℝ),
           IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, f y = g j y}

/-! ## The depth bound of Theorem 2 -/

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so `n - 1 ≥ 2 > 0`
    and the real logarithm `Real.logb 3 (n - 1)` is well-behaved). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-! ## Theorem 2 -/

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉+1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent023


namespace Agent024

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We model an `n`-dimensional real vector as a function `Fin n → ℝ`.

An affine transformation `ℝ^a → ℝ^b` is modelled concretely as `x ↦ A.mulVec x + c`
for a matrix `A : Matrix (Fin b) (Fin a) ℝ` and a bias vector `c : Fin b → ℝ`.

A ReLU network with `k` hidden layers computing `f : (Fin n → ℝ) → ℝ` is modelled by
the inductive predicate `NetComputes n k f`, which unfolds exactly the alternating
composition
    `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ... ∘ ReLU ∘ T^(1)`
from the paper: the base case `k = 0` is a single affine map `n → 1` (no hidden
layers, no ReLU applied); the successor case peels off the first affine map
`T^(1) : n → m` together with the following componentwise ReLU, and recurses on a
network with `k` hidden layers from the (existentially quantified) intermediate
width `m`.

`ReLUn n k` is then the set of functions representable with **at most** `k` hidden
layers (the standard convention for this notation in the depth-separation
literature: `ReLU_{n,k}` is monotone increasing in `k`, since one can always pad a
shallower network with extra trivial affine+ReLU layers to reach exactly `k`
hidden layers without changing the represented function). With this convention
`CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}` says: every CPWL function on `ℝ^n` is
representable with at most that many hidden layers (and, trivially, every function
representable with that many hidden layers is CPWL).

`CPWL n` is defined as the continuous functions that are, near every point, equal
to one of finitely many affine functions (a genuine local piecewise-linearity
condition on a finite family of affine pieces — not defined via ReLU networks and
not via a max-of-affines normal form).
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector. -/
def reluVec {m : ℕ} (v : Fin m → ℝ) : Fin m → ℝ := fun i => relu (v i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias
vector. -/
structure Affine (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- The function computed by an affine transformation. -/
def Affine.toFun {a b : ℕ} (T : Affine a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `NetComputes n k f` holds iff `f : (Fin n → ℝ) → ℝ` is computed by some ReLU
network with input dimension `n`, exactly `k` hidden layers, and output dimension
`1`, i.e. by some alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`
of affine transformations `T^(1), …, T^(k+1)` (with the intermediate widths
`n_1, …, n_k` existentially quantified). -/
inductive NetComputes : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop where
  /-- Zero hidden layers: the network is a single affine map `T^(1) : ℝ^n → ℝ`. -/
  | base {n : ℕ} (T : Affine n 1) :
      NetComputes n 0 (fun x => T.toFun x 0)
  /-- `k + 1` hidden layers: apply the first affine map `T^(1) : ℝ^n → ℝ^m`,
  then componentwise ReLU, then recurse on a network with `k` hidden layers
  from the intermediate width `m`. -/
  | step {n m k : ℕ} (T : Affine n m) {f : (Fin m → ℝ) → ℝ}
      (hf : NetComputes m k f) :
      NetComputes n (k + 1) (fun x => f (reluVec (T.toFun x)))

/-- The set of functions `ℝ^n → ℝ` representable by a ReLU network with **at most**
`k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, NetComputes n k' f}

/-- The space of continuous piecewise linear functions `ℝ^n → ℝ`: continuous
functions that, in a neighbourhood of every point, coincide with one of finitely
many affine functions. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ N : ℕ, ∃ pieces : Fin N → Affine n 1,
      ∀ x : Fin n → ℝ, ∃ i : Fin N, ∀ᶠ y in nhds x, f y = (pieces i).toFun y 0}

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from the theorem, with the ceiling of the
real logarithm base `3` taken via `Nat.ceil`. -/
def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, the continuous piecewise linear functions on `ℝ^n`
are exactly those representable by a ReLU network with at most
`⌈log_3(n - 1)⌉ + 1` hidden layers. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent024


namespace Agent025

/-!
# Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity: Subdividing the
Simplex"), formalized.

We encode `ℝ^n` concretely as `Fin n → ℝ`.

## Modelling choices

* Affine maps `ℝ^a → ℝ^b` are given concretely by a matrix `A : Matrix (Fin b) (Fin a) ℝ`
  and a bias vector `c : Fin b → ℝ`, acting as `x ↦ A * x + c`.
* A ReLU network computing `f : (Fin n → ℝ) → ℝ` with `k` hidden layers is encoded by the
  recursive predicate `NetworkComputable`, which unwinds exactly to the alternating
  composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper, where the
  intermediate widths `n_1, …, n_k` are existentially quantified.
* `ReLUn n k` is the set of functions representable by a network with *exactly* `k`
  hidden layers (this matches the literal architecture described in the paper: "the
  subset of CPWL_n representable with k hidden layers"). Note that this is *not* a real
  restriction relative to an "at most k" reading: since `ReLU (t) - ReLU (-t) = t`, an
  identity map on any coordinate can be simulated by one extra ReLU hidden layer, so a
  network with `k` hidden layers can always be padded to one with `k+1` hidden layers
  computing the same function. Hence `ReLUn n k ⊆ ReLUn n (k+1)` in general, and the two
  readings of the theorem statement agree.
* `CPWL n` is defined mathematically (not via ReLU networks, and not as a "max of
  finitely many affine functions" normal form): `f` is continuous, and there is a finite
  family of affine functions such that `f` locally agrees with (at least) one of them
  near every point. This is a standard formulation of "continuous, finitely
  piecewise-affine".
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined using the real logarithm `Real.logb 3`
  and `Nat.ceil`.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of ReLU to a vector in `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given by a matrix and a bias vector,
acting as `x ↦ A * x + c`. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- The function `ℝ^a → ℝ^b` computed by an affine transformation. -/
def AffineMap.apply {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, T.A i j * x j) + T.c i

/-- `NetworkComputable n k f` means that `f : ℝ^n → ℝ` is computed by *some* ReLU network
with exactly `k` hidden layers, i.e. `f` is the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of affine transformations `T^(1), …, T^(k+1)`
with componentwise ReLU applications, for some choice of intermediate widths
`n_1, …, n_k`.

The recursion peels off the first hidden layer: with `k + 1` hidden layers, `f` factors
as `g ∘ ReLU ∘ T^(1)` where `T^(1) : ℝ^n → ℝ^m` is affine (for some hidden width `m`) and
`g : ℝ^m → ℝ` is itself computable with the remaining `k` hidden layers. The base case
`k = 0` is a single affine transformation `ℝ^n → ℝ^1`. -/
def NetworkComputable : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : AffineMap n 1, ∀ x, f x = T.apply x 0
  | n, k + 1, f =>
      ∃ (m : ℕ) (T : AffineMap n m) (g : (Fin m → ℝ) → ℝ),
        NetworkComputable m k g ∧ ∀ x, f x = g (reluVec (T.apply x))

/-- `ReLUn n k`, the subset of `CPWL_n` (indeed, of all functions `ℝ^n → ℝ`) representable
by a ReLU network with exactly `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | NetworkComputable n k f }

/-- An affine function `ℝ^n → ℝ`, given by a coefficient vector and a constant term. -/
def IsAffine (n : ℕ) (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (c : ℝ), ∀ x, g x = (∑ j, a j * x j) + c

/-- `CPWL n`, the space of continuous piecewise-linear (CPWL) functions `ℝ^n → ℝ`: `f` is
continuous, and there is a *finite* family of affine functions such that `f` agrees with
(at least) one member of the family on a neighborhood of every point. This is a genuine
piecewise-linearity condition (a finite "atlas" of affine pieces covering `ℝ^n`), not a
disguised max-of-affine normal form and not defined via ReLU networks. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
      ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ),
        (∀ i, IsAffine n (g i)) ∧
        ∀ x : Fin n → ℝ, ∃ i, ∀ᶠ y in nhds x, f y = g i y }

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from the theorem statement, for `n ≥ 3` (so that
`n - 1 ≥ 2` and the logarithm is well-defined and positive). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent025


namespace Agent026

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We encode `ℝ^n` concretely as `Fin n → ℝ`.

## Modelling choices (see summary at call site)

* `relu` is `max 0 ·` on `ℝ`; `reluVec` applies it componentwise.
* An affine map `ℝ^a → ℝ^b` is a pair `(A, c)` with `A : Matrix (Fin b) (Fin a) ℝ`
  and `c : Fin b → ℝ`, acting as `x ↦ A.mulVec x + c` (spelled out with a `Finset.sum`
  to avoid extra `Matrix` API dependencies).
* A ReLU network with exactly `k` hidden layers, input dimension `n`, output dimension
  `m`, is encoded by the recursively defined type `NetParams n m k`: for `k = 0` it is
  a single affine map `ℝ^n → ℝ^m` (depth 1, 0 hidden layers); for `k+1` it is a choice of
  hidden width `h`, an affine map `ℝ^n → ℝ^h`, and a `(h, m, k)`-network for the rest.
  `NetParams.eval` unfolds this exactly as the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`.
* `ReLUn n k` is taken to be the set of functions representable with **at most** `k`
  hidden layers (existentially quantifying `k' ≤ k`). This is the standard reading in
  the depth-separation literature: it makes `ReLUn n ·` monotone nondecreasing in `k`,
  so that the equality `CPWL n = ReLUn n (⌈log_3(n-1)⌉+1)` expresses "this many hidden
  layers already suffice to reach the full class `CPWL n`, and no representable function
  ever leaves that class" — the natural way to read `MAX_{3^n+2} ∈ ReLU_{n+1}` extending
  monotonically. (Reading it as *exactly* `k` would make the statement false or
  ill-behaved for trivial reasons, e.g. constant functions needing padding layers.)
* `CPWL n` is defined as: `f` is continuous **and** there is a finite family of
  polyhedra (finite intersections of affine half-spaces) covering `ℝ^n`, on each of
  which `f` agrees with some affine function. This is a genuine piecewise-linearity
  condition (a finite polyhedral subdivision), not a max-of-affine normal form and not
  "representable by a ReLU network".
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined literally with `Real.logb 3` and
  `Nat.ceil` (`⌈·⌉₊`).
-/

noncomputable section

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^n`. -/
def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given by a matrix and a bias vector. -/
def AffineMap' (a b : ℕ) : Type := Matrix (Fin b) (Fin a) ℝ × (Fin b → ℝ)

/-- Evaluate an affine transformation `x ↦ A x + c`. -/
def applyAffine {a b : ℕ} (T : AffineMap' a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, T.1 i j * x j) + T.2 i

/-- Parameters of a ReLU network with input dimension `n`, output dimension `m`,
and exactly `k` hidden layers: for `k = 0` a single affine map, for `k + 1` a hidden
width `h`, an affine map `ℝ^n → ℝ^h`, together with the parameters of the remaining
`(h, m, k)`-network (to be composed with `ReLU` in between). -/
def NetParams (n m : ℕ) : ℕ → Type
  | 0 => AffineMap' n m
  | k + 1 => Σ h : ℕ, AffineMap' n h × NetParams h m k

/-- The function `ℝ^n → ℝ^m` computed by a ReLU network, i.e. the alternating
composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`. -/
def NetParams.eval {n m : ℕ} : (k : ℕ) → NetParams n m k → (Fin n → ℝ) → (Fin m → ℝ)
  | 0, T, x => applyAffine T x
  | k + 1, ⟨_, T, rest⟩, x => NetParams.eval k rest (reluVec (applyAffine T x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network
with **at most** `k` hidden layers (output dimension `1`). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, ∃ P : NetParams n 1 k', f = fun x => NetParams.eval k' P x 0 }

/-- A polyhedron in `ℝ^n`: a finite intersection of closed affine half-spaces. -/
def IsPolyhedron {n : ℕ} (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (a : Fin m → (Fin n → ℝ)) (b : Fin m → ℝ),
    S = ⋂ i, {x : Fin n → ℝ | (∑ j, a i j * x j) ≤ b i}

/-- `CPWL n` is the set of continuous, piecewise affine functions `ℝ^n → ℝ`: those `f`
that are continuous and admit a finite polyhedral subdivision of `ℝ^n` on each piece of
which `f` agrees with some affine function. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
      ∃ (m : ℕ) (S : Fin m → Set (Fin n → ℝ)) (A : Fin m → (Fin n → ℝ)) (c : Fin m → ℝ),
        (∀ i, IsPolyhedron (S i)) ∧
        (⋃ i, S i) = Set.univ ∧
        ∀ i, ∀ x ∈ S i, f x = (∑ j, A i j * x j) + c i }

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from the theorem statement. -/
def depthBound (n : ℕ) : ℕ := ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

end

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉+1}`. -/
theorem theorem2 : ∀ n : ℕ, n ≥ 3 → CPWL n = ReLUn n (depthBound n) := sorry

end Agent026


namespace Agent028

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):  for `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`.

## Modelling choices

* `ℝ^n` is encoded as `Fin n → ℝ`.
* Affine transformations `ℝ^a → ℝ^b` are given concretely by a weight matrix (as a
  function `Fin b → Fin a → ℝ`) and a bias vector `Fin b → ℝ`, acting as `x ↦ A x + c`.
* A ReLU network with `k` hidden layers, input dimension `n` and output dimension `m` is
  modelled by the recursively defined predicate `IsReLUNetFun`, mirroring the alternating
  composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper: `k = 0` hidden
  layers means a single affine map, and `k+1` hidden layers means an affine map into some
  hidden width `h`, followed by (componentwise) ReLU, followed by a network with `k` hidden
  layers from `h` to `m`.
* `ReLUn n k` is the set of scalar functions `ℝ^n → ℝ` representable by a network with
  *at most* `k` hidden layers (this is the reading under which Theorem 2, an equality of
  sets, is true: adding extra hidden layers never removes representability, so the classes
  `ReLU_{n,k}` are monotone increasing in `k`).
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of affine
  functions `ℝ^n → ℝ` such that every point of `ℝ^n` has a neighbourhood on which `f` agrees
  with one member of the family. This is a genuine piecewise-linearity condition (not a
  disguised "representable by a ReLU network" or "max of finitely many affine functions"
  definition).
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded using `Real.logb 3` and `Nat.ceil`, applied
  to the natural number `n - 1` (well-behaved since `n ≥ 3` gives `n - 1 ≥ 2`).
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given by a matrix `A` (as a function of indices)
and a bias vector `c`, acting as `x ↦ A x + c`. -/
structure Affine (a b : ℕ) where
  A : Fin b → Fin a → ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def Affine.apply {a b : ℕ} (T : Affine a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, T.A i j * x j) + T.c i

/-- `IsReLUNetFun k n m f` means the function `f : ℝ^n → ℝ^m` is *exactly* computed by a
ReLU network with `k` hidden layers, i.e. by an alternating composition of `k + 1` affine
transformations and `k` componentwise ReLU applications:
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`. -/
def IsReLUNetFun : (k n m : ℕ) → ((Fin n → ℝ) → (Fin m → ℝ)) → Prop
  | 0, n, m, f => ∃ T : Affine n m, f = T.apply
  | (k + 1), n, m, f =>
      ∃ (h : ℕ) (T : Affine n h) (g : (Fin h → ℝ) → (Fin m → ℝ)),
        IsReLUNetFun k h m g ∧ f = g ∘ reluVec ∘ T.apply

/-- `ReLUn n k` is the set of scalar functions `ℝ^n → ℝ` representable by a ReLU network
with *at most* `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, IsReLUNetFun k' n 1 (fun x _ => f x) }

/-- An affine (scalar-valued) function `ℝ^n → ℝ`, given by a weight vector and a bias. -/
structure AffineFunc (n : ℕ) where
  w : Fin n → ℝ
  b : ℝ

/-- Evaluation of a scalar affine function. -/
def AffineFunc.eval {n : ℕ} (T : AffineFunc n) (x : Fin n → ℝ) : ℝ :=
  (∑ i, T.w i * x i) + T.b

/-- `CPWL n` is the set of continuous, piecewise linear functions `ℝ^n → ℝ`: those that are
continuous and, near every point, agree with one of finitely many affine functions. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (ι : Type) (_ : Fintype ι) (T : ι → AffineFunc n),
          ∀ x : Fin n → ℝ, ∃ i : ι, Filter.Eventually (fun y => f y = (T i).eval y) (nhds x) }

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from the paper, for `n - 1 ≥ 2` (i.e. `n ≥ 3`). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n - 1 : ℕ) : ℝ)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent028


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
def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end

end Agent029


namespace Agent030

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We encode `ℝ^n` as `Fin n → ℝ`.

## Modelling choices (see summary at the end)

* Vectors: `Fin n → ℝ`.
* Affine maps `ℝ^a → ℝ^b` are given concretely as `x ↦ A.mulVec x + c` for a matrix
  `A : Matrix (Fin b) (Fin a) ℝ` and bias `c : Fin b → ℝ`.
* "Computes with `k` hidden layers" is defined by recursion on `k`, directly mirroring the
  alternating composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper.
* `ReLUn n k` is taken to mean *representable with at most `k` hidden layers* (monotone in
  `k`), since that is the reading under which Theorem 2 (an equality, not just an inclusion)
  is the correct/true statement: `CPWL_n` is exhausted already at depth bound `K`, and more
  hidden layers do not produce functions outside `CPWL_n`.
* `CPWL n` is defined as: continuous, and admitting a *finite polyhedral subdivision*
  covering `ℝ^n` (each piece a finite intersection of closed halfspaces) on each piece of
  which `f` agrees with some affine function. This is a genuine geometric definition, not a
  "max of affines" normal form and not "representable by some ReLU network".
* The depth bound uses the real `Real.logb 3` composed with `Nat.ceil`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b` given by a matrix `A` and bias vector `c`,
applied concretely as `x ↦ A * x + c`. -/
def affineMap {a b : ℕ} (A : Matrix (Fin b) (Fin a) ℝ) (c : Fin b → ℝ) :
    (Fin a → ℝ) → (Fin b → ℝ) :=
  fun x => A.mulVec x + c

/-- `f` is affine (as a scalar-valued function `ℝ^n → ℝ`): it equals `a ⬝ x + c` for some
fixed coefficient vector `a` and constant `c`. -/
def IsAffineFn (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (c : ℝ), ∀ x : Fin n → ℝ, f x = (∑ i, a i * x i) + c

/-- A closed halfspace `{x | a ⬝ x ≤ b}` in `ℝ^n`. -/
def IsHalfspace (n : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), S = {x : Fin n → ℝ | (∑ i, a i * x i) ≤ b}

/-- A (closed, possibly unbounded) polyhedron: a finite intersection of closed halfspaces. -/
def IsPolyhedron (n : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (l : ℕ) (H : Fin l → Set (Fin n → ℝ)), (∀ j, IsHalfspace n (H j)) ∧ S = ⋂ j, H j

/-- The space of continuous piecewise-linear functions `ℝ^n → ℝ`: continuous functions that
admit a finite polyhedral subdivision of `ℝ^n` on each piece of which the function is affine. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (P : Fin m → Set (Fin n → ℝ)) (g : Fin m → (Fin n → ℝ) → ℝ),
          (∀ i, IsPolyhedron n (P i)) ∧
          (∀ i, IsAffineFn n (g i)) ∧
          (⋃ i, P i) = Set.univ ∧
          (∀ i, ∀ x ∈ P i, f x = g i x) }

/-- `ComputesWithHiddenLayers n k f` means `f : ℝ^n → ℝ` is computed by a ReLU network with
exactly `k` hidden layers, i.e. by an alternating composition of `k + 1` affine
transformations `T^(1), …, T^(k+1)` with componentwise ReLU applied between consecutive ones:
`f = T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`.

The base case `k = 0` is a single affine map `ℝ^n → ℝ^1` (no hidden layer, no ReLU). The
successor case peels off the first affine map `T^(1) : ℝ^n → ℝ^m` together with the
following ReLU, and recurses on a network `g` with `k` hidden layers computing `ℝ^m → ℝ`. -/
def ComputesWithHiddenLayers : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f =>
      ∃ (A : Matrix (Fin 1) (Fin n) ℝ) (c : Fin 1 → ℝ),
        ∀ x : Fin n → ℝ, f x = affineMap A c x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ) (g : (Fin m → ℝ) → ℝ),
        ComputesWithHiddenLayers m k g ∧
          ∀ x : Fin n → ℝ, f x = g (reluVec (affineMap A c x))

/-- `ReLUn n k`: the functions `ℝ^n → ℝ` representable by a ReLU network with *at most* `k`
hidden layers. (See the modelling-choice note above for why "at most" rather than
"exactly" is the reading that makes Theorem 2 a true equality.) -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, ComputesWithHiddenLayers n k' f }

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2. -/
def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent030


namespace Agent031

/-
Modelling choices (see summary at the end of the task too):

* Vectors `ℝ^n` are encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is encoded concretely as a matrix `A : Matrix
  (Fin b) (Fin a) ℝ` together with a bias vector, evaluated as `x ↦ A * x + bias`.
* A ReLU network with `k` *hidden layers* computing `f : ℝ^n → ℝ` is defined by
  structural recursion on `k`:
    - `k = 0`: the network is a single affine map `ℝ^n → ℝ` (a "depth 1" network,
      i.e. `T^(1)` alone, no ReLU is ever applied).
    - `k+1`: the first hidden layer applies an affine map `T : ℝ^n → ℝ^m` followed by
      componentwise ReLU, and the resulting vector in `ℝ^m` feeds a network with `k`
      hidden layers (i.e. the remaining affine maps `T^(2), ..., T^(k+2)`).
  This exactly matches the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper.
* `ReLUn n k` is taken to be the set of functions representable with *at most* `k`
  hidden layers (an increasing union over `k' ≤ k`), which is the standard convention
  and the one under which `ReLU_{n,k}` is monotone in `k` (extra hidden layers can
  always simulate fewer, e.g. via the identity `x = ReLU(x) - ReLU(-x)`), matching the
  intended reading of Theorem 2.
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of affine
  functions `ℝ^n → ℝ` such that every point of `ℝ^n` has a neighbourhood on which `f`
  agrees with (at least) one member of the family. This is a genuine local
  piecewise-linearity condition, not a "max of affine functions" formula and not
  "representable by some ReLU network".
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded using `Real.logb 3` and `Nat.ceil`
  (notation `⌈·⌉₊`).
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on vectors. -/
def reluVec {m : ℕ} (v : Fin m → ℝ) : Fin m → ℝ := fun i => relu (v i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias
vector. -/
structure AffineMap' (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  bias : Fin b → ℝ

/-- Evaluation of an affine transformation: `x ↦ A * x + bias`. -/
def AffineMap'.eval {a b : ℕ} (T : AffineMap' a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, T.A i j * x j) + T.bias i

/-- `IsReLUComputable n k f` means `f : ℝ^n → ℝ` is computed by a ReLU network with
exactly `k` hidden layers, i.e. by the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations
`T^(1), ..., T^(k+1)`, with componentwise ReLU applied after each of the first `k` of
them. Defined by recursion on `k`, peeling off the first hidden layer at each step. -/
def IsReLUComputable : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : AffineMap' n 1, ∀ x, f x = T.eval x 0
  | n, k + 1, f =>
      ∃ (m : ℕ) (T : AffineMap' n m) (g : (Fin m → ℝ) → ℝ),
        IsReLUComputable m k g ∧ ∀ x, f x = g (reluVec (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, IsReLUComputable n k' f}

/-- `CPWL n` is the set of continuous, piecewise linear functions `ℝ^n → ℝ`: those that
are continuous and locally agree, near every point, with one of finitely many affine
functions. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (T : Fin m → AffineMap' n 1),
      ∀ x : Fin n → ℝ, ∃ i : Fin m, ∃ ε : ℝ, ε > 0 ∧
        ∀ y : Fin n → ℝ, dist y x < ε → f y = (T i).eval y 0}

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from the theorem statement. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) : CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent031


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


namespace Agent033

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We encode `ℝ^n` concretely as `Fin n → ℝ`.

Theorem 2 states: for `n ≥ 3`,
`CPWL_n = ReLU_{n, ⌈log_3 (n-1)⌉ + 1}`.

## Modelling choices (see summary at the end of the task)

* Vectors: `Fin n → ℝ`.
* Affine maps `ℝ^a → ℝ^b`: an explicit structure `x ↦ A * x + c` with `A` a matrix
  and `c` a vector.
* A ReLU network with `k` hidden layers computing `f : (Fin n → ℝ) → ℝ` is defined
  recursively on `k`: for `k = 0` it is a single affine map `n → 1`; for `k + 1` it is
  an affine map `n → m` followed by (componentwise) ReLU, followed by a `k`-hidden-layer
  network from `m` to the output. This exactly mirrors the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper.
* `ReLUn n k` is taken to be functions representable with *at most* `k` hidden layers
  (a union over `j ≤ k` of the "exactly `j`" sets). This is the reading under which
  `ReLUn n k` is monotone in `k` (extra layers can only help, e.g. by simulating the
  identity via `x = ReLU(x) - ReLU(-x)` on doubled width) and hence the equality with
  `CPWL_n` in Theorem 2 is the natural/true statement.
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of affine
  functions such that every point of `ℝ^n` has an open neighborhood on which `f`
  coincides with (at least) one member of the family. This is a genuine
  piecewise-linearity condition (not defined via ReLU-representability, and not a
  max-of-affine normal form).
* The depth bound `⌈log_3 (n-1)⌉ + 1` is defined via `Real.logb 3` and `Nat.ceil`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of ReLU to a vector. -/
def reluVec {k : ℕ} (x : Fin k → ℝ) : Fin k → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given explicitly by a matrix and a bias
vector: `x ↦ A * x + c`. -/
structure AffineMapRn (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine map. -/
def AffineMapRn.eval {a b : ℕ} (T : AffineMapRn a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `ComputesReLU n k f` means `f : ℝ^n → ℝ` is computed by a ReLU network with
exactly `k` hidden layers, i.e. `f = T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`
for some affine transformations `T^(1), …, T^(k+1)` of matching dimensions. -/
def ComputesReLU : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : AffineMapRn n 1, ∀ x, f x = T.eval x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : AffineMapRn n m) (g : (Fin m → ℝ) → ℝ),
        ComputesReLU m k g ∧ ∀ x, f x = g (reluVec (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network
with *at most* `k` hidden layers (see the discussion above for why "at most" is the
right reading). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ j ≤ k, ComputesReLU n j f }

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: `f` is
continuous, and there is a finite family of affine functions such that every point
has an open neighborhood on which `f` agrees with one member of the family. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (a : Fin m → (Fin n → ℝ)) (b : Fin m → ℝ),
          ∀ x : Fin n → ℝ, ∃ i : Fin m, ∃ U : Set (Fin n → ℝ),
            IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, f y = (∑ j, a i j * y j) + b i }

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from the theorem statement. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3 (n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent033


namespace Agent034

/-! ### Basic building blocks -/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^n`, encoded as `Fin n → ℝ`. -/
def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix `A` and a
translation vector `c`, acting as `x ↦ A * x + c`. -/
structure AffineMapRB (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def AffineMapRB.eval {a b : ℕ} (T : AffineMapRB a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, T.A i j * x j) + T.c i

/-- A function `ℝ^n → ℝ` is *affine* if it has the form `x ↦ ⟨w, x⟩ + b`. -/
def IsAffineFun {n : ℕ} (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (w : Fin n → ℝ) (b : ℝ), ∀ x, g x = (∑ i, w i * x i) + b

/-! ### ReLU networks -/

/-- `ReLUNet a b k` is (the data of) a ReLU network with input dimension `a`, output
dimension `b`, and `k` hidden layers, i.e. `k + 1` affine transformations
`T^(1), …, T^(k+1) : ℝ^{n_0} → ℝ^{n_1} → ⋯ → ℝ^{n_{k+1}}` (with `n_0 = a`,
`n_{k+1} = b`) composed with `ReLU` in between:
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`.
The `zero` constructor is a single affine transformation (`0` hidden layers,
depth `1`); the `succ` constructor prepends one more affine transformation
`T : ℝ^a → ℝ^m` followed by a `ReLU`, then continues with a network with one
fewer hidden layer from `ℝ^m` to `ℝ^b`. -/
inductive ReLUNet : ℕ → ℕ → ℕ → Type
  | zero {a b : ℕ} (T : AffineMapRB a b) : ReLUNet a b 0
  | succ {a m b k : ℕ} (T : AffineMapRB a m) (rest : ReLUNet m b k) : ReLUNet a b (k + 1)

/-- The function `ℝ^a → ℝ^b` computed by a ReLU network, obtained by unfolding the
alternating composition `T^(k+1) ∘ ReLU ∘ ⋯ ∘ ReLU ∘ T^(1)`. -/
def ReLUNet.eval {a b k : ℕ} (net : ReLUNet a b k) (x : Fin a → ℝ) : Fin b → ℝ :=
  match net with
  | ReLUNet.zero T => T.eval x
  | ReLUNet.succ T rest => rest.eval (reluVec (T.eval x))

/-- `ReLUn n k`: the functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers (output dimension `1`).

**Modelling choice (exactly-`k` vs at-most-`k`).** We use "at most `k`" rather
than "exactly `k`". A ReLU network with `k` hidden layers can always be
converted into one with `k + 1` hidden layers computing the *same* function
(e.g. prepend an extra affine layer `T = (I, 0)` acting as the identity on
`ℝ^{n_1}`, followed by a `ReLU` that changes nothing once one more coordinate
is added and subtracted back out by the following affine map); consequently
`ReLU_{n,k}` is monotone increasing in `k` under this reading. This monotonicity
is essential for Theorem 2 to be a meaningful equality: `CPWL n` is the
increasing union `⋃ k, ReLU_{n,k}` (by the discussion after Theorem 1, *every*
CPWL function needs only finitely many layers), and Theorem 2 pins down the
exact number of layers `⌈log_3(n-1)⌉ + 1` at which this union has already
stabilized to all of `CPWL n`. Under an "exactly `k`" reading the two sides of
the theorem could easily be unequal simply because some CPWL functions need
strictly *fewer* than the stated number of layers, which is not the intended
content of the theorem. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, ∃ net : ReLUNet n 1 k', ∀ x, f x = net.eval x 0}

/-! ### CPWL functions -/

/-- A function `f : ℝ^n → ℝ` is CPWL if it is continuous and there is a finite
subdivision of `ℝ^n` into polyhedral pieces `P 0, …, P (m-1)` — each piece cut
out by finitely many affine inequalities `⟨w, x⟩ + b ≤ 0` — covering `ℝ^n`, on
each of which `f` agrees with some affine function. This is a genuine
"continuous and piecewise affine on a finite polyhedral complex" definition:
it is *not* the same as "continuous and expressible as a max of finitely many
affine functions" (which would trivialize / assume the ReLU representation
result), and it does *not* refer to ReLU networks at all. -/
def IsCPWL {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  Continuous f ∧
  ∃ (m : ℕ) (P : Fin m → Set (Fin n → ℝ)) (A : Fin m → ((Fin n → ℝ) → ℝ)),
    (⋃ i, P i) = Set.univ ∧
    (∀ i, ∃ (ι : ℕ) (w : Fin ι → Fin n → ℝ) (b : Fin ι → ℝ),
        P i = {x | ∀ j, (∑ l, w j l * x l) + b j ≤ 0}) ∧
    (∀ i, IsAffineFun (A i)) ∧
    (∀ i, ∀ x ∈ P i, f x = A i x)

/-- `CPWL n`: the set of continuous piecewise-linear functions `ℝ^n → ℝ`. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) := {f | IsCPWL f}

/-! ### The depth bound `⌈log_3(n - 1)⌉ + 1` -/

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from Theorem 2. We use the genuine real
logarithm `Real.logb 3` together with `Nat.ceil` (notation `⌈·⌉₊`), which for a
nonnegative real argument computes exactly the mathematical ceiling; for
`n ≥ 3` we have `(n : ℝ) - 1 ≥ 2 > 0`, so this is well-behaved. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-! ### Theorem 2 -/

/-- **Theorem 2.** For `n ≥ 3`,
`CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`,
i.e. the continuous piecewise-linear functions on `ℝ^n` are exactly those
representable by a ReLU network with at most `⌈log_3(n-1)⌉ + 1` hidden layers. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent034


namespace Agent035

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

  "Better Neural Network Expressivity: Subdividing the Simplex"
  (Bakaev, Brunck, Hertrich, Stade, Yehudayoff)

  Theorem 2. For n ≥ 3, we have CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}.

## Modelling choices

* Vectors `ℝ^n` are encoded as `Fin n → ℝ`.
* An affine map `ℝ^a → ℝ^b` is encoded concretely as a matrix `A : Matrix (Fin b) (Fin a) ℝ`
  together with a bias vector `b : Fin b → ℝ`, acting via `x ↦ A.mulVec x + b`.
* A ReLU network with exactly `k` hidden layers, input dimension `a` and output dimension `c`
  is encoded as a dependent inductive family `NetLayers k a c` of `k + 1` affine layers, with
  a `relu` (componentwise) applied after every layer except the last (output) one. This
  literally mirrors the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper.
* `ReLUn n k` is taken to be the set of functions representable with **at most** `k` hidden
  layers (rather than *exactly* `k`): a network with `k'` hidden layers for any `k' ≤ k`
  witnesses membership. This is the standard reading in the neural-network-depth literature
  (adding hidden layers can only help, e.g. via layer padding), and it is also the reading
  under which the stated equality `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉+1}` is meaningful as a
  *sufficiency* statement for that specific depth (rather than requiring the depth to be
  simultaneously necessary at exactly that value for every single CPWL function).
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of affine
  functions `ℝ^n → ℝ` such that `f` locally agrees (in a neighbourhood of every point) with
  one of them. This is a genuine piecewise-linearity condition (not defined via ReLU
  networks, and not a max-of-affine normal form).
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded using the real logarithm `Real.logb 3` and
  `Nat.ceil` (`⌈·⌉₊`), matching the paper's real-valued ceiling of `log_3`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector in `ℝ^n`. -/
def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias vector. -/
structure AffineMap' (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  bias : Fin b → ℝ

/-- The function `ℝ^a → ℝ^b` computed by an affine transformation. -/
def AffineMap'.apply {a b : ℕ} (T : AffineMap' a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.bias

/-- A ReLU network with exactly `k` hidden layers, input dimension `a`, output dimension `c`,
given as a chain of `k + 1` affine transformations, each (except the last) followed by a
componentwise ReLU. This directly encodes the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper: the `last` constructor is the
final affine map `T^(k+1)` (no `k` hidden layers, i.e. depth 1), and `cons` prepends a new
affine map `T^(1)` together with the ReLU applied right after it, incrementing the hidden
layer count by one. -/
inductive NetLayers : ℕ → ℕ → ℕ → Type
  | last {a b : ℕ} (T : AffineMap' a b) : NetLayers 0 a b
  | cons {a b c : ℕ} {k : ℕ} (T : AffineMap' a b) (rest : NetLayers k b c) :
      NetLayers (k + 1) a c

/-- The function `ℝ^a → ℝ^c` computed by a ReLU network. -/
def NetLayers.eval {k a c : ℕ} (net : NetLayers k a c) (x : Fin a → ℝ) : Fin c → ℝ :=
  match net with
  | .last T => T.apply x
  | .cons T rest => rest.eval (reluVec (T.apply x))

/-- A function `ℝ^n → ℝ` is computed by a ReLU network with exactly `k` hidden layers. -/
def NetworkComputes (n k : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ net : NetLayers k n 1, ∀ x : Fin n → ℝ, f x = net.eval x 0

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers (see the module docstring for why "at most" is the right
reading here). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' : ℕ, k' ≤ k ∧ NetworkComputes n k' f }

/-- `f : ℝ^n → ℝ` is continuous and piecewise linear: it is continuous, and there is a
finite family of affine functions such that `f` locally agrees with one of them at every
point. -/
def IsCPWL (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  Continuous f ∧
    ∃ (m : ℕ) (g : Fin m → AffineMap' n 1),
      ∀ x : Fin n → ℝ, ∃ i : Fin m, ∀ᶠ y in nhds x, f y = (g i).apply y 0

/-- `CPWL n` is the space of continuous piecewise linear functions `ℝ^n → ℝ`. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) := { f | IsCPWL n f }

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from the paper, as a number of hidden layers. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent035


namespace Agent036

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):

  For n ≥ 3,  CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}.

## Modelling choices

* `ℝ^n` is encoded as `Fin n → ℝ`.
* An affine map `ℝ^a → ℝ^b` is a matrix `A : Matrix (Fin b) (Fin a) ℝ` together with a
  bias vector `c : Fin b → ℝ`, evaluated as `x ↦ A.mulVec x + c`.
* A ReLU network with `k` hidden layers computing `f : ℝ^n → ℝ` is defined recursively
  (`NetOutput`): with `0` hidden layers it is a single affine map `ℝ^n → ℝ`; with `k+1`
  hidden layers it is an affine map `ℝ^n → ℝ^m` followed by a componentwise ReLU, feeding
  into a function computed by a `k`-hidden-layer network on `ℝ^m`. This literally unwinds
  the alternating composition `T^(k+1) ∘ ReLU ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper.
* `ReLUn n k` is the set of functions representable with **at most** `k` hidden layers
  (i.e. `∃ j ≤ k`, exactly `j` hidden layers suffice). This is the reading that makes
  Theorem 2 true: since one can always pad a network with extra layers implementing the
  identity (e.g. `x ↦ relu(x) - relu(-x)`), the "exactly k" and "at most k" classes
  coincide for `k ≥ 1`, but "at most k" is the natural monotone notion intended by the
  inclusion `ReLU_{n,k} ⊆ ReLU_{n,k+1}` implicit in the paper's depth hierarchy.
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of affine
  functions `ℝ^n → ℝ` such that every point of `ℝ^n` has a neighbourhood on which `f`
  coincides with one member of the family. This is a genuine local piecewise-linearity
  condition (not "representable by a ReLU network", and not a max-of-affines normal
  form).
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded with the real logarithm `Real.logb 3`
  and `Nat.ceil`.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given by a matrix and a bias vector. -/
structure Affine (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation: `x ↦ A x + c`. -/
def Affine.eval {a b : ℕ} (T : Affine a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `NetOutput n k f` means `f : ℝ^n → ℝ` is computed by a ReLU network with exactly `k`
hidden layers, i.e. `f = T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` for some affine maps
`T^(1), …, T^(k+1)` of matching dimensions. Defined by recursion on `k`: with `0` hidden
layers the network is just a single affine map, and with `k+1` hidden layers we peel off
the first affine map `T^(1) : ℝ^n → ℝ^m`, apply ReLU, and feed the result into a
`k`-hidden-layer network on `ℝ^m`. -/
def NetOutput : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : Affine n 1, ∀ x, f x = T.eval x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : Affine n m) (g : (Fin m → ℝ) → ℝ),
        NetOutput m k g ∧ ∀ x, f x = g (reluVec (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
**at most** `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ j, j ≤ k ∧ NetOutput n j f}

/-- The space of continuous piecewise linear functions `ℝ^n → ℝ`: `f` is continuous, and
there is a finite family of affine functions such that every point has a neighbourhood on
which `f` agrees with one member of the family. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (g : Fin m → ((Fin n → ℝ) → ℝ)),
      (∀ i, ∃ T : Affine n 1, ∀ x, g i x = T.eval x 0) ∧
      ∀ x : Fin n → ℝ, ∃ i, ∃ U ∈ nhds x, ∀ y ∈ U, f y = g i y}

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from the paper, as a natural number. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent036


namespace Agent037

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

  "Better Neural Network Expressivity: Subdividing the Simplex"
  (Bakaev, Brunck, Hertrich, Stade, Yehudayoff)

  Theorem 2. For n ≥ 3, CPWL_n = ReLU_{n, ⌈log_3(n−1)⌉ + 1}.

## Modelling choices

* Vectors `ℝ^n` are encoded as `ℝn n := Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is encoded concretely by a matrix `A` and a
  translation vector `c`, evaluated as `x ↦ A * x + c` (via `Matrix.mulVec`).
* A ReLU network with `k` hidden layers computing `f : ℝn n → ℝ` is defined recursively
  (`computesReLU`): with `0` hidden layers it is a single affine transformation
  `ℝn n → ℝn 1`; with `k+1` hidden layers it is an affine transformation `ℝn n → ℝn m`
  (arbitrary hidden width `m`) followed by componentwise ReLU, whose output is then fed
  into a network with `k` hidden layers. This mirrors the definition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper, unfolded one layer at a time.
* `ReLUn n k` is taken to mean functions representable with **at most** `k` hidden
  layers (i.e. `∃ k' ≤ k, computesReLU k' n f`), not *exactly* `k`. This is the standard
  reading in this literature: extra hidden layers can always simulate fewer ones (e.g. by
  padding with an affine map into two nonnegative "positive/negative part" coordinates and
  subtracting after a ReLU, which realizes the identity), so `ReLU_{n,k}` is monotone in
  `k`, and this is the reading under which the stated equality with `CPWL_n` can hold
  (`CPWL_n` is by definition already closed under "using more layers than needed").
* `CPWL n` is defined mathematically as: continuous functions `f : ℝn n → ℝ` for which
  there is a finite cover of `ℝn n` by (closed) polyhedra, each given as a finite
  intersection of halfspaces, on each of which `f` agrees with some affine function. This
  is a genuine piecewise-linearity condition, independent of any network representation.
* The depth bound `⌈log_3(n−1)⌉ + 1` is encoded using the real logarithm `Real.logb 3`
  together with `Nat.ceil`.
-/

/-- `ℝ^n` encoded as functions `Fin n → ℝ`. -/
abbrev ℝn (n : ℕ) := Fin n → ℝ

/-- The ReLU activation function `max 0 ·` on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector. -/
def reluVec {n : ℕ} (x : ℝn n) : ℝn n := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix `A` and a
translation vector `c`, evaluated as `x ↦ A * x + c`. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : ℝn b

/-- Evaluation of an `AffineMap`. -/
def AffineMap.eval {a b : ℕ} (T : AffineMap a b) (x : ℝn a) : ℝn b :=
  T.A.mulVec x + T.c

/-- `computesReLU k n f` means: `f : ℝn n → ℝ` is computed by a ReLU network with input
dimension `n`, output dimension `1`, and exactly `k` hidden layers, i.e. by the alternating
composition of `k + 1` affine transformations and `k` componentwise applications of ReLU:
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`. -/
def computesReLU : (k : ℕ) → (n : ℕ) → (ℝn n → ℝ) → Prop
  | 0, n, f => ∃ T : AffineMap n 1, ∀ x, f x = T.eval x 0
  | (k + 1), n, f =>
      ∃ (m : ℕ) (T : AffineMap n m) (g : ℝn m → ℝ),
        computesReLU k m g ∧ ∀ x, f x = g (reluVec (T.eval x))

/-- `ReLUn n k`: the functions `ℝn n → ℝ` representable by a ReLU network with at most `k`
hidden layers (see the module docstring for why "at most" rather than "exactly" is the
right reading here). -/
def ReLUn (n k : ℕ) : Set (ℝn n → ℝ) :=
  {f | ∃ k' ≤ k, computesReLU k' n f}

/-- A function `ℝn n → ℝ` is affine if it has the form `x ↦ ⟨a, x⟩ + b`. -/
def IsAffineFn (n : ℕ) (g : ℝn n → ℝ) : Prop :=
  ∃ (a : ℝn n) (b : ℝ), ∀ x, g x = (∑ i, a i * x i) + b

/-- A (closed) polyhedron in `ℝn n`: a finite intersection of closed halfspaces
`{x | ⟨a, x⟩ ≤ b}`. -/
def IsPolyhedron (n : ℕ) (S : Set (ℝn n)) : Prop :=
  ∃ (m : ℕ) (a : Fin m → ℝn n) (b : Fin m → ℝ),
    S = {x | ∀ i, (∑ j, a i j * x j) ≤ b i}

/-- `CPWL n`: the continuous piecewise-linear functions `ℝn n → ℝ`, defined as those
continuous functions for which there is a finite cover of `ℝn n` by polyhedra, on each of
which `f` agrees with some affine function. This is a genuine polyhedral-subdivision
definition, not a "representable by ReLU network" or "max of affine functions" definition. -/
def CPWL (n : ℕ) : Set (ℝn n → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (P : Fin m → Set (ℝn n)) (g : Fin m → ℝn n → ℝ),
          (∀ i, IsPolyhedron n (P i)) ∧
          (∀ i, IsAffineFn n (g i)) ∧
          (∀ x : ℝn n, ∃ i, x ∈ P i) ∧
          (∀ i, ∀ x ∈ P i, f x = g i x) }

/-- The depth bound `⌈log_3(n − 1)⌉ + 1` from Theorem 2, using the real logarithm and
`Nat.ceil`. -/
def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n−1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent037


namespace Agent038

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

`CPWL n = ReLU_{n, ⌈log_3 (n-1)⌉ + 1}` for `n ≥ 3`.

## Modelling choices

* Vectors `ℝ^n` are modelled as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is modelled concretely as a bundled
  pair of a "weight function" `W : Fin b → Fin a → ℝ` and a bias
  `c : Fin b → ℝ`, applied as `x ↦ (fun i => ∑ j, W i j * x j + c i)`.
  This avoids pulling in `Matrix`/`Matrix.mulVec` machinery while being
  definitionally the same content.
* A ReLU network with `k` hidden layers computing `f : ℝ^n → ℝ` is defined
  *recursively* on `k`, directly mirroring the alternating composition
  `T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}` from the paper:
  - `k = 0`: `f` is computed by a single affine transformation `ℝ^n → ℝ^1`
    (no hidden layer, no ReLU applied at all — this is `T^{(1)}` alone).
  - `k + 1`: there is a hidden width `m`, an affine map `T : ℝ^n → ℝ^m`, and
    a function `g : ℝ^m → ℝ` computable with `k` hidden layers, such that
    `f = g ∘ ReLU ∘ T`.
  `ReLUn n k` is the set of functions computable with *exactly* `k` hidden
  layers in this recursive sense. (Note: because one can always simulate the
  identity on `ℝ` using two extra ReLU neurons via `x = ReLU x - ReLU (-x)`,
  the "exactly `k`" and "at most `k`" readings coincide for all `k ≥ 1`, so
  this choice is not actually a restriction; we simply find the "exactly
  `k`" recursive definition the most literal transcription of the paper's
  alternating-composition definition.)
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family
  of affine functionals `ℝ^n → ℝ` such that every point of `ℝ^n` has a
  neighborhood on which `f` coincides with one member of the family. This is
  a genuine local piecewise-linearity condition (a finite atlas of affine
  pieces), not a restatement of ReLU-representability and not the
  max-of-affine normal form.
* The depth bound is `⌈log_3 (n - 1)⌉ + 1`, encoded literally via
  `Real.logb 3` and `Nat.ceil` (`⌈·⌉₊`).
-/

/-- A componentwise ReLU. -/
def reluScalar (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `reluScalar` to a vector in `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ :=
  fun i => reluScalar (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a weight
function and a bias vector. -/
structure Affine (a b : ℕ) where
  /-- The "matrix" of coefficients: `W i j` is the coefficient of input
  coordinate `j` in output coordinate `i`. -/
  W : Fin b → Fin a → ℝ
  /-- The bias vector. -/
  c : Fin b → ℝ

/-- Evaluate an affine transformation at a point. -/
def Affine.apply {a b : ℕ} (T : Affine a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (Finset.univ.sum fun j => T.W i j * x j) + T.c i

/-- `ComputesHidden k n f` means `f : ℝ^n → ℝ` is computed by a ReLU network
with exactly `k` hidden layers, i.e. `f` arises as the alternating
composition `T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}` of `k + 1`
affine transformations with `k` interspersed componentwise ReLUs. -/
def ComputesHidden : ℕ → (n : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | 0, n, f => ∃ T : Affine n 1, f = fun x => T.apply x 0
  | (k + 1), n, f =>
      ∃ (m : ℕ) (T : Affine n m) (g : (Fin m → ℝ) → ℝ),
        ComputesHidden k m g ∧ f = fun x => g (reluVec (T.apply x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU
network with exactly `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ComputesHidden k n f}

/-- An affine functional `ℝ^n → ℝ`, as a `Prop` predicate: `a` is affine iff
it has the form `x ↦ ⟨c, x⟩ + b` for some coefficients `c` and constant `b`. -/
def IsAffineFunctional (n : ℕ) (a : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (coef : Fin n → ℝ) (b : ℝ), ∀ x, a x = (Finset.univ.sum fun i => coef i * x i) + b

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`:
those that are continuous and admit a *finite* family of affine functionals
such that every point has a neighborhood on which `f` agrees with one member
of the family. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
      ∃ (r : ℕ) (a : Fin r → (Fin n → ℝ) → ℝ),
        (∀ i, IsAffineFunctional n (a i)) ∧
        ∀ x : Fin n → ℝ, ∃ (i : Fin r) (ε : ℝ), ε > 0 ∧
          ∀ y : Fin n → ℝ, dist y x < ε → f y = a i y}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, encoded via the
real logarithm `Real.logb 3` and `Nat.ceil`. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3 (n - 1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent038


namespace Agent039

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

  "Better Neural Network Expressivity: Subdividing the Simplex"

Theorem 2 states: for `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`.

## Modelling choices (see final summary)

* Vectors `ℝ^n` are modelled as `Fin n → ℝ`.
* Affine maps `ℝ^a → ℝ^b` are modelled concretely by a matrix and a bias vector.
* A ReLU network with `k` hidden layers computing `f : ℝ^n → ℝ` is defined by
  structural recursion on `k`, mirroring the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper.
* `ReLUn n k` is taken to be the set of functions representable with **at most**
  `k` hidden layers (rather than *exactly* `k`). This is the reading under which
  the theorem is true and matches the informal usage "representable with `k`
  hidden layers" in the paper (any network can be padded to use more layers via
  an identity-simulating pair of ReLUs, so "exactly k" and "at most k" describe
  the same increasing filtration of `CPWL_n`; "at most k" is the more natural
  and directly usable definition).
* `CPWL n` is defined genuinely: continuity, together with the existence of a
  *finite* family of affine functions such that every point has a neighborhood
  on which `f` coincides with one member of the family. This is a real
  piecewise-linearity condition, not a "representable by a ReLU network" or
  max-of-affine restatement of the theorem.
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined using the real logarithm
  `Real.logb 3` together with `Nat.ceil`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector. -/
def reluVec {m : ℕ} (v : Fin m → ℝ) : Fin m → ℝ := fun i => relu (v i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix `A` and a
bias vector `c`, computing `x ↦ A * x + c`. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an `AffineMap`. -/
def AffineMap.eval {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `NetProp n k f` holds iff `f : ℝ^n → ℝ` is computed by a ReLU network with
exactly `k` hidden layers, i.e. `f` is the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations
`T^(1), …, T^(k+1)` (with `T^(k+1)` landing in `ℝ^1`), interspersed with `k`
applications of componentwise ReLU. Defined by recursion on `k`: the base case
`k = 0` is a single affine transformation `ℝ^n → ℝ^1`; the inductive step peels
off the first affine map `T^(1) : ℝ^n → ℝ^m` together with a ReLU application,
reducing to a network with `k` hidden layers on the remaining `k + 1` affine
maps. -/
def NetProp (n : ℕ) : ℕ → ((Fin n → ℝ) → ℝ) → Prop
  | 0, f => ∃ w : AffineMap n 1, ∀ x, f x = w.eval x 0
  | (k + 1), f =>
      ∃ (m : ℕ) (T : AffineMap n m) (g : (Fin m → ℝ) → ℝ),
        NetProp m k g ∧ ∀ x, f x = g (reluVec (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU
network with **at most** `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ j ≤ k, NetProp n j f}

/-- `CPWL n` is the set of continuous, genuinely piecewise-linear functions
`ℝ^n → ℝ`: `f` is continuous, and there is a finite family of affine functions
(given by weight vectors `w i` and intercepts `b i`, indexed by a finite type
`ι`) such that every point `x` has a neighborhood on which `f` agrees with one
member `i` of the family. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → Fin n → ℝ) (b : ι → ℝ),
      ∀ x : Fin n → ℝ, ∃ i : ι, ∃ U : Set (Fin n → ℝ), IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, f y = (∑ j, w i j * y j) + b i}

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from the theorem statement, using the
real logarithm `Real.logb 3` and `Nat.ceil`. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent039


namespace Agent040

open scoped BigOperators

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m` (encoded as `Fin m → ℝ`). -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias
vector: `x ↦ A * x + c`. -/
structure Affine (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- The function `ℝ^a → ℝ^b` computed by an affine transformation. -/
def Affine.eval {a b : ℕ} (T : Affine a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, T.A i j * x j) + T.c i

/-- `NetworkComputes k n f` holds iff `f : ℝ^n → ℝ` is computed by a ReLU network with
exactly `k` hidden layers, i.e. by the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations, with
componentwise ReLU applied after each of the first `k` of them (matching the definition
in the paper's Introduction).

The recursion peels off the first affine map `T^(1) : ℝ^n → ℝ^m` (where `m` is the
width `n_1` of the first hidden layer) together with the ReLU applied to its output,
leaving a network with `k` hidden layers and input dimension `m` computing the rest.
The base case `k = 0` is a single affine map `ℝ^n → ℝ` (no hidden layers, no ReLU). -/
def NetworkComputes : ℕ → (n : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | 0, n, f => ∃ T : Affine n 1, ∀ x, f x = T.eval x 0
  | k + 1, n, f =>
      ∃ (m : ℕ) (T : Affine n m) (g : (Fin m → ℝ) → ℝ),
        NetworkComputes k m g ∧ ∀ x, f x = g (reluVec (T.eval x))

/-- `ReLUn n k`: the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*exactly* `k` hidden layers (the literal reading of "the subset of `CPWL_n`
representable with `k` hidden layers" from the paper). Note that an extra hidden layer
can always simulate the identity on each coordinate, since
`x = ReLU x - ReLU (-x)`; consequently `NetworkComputes k n f` implies
`NetworkComputes (k+1) n f`, so this "exactly `k`" reading is monotone in `k` and
coincides with an "at most `k`" reading — either is consistent with Theorem 2 as an
equality of sets for the specific bound below. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | NetworkComputes k n f }

/-- `CPWL n`: the continuous, piecewise-linear functions `ℝ^n → ℝ`. A function is CPWL
if it is continuous and there is a *finite* family `S` of affine functions such that
every point of `ℝ^n` has a neighborhood on which `f` agrees with (at least) one member
of `S`. This is a genuine piecewise-linearity condition: it is not automatically
satisfied by every continuous function, and it does not presuppose representability by
a ReLU network or a max-of-affine normal form. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
      ∃ S : Finset (Affine n 1), ∀ x : Fin n → ℝ,
        ∃ T ∈ S, ∀ᶠ y in nhds x, f y = T.eval y 0 }

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so `n - 1 ≥ 2`
and the real logarithm base `3` is well-defined and positive on it). -/
def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 : ∀ n : ℕ, n ≥ 3 → CPWL n = ReLUn n (depthBound n) := sorry

end Agent040


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


namespace Agent042

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We model vectors `ℝ^n` as `Fin n → ℝ`.

* An **affine layer** `ℝ^a → ℝ^b` is given concretely by a matrix `A : Matrix (Fin b) (Fin a) ℝ`
  and a vector `c : Fin b → ℝ`, computing `x ↦ A.mulVec x + c`.
* A **ReLU network with `k` hidden layers** is a list of `k + 1` affine layers of matching
  dimensions (input dimension `n`, output dimension `1`), computed by applying `ReLU`
  componentwise after every layer *except* the last one (matching the alternating
  composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper).
* `ReLUn n k` is the set of functions `ℝ^n → ℝ` computed by *some* network with **exactly**
  `k` hidden layers (the literal reading of "representable with `k` hidden layers"). Note
  that padding a network with extra "identity" hidden layers (via
  `ReLU(x) - ReLU(-x) = x`, doubling the width) shows `ReLUn n k ⊆ ReLUn n (k+1)`, so this
  choice agrees with the "at most `k`" reading for the purposes of Theorem 2.
* `CPWL n` is defined directly and honestly: continuous functions that are affine on each
  piece of a *finite* subdivision of `ℝ^n` into (closed, convex) polyhedra, each polyhedron
  itself cut out by finitely many affine inequalities. This is independent of the ReLU
  network model and does not assume a max-of-affine normal form.
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined via `Real.logb 3` and `Nat.ceil`.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^inDim → ℝ^outDim`, given concretely by a matrix and a
translation vector: `x ↦ A * x + c`. -/
structure AffineLayer where
  inDim  : ℕ
  outDim : ℕ
  A : Matrix (Fin outDim) (Fin inDim) ℝ
  c : Fin outDim → ℝ

/-- Evaluate an affine layer on a dimension-tagged vector, provided the dimensions match;
otherwise the input is returned unchanged (this branch never occurs for well-formed
networks, see `NetworkComputes`). -/
def AffineLayer.evalSig (T : AffineLayer) (v : Σ m : ℕ, Fin m → ℝ) : Σ m : ℕ, Fin m → ℝ :=
  if h : v.1 = T.inDim then
    ⟨T.outDim, T.A.mulVec (v.2 ∘ Fin.cast h.symm) + T.c⟩
  else
    v

/-- Componentwise `relu` on a dimension-tagged vector. -/
def reluVecSig (v : Σ m : ℕ, Fin m → ℝ) : Σ m : ℕ, Fin m → ℝ := ⟨v.1, reluVec v.2⟩

/-- The forward pass of a ReLU network given as a list of affine layers: apply each layer,
inserting a componentwise `ReLU` between consecutive layers but *not* after the final layer
(matching `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`). -/
def runLayers : List AffineLayer → (Σ m : ℕ, Fin m → ℝ) → (Σ m : ℕ, Fin m → ℝ)
  | [], v => v
  | [T], v => T.evalSig v
  | T :: rest, v => runLayers rest (reluVecSig (T.evalSig v))

/-- `NetworkComputes n layers f` means: `layers` is a well-formed ReLU network with input
dimension `n` and output dimension `1` (consecutive layers have matching dimensions), and
its forward pass computes `f`. -/
def NetworkComputes (n : ℕ) (layers : List AffineLayer) (f : (Fin n → ℝ) → ℝ) : Prop :=
  (layers.head?.map (·.inDim) = some n) ∧
  (layers.getLast?.map (·.outDim) = some 1) ∧
  (List.Chain' (fun T1 T2 => T1.outDim = T2.inDim) layers) ∧
  (∀ x : Fin n → ℝ, ∃ y : Fin 1 → ℝ, runLayers layers ⟨n, x⟩ = ⟨1, y⟩ ∧ f x = y 0)

/-- The set of functions `ℝ^n → ℝ` representable by a ReLU network with **exactly** `k`
hidden layers, i.e. `k + 1` affine transformations. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ layers : List AffineLayer, layers.length = k + 1 ∧ NetworkComputes n layers f}

/-- A polyhedron in `ℝ^n`: the solution set of a finite system of affine inequalities
`⟨a_j, x⟩ ≤ b_j`. -/
def IsPolyhedron {n : ℕ} (P : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (a : Fin m → (Fin n → ℝ)) (b : Fin m → ℝ),
    P = {x : Fin n → ℝ | ∀ j : Fin m, (∑ i, a j i * x i) ≤ b j}

/-- `CPWL n`: continuous functions `ℝ^n → ℝ` that admit a finite subdivision of `ℝ^n` into
polyhedral pieces, on each of which the function agrees with some affine function. This is
a genuine piecewise-linearity condition, independent of the ReLU network model. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
       ∃ (m : ℕ) (P : Fin m → Set (Fin n → ℝ)) (A : Fin m → (Fin n → ℝ)) (c : Fin m → ℝ),
         (∀ i, IsPolyhedron (P i)) ∧
         (⋃ i, P i) = Set.univ ∧
         (∀ i, ∀ x ∈ P i, f x = (∑ k, A i k * x k) + c i)}

noncomputable section

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from Theorem 2, as the number of hidden layers. -/
def depthBound (n : ℕ) : ℕ := ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

end

/-- **Theorem 2.** For `n ≥ 3`, the class of continuous piecewise-linear functions on `ℝ^n`
coincides with the class of functions representable by a ReLU network with
`⌈log_3(n - 1)⌉ + 1` hidden layers. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent042


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
def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent043


namespace Agent044

/-!
# Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity: Subdividing the Simplex")

For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`.

## Modelling choices

* `ℝ^n` is encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is encoded concretely as a matrix `A` together with a
  bias vector `c`, evaluated as `x ↦ A.mulVec x + c`.
* A ReLU network with exactly `k` hidden layers computing `f : ℝ^n → ℝ` is defined by recursion
  on `k`: with `0` hidden layers, `f` is exactly one affine map `ℝ^n → ℝ^1`; with `k+1` hidden
  layers, `f` factors as `g ∘ ReLU ∘ T` where `T : ℝ^n → ℝ^m` is affine (`m > 0` neurons in the
  first hidden layer) and `g : ℝ^m → ℝ` is computed by a network with `k` hidden layers. This
  directly mirrors the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper, peeling off `T^(1)` at each step.
* `ReLUn n k` is taken to be the functions representable with **at most** `k` hidden layers
  (i.e. `∃ k' ≤ k`), not *exactly* `k`. This is the standard reading and the one that makes
  Theorem 2 true: e.g. every affine function lies in `ReLUn n k` for every `k`, not just `k = 0`.
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of affine functions
  such that around every point `x` there is a neighbourhood on which `f` agrees with one member
  of the family. This is a genuine local-affine-pieces condition, independent of ReLU networks.
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded using the real logarithm `Real.logb 3` and
  `Nat.ceil`, applied to the real number `(n : ℝ) - 1`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise (vectorized) application of `relu`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias vector. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an `AffineMap` as `x ↦ A * x + c`. -/
def AffineMap.eval {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `NetComputes n k f` means `f : ℝ^n → ℝ` is computed by a ReLU network with **exactly** `k`
hidden layers, i.e. `f` is the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations, defined by
recursion on `k` (peeling off the innermost affine map `T^(1)` and the hidden layer it feeds). -/
def NetComputes : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : AffineMap n 1, ∀ x, f x = T.eval x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (_ : 0 < m) (T : AffineMap n m) (g : (Fin m → ℝ) → ℝ),
        NetComputes m k g ∧ ∀ x, f x = g (reluVec (T.eval x))

/-- `ReLUn n k`, the set of functions `ℝ^n → ℝ` representable by a ReLU network with **at most**
`k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, NetComputes n k' f }

/-- `CPWL n`, the set of continuous piecewise-linear functions `ℝ^n → ℝ`: `f` is continuous, and
there is a finite family of affine functions (linear part `A i`, bias `b i`) such that every
point of `ℝ^n` has a neighbourhood on which `f` coincides with one member of the family. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (N : ℕ) (A : Fin N → (Fin n → ℝ)) (b : Fin N → ℝ),
          ∀ x : Fin n → ℝ, ∃ i : Fin N, ∀ᶠ y in nhds x, f y = (∑ j, A i j * y j) + b i }

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from Theorem 2, for `n ≥ 3`. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent044


namespace Agent045

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):  for `n ≥ 3`, `CPWL n = ReLUn n (⌈log_3 (n-1)⌉ + 1)`.

Modelling choices:
* `ℝ^n` is encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is encoded concretely as a matrix `A` together
  with a bias vector `c`, via `x ↦ A * x + c`.
* A ReLU network with `k` hidden layers computing `f : ℝ^n → ℝ` is encoded by the
  recursive predicate `ComputesWithHidden`, which literally unwinds the alternating
  composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper: peel off the
  first affine map, apply ReLU componentwise, and recurse with one fewer hidden layer.
* `ReLUn n k` is taken to be the functions representable with *at most* `k` hidden
  layers (not exactly `k`). This is the standard convention in this literature (depth
  can always be padded, e.g. via `x = ReLU x - ReLU (-x)`, so the classes are monotone
  in `k`), and it is the reading under which the stated equality `CPWL n = ReLUn n (…)`
  is the correct/true statement of Theorem 2.
* `CPWL n` is defined directly as: `f` is continuous, and there is a *finite* family of
  affine functions such that `f` agrees with (at least) one member of the family in a
  neighbourhood of every point. This is a genuine local/piecewise-affine condition; it
  is not defined via ReLU-network representability and is not a global max-of-affine
  normal form.
* The depth bound `⌈log_3 (n-1)⌉ + 1` is encoded using the real logarithm
  `Real.logb 3` together with `Nat.ceil`, matching the paper's real-valued `log_3`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector in `ℝ^m` (encoded as `Fin m → ℝ`). -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix `A` and a bias
vector `c`, so that it computes `x ↦ A * x + c`. -/
structure AffineTransform (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- The function `ℝ^a → ℝ^b` computed by an affine transformation. -/
def AffineTransform.eval {a b : ℕ} (T : AffineTransform a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, T.A i j * x j) + T.c i

/-- `ComputesWithHidden k n f` means `f : ℝ^n → ℝ` is computed by a ReLU network with
exactly `k` hidden layers, i.e. by the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations
`T^(1), …, T^(k+1)`, with `ReLU` applied componentwise between consecutive affine maps.
The base case `k = 0` is a single affine transformation `ℝ^n → ℝ^1` (no hidden layers,
depth `1`), and the recursive case peels off the first affine map and the ReLU applied
to its output, then recurses on the remaining `k` hidden layers with the new input
dimension `m`. -/
def ComputesWithHidden : (k : ℕ) → (n : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | 0, n, f => ∃ T : AffineTransform n 1, ∀ x, f x = T.eval x 0
  | (k + 1), n, f =>
      ∃ (m : ℕ) (T : AffineTransform n m) (g : (Fin m → ℝ) → ℝ),
        ComputesWithHidden k m g ∧ ∀ x, f x = g (reluVec (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers. (Depth can always be padded without changing the
represented function, e.g. via the identity `x = ReLU x - ReLU (-x)`, so this "at most"
reading is the one under which the classes `ReLUn n k` increase with `k` and Theorem 2's
equality with `CPWL n` is the intended, true statement.) -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, ComputesWithHidden k' n f}

/-- An affine function `ℝ^n → ℝ`, i.e. `x ↦ ⟨a, x⟩ + b` for some vector `a` and scalar `b`. -/
def IsAffineFun (n : ℕ) (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x, g x = (∑ i, a i * x i) + b

/-- `CPWL n` is the set of continuous, piecewise linear functions `ℝ^n → ℝ`: those `f`
that are continuous, and are locally equal, near every point, to one member of some
fixed *finite* family of affine functions. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
        ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ),
          (∀ i, IsAffineFun n (g i)) ∧
          ∀ x : Fin n → ℝ, ∃ i : Fin m, Filter.Eventually (fun y => f y = g i y) (nhds x)}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, using the real logarithm to
base `3` and `Nat.ceil`. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3 (n-1)⌉ + 1}`. -/
theorem theorem2 : ∀ n : ℕ, n ≥ 3 → CPWL n = ReLUn n (depthBound n) := sorry

end Agent045


namespace Agent046

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

  "For n ≥ 3, we have CPWL_n = ReLU_{n, ⌈log_3(n−1)⌉ + 1}."

## Modelling choices

* Vectors `ℝ^m` are encoded as `Fin m → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is encoded concretely as a matrix `A : Matrix
  (Fin b) (Fin a) ℝ` together with a bias vector, applied as `x ↦ A x + bias`.
* A ReLU network with `k` hidden layers computing `f : ℝ^n → ℝ` is defined by
  *structural recursion on `k`*: with `0` hidden layers, `f` is exactly one affine map
  `ℝ^n → ℝ`; with `k+1` hidden layers, `f` factors as `g ∘ ReLU ∘ T` where `T : ℝ^n → ℝ^m`
  is affine and `g` is computable with `k` hidden layers on `ℝ^m`. This directly encodes
  the alternating composition `T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}` from the
  paper.
* `ReLUn n k` is taken to be functions representable with **at most** `k` hidden layers
  (i.e. the union over `k' ≤ k` of the exactly-`k'` classes). This is the standard reading
  in the depth-separation literature and is the one that makes Theorem 2 meaningful: the
  classes `ReLUn n k` must be monotone increasing in `k` for "the smallest `k` for which
  `ReLUn n k` already covers all of `CPWL n`" to make sense as an equality statement.
* `CPWL n` is defined mathematically (not via ReLU networks!) as: continuous functions
  `f : ℝ^n → ℝ` admitting a *finite* subdivision of `ℝ^n` into polyhedral pieces (each a
  finite intersection of halfspaces) covering `ℝ^n`, on each of which `f` agrees with some
  affine function from a finite list.
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded literally using `Real.logb 3` and
  `Nat.ceil` (`⌈·⌉₊`), applied to the real number `(n - 1 : ℝ)` (ordinary real subtraction
  of the cast of `n`, not truncated natural subtraction).
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of ReLU to a vector. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias
vector: `x ↦ A x + bias`. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  bias : Fin b → ℝ

/-- Evaluating an `AffineMap` at a point. -/
def AffineMap.apply {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, T.A i j * x j) + T.bias i

/-- `NetComputes n k f` means `f : ℝ^n → ℝ` is computed by some ReLU network with exactly
`k` hidden layers, i.e. `f` is the alternating composition
`T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}` of `k + 1` affine transformations with
componentwise ReLU applications between consecutive ones. Defined by recursion on `k`:
with `0` hidden layers a single affine map `ℝ^n → ℝ` is applied; with `k + 1` hidden
layers, an affine map `T : ℝ^n → ℝ^m` is applied, then `ReLU`, and the remaining `k`
hidden layers compute `g` on `ℝ^m`, with `f = g ∘ ReLU ∘ T`. -/
def NetComputes : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : AffineMap n 1, f = fun x => T.apply x 0
  | n, k + 1, f =>
      ∃ (m : ℕ) (T : AffineMap n m) (g : (Fin m → ℝ) → ℝ),
        NetComputes m k g ∧ f = fun x => g (reluVec (T.apply x))

/-- `ReLUn n k`, the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, NetComputes n k' f }

/-- A function `ℝ^n → ℝ` is affine if it has the form `x ↦ c ⬝ x + d` for some vector `c`
and constant `d`. -/
def IsAffineFun (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (c : Fin n → ℝ) (d : ℝ), ∀ x, f x = (∑ i, c i * x i) + d

/-- A subset of `ℝ^n` is a (closed) polyhedron if it is a finite intersection of
halfspaces `{x | a ⬝ x ≤ b}`. -/
def IsPolyhedron (n : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (a : Fin m → Fin n → ℝ) (b : Fin m → ℝ),
    S = ⋂ i, {x : Fin n → ℝ | (∑ j, a i j * x j) ≤ b i}

/-- `CPWL n`, the set of continuous piecewise-linear functions `ℝ^n → ℝ`: continuous
functions for which there is a finite polyhedral subdivision of `ℝ^n` (finitely many
polyhedral pieces covering `ℝ^n`) together with a finite list of affine functions, such
that `f` agrees with one of these affine functions on each piece. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
      ∃ (m : ℕ) (g : Fin m → ((Fin n → ℝ) → ℝ)) (P : Fin m → Set (Fin n → ℝ)),
        (∀ i, IsAffineFun n (g i)) ∧
        (∀ i, IsPolyhedron n (P i)) ∧
        (⋃ i, P i) = Set.univ ∧
        ∀ i, ∀ x ∈ P i, f x = g i x }

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so `n - 1 ≥ 2`,
using real subtraction of the cast of `n`). -/
def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n−1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent046


namespace Agent047

/-! ### Basic building blocks: ReLU, affine maps -/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b` given concretely by a matrix `A` and a bias
vector `c`, applied as `x ↦ A * x + c`. -/
def affineApply {a b : ℕ} (A : Matrix (Fin b) (Fin a) ℝ) (c : Fin b → ℝ)
    (x : Fin a → ℝ) : Fin b → ℝ :=
  A.mulVec x + c

/-! ### ReLU networks -/

/-- `NetComputes n m k f` says that `f : ℝ^n → ℝ^m` is computed by a ReLU network with
`k` hidden layers, i.e. by an alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ... ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations
`T^(1), ..., T^(k+1)` with componentwise ReLU applied after each of the first `k` of them.
We build this up recursively from the *output* side: a `0`-hidden-layer network is a
single affine map (depth `1`), and a `(k+1)`-hidden-layer network is a `k`-hidden-layer
network `g : ℝ^n → ℝ^p` followed by a ReLU and one more affine map `ℝ^p → ℝ^m`. -/
def NetComputes : (n m k : ℕ) → ((Fin n → ℝ) → (Fin m → ℝ)) → Prop
  | n, m, 0, f =>
      ∃ (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ), ∀ x, f x = affineApply A c x
  | n, m, (k + 1), f =>
      ∃ (p : ℕ) (g : (Fin n → ℝ) → (Fin p → ℝ)) (A : Matrix (Fin m) (Fin p) ℝ)
        (c : Fin m → ℝ),
        NetComputes n p k g ∧ ∀ x, f x = affineApply A c (reluVec (g x))

/-- A scalar function `f : ℝ^n → ℝ` is computed by a ReLU network with `k` hidden layers
if it is (identifying `ℝ` with `ℝ^1`) the output of a `NetComputes` network
`ℝ^n → ℝ^1`. -/
def ReluComputable (n k : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  NetComputes n 1 k (fun x (_ : Fin 1) => f x)

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers. We use "at most" rather than "exactly": a network can always
be padded with extra layers that compute the identity via ReLU (`x = ReLU x - ReLU (-x)`),
so the classes of functions representable with `k` and with `k + 1` hidden layers are
naturally increasing in `k`. Reading `ReLU_{n,k}` as "at most `k` hidden layers" is what
makes the single equality `CPWL_n = ReLU_{n,k}` (for one specific `k`) the right statement
of Theorem 2, without silently relying on a separate monotonicity/padding lemma. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, ReluComputable n k' f }

/-! ### CPWL functions -/

/-- An affine function `ℝ^n → ℝ`, given by a linear part `a` and a constant `b`. -/
def IsAffineFun (n : ℕ) (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x : Fin n → ℝ, g x = (Finset.univ.sum fun i => a i * x i) + b

/-- The space of continuous, piecewise-linear functions `ℝ^n → ℝ`: continuous functions
that, at every point of `ℝ^n`, locally agree with one of finitely many affine functions.
This is a genuine piecewise-linearity condition (not "representable by some ReLU
network" and not a max-of-affine normal form), matching the informal definition of CPWL
in the paper. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ), (∀ i, IsAffineFun n (g i)) ∧
          ∀ x : Fin n → ℝ, ∃ i, ∀ᶠ y in nhds x, f y = g i y }

/-! ### The depth bound `⌈log_3 (n - 1)⌉ + 1` -/

/-- The number of hidden layers `⌈log_3 (n - 1)⌉ + 1` from the statement of Theorem 2,
using the real logarithm `Real.logb 3` and `Nat.ceil`. For `n ≥ 3` we have `n - 1 ≥ 2`,
so the argument of the logarithm is positive. -/
def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-! ### Theorem 2 -/

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉+1}`: the continuous
piecewise-linear functions on `ℝ^n` are exactly those representable by a ReLU network
with at most `⌈log_3(n-1)⌉ + 1` hidden layers. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent047


namespace Agent048

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We model `ℝ^n` as `Fin n → ℝ`. An affine transformation `ℝ^a → ℝ^b` is given
concretely by a matrix and a bias vector, `x ↦ A * x + c`. A ReLU network with
`k` hidden layers computing `f : ℝ^n → ℝ` is modelled by the recursive relation
`Computes k n f`, built by peeling off the first affine map and the ReLU that
follows it. `ReLUn n k` is the set of functions computable with *at most* `k`
hidden layers (the standard convention for these depth-separation results,
matching monotonicity `ReLUn n k ⊆ ReLUn n (k+1)`). `CPWL n` is defined as:
continuous, and locally (in a neighbourhood of every point) equal to one of
finitely many affine functions -- a genuine piecewise-linear condition, not
phrased via ReLU networks or via a max-of-affine normal form.
-/

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a
bias vector: `x ↦ A * x + c`. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluate an affine transformation at a point. -/
noncomputable def AffineMap.eval {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) :
    Fin b → ℝ :=
  fun i => (∑ j, T.A i j * x j) + T.c i

/-- The ReLU function `max 0 ·` on `ℝ`, applied componentwise to a vector. -/
noncomputable def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => max 0 (x i)

/-- `Computes k n f` means `f : ℝ^n → ℝ` is computed by a ReLU network with
exactly `k` hidden layers, i.e. by an alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations
with componentwise ReLU applications in between. The base case `k = 0` is a
single affine map with no ReLU (depth `1`, `0` hidden layers); the recursive
case peels off the first affine map `T^(1) : ℝ^n → ℝ^m` and the following
ReLU, leaving a network with `k` hidden layers computing `g : ℝ^m → ℝ`. -/
def Computes : (k : ℕ) → (n : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | 0, n, f => ∃ T : AffineMap n 1, ∀ x, f x = T.eval x 0
  | (k + 1), n, f =>
      ∃ (m : ℕ) (T : AffineMap n m) (g : (Fin m → ℝ) → ℝ),
        Computes k m g ∧ ∀ x, f x = g (reluVec (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU
network with *at most* `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, Computes k' n f }

/-- A function `ℝ^n → ℝ` is affine if it has the form `x ↦ a ⬝ x + b`. -/
def IsAffineFun {n : ℕ} (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x, g x = (∑ i, a i * x i) + b

/-- `CPWL n` is the space of continuous, piecewise linear functions
`ℝ^n → ℝ`: `f` is continuous, and there is a finite family of affine
functions `g 1, ..., g m` such that every point `x` has a neighbourhood on
which `f` coincides with (at least) one of the `g i`. This is a genuine
polyhedral-subdivision-style piecewise-linearity condition, independent of
any ReLU-network representation and independent of any max-of-affine normal
form. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ),
          (∀ i, IsAffineFun (g i)) ∧
          ∀ x : Fin n → ℝ, ∃ i, ∀ᶠ y in nhds x, f y = g i y }

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, for `n ≥ 3`
(so `n - 1 ≥ 2 > 0`, and the real logarithm base `3` is well-defined and
positive here). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent048


namespace Agent049

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We model `ℝ^n` concretely as `Fin n → ℝ`.

## Modelling choices (see summary at the end of the task)

* `relu` is `max 0 ·` on `ℝ`, and `reluVec` applies it componentwise.
* An affine map `ℝ^n → ℝ^m` is given concretely by a matrix `A : Matrix (Fin m) (Fin n) ℝ`
  and a bias vector `c : Fin m → ℝ`, evaluated as `x ↦ A.mulVec x + c`.
* A ReLU network with exactly `k` hidden layers computing `f : ℝ^n → ℝ` is defined
  *recursively* on `k`: with `0` hidden layers `f` must itself be affine (a single affine
  transformation, no ReLU applied at all); with `k+1` hidden layers, `f` factors as
  `g ∘ (reluVec ∘ (affine map ℝ^n → ℝ^m))` for some hidden width `m` and some function `g`
  computable with `k` hidden layers on input dimension `m`.
* `ReLUn n k` is taken to be the functions representable with **at most** `k` hidden
  layers (not *exactly* `k`). This is the reading under which Theorem 2, stated as a set
  *equality* `CPWL n = ReLUn n (depthBound n)`, can be true: `ReLUn n k` is monotone
  increasing in `k` (more layers can only help), and `CPWL n` is the union over all `k` of
  the exactly-`k` classes, so the "at most" reading is needed for the depth bound `K` to
  give a class that is closed under adding further (necessarily useless, since `CPWL n`
  is already everything representable) hidden layers.
* The depth bound `⌈log_3 (n-1)⌉ + 1` is defined literally via `Real.logb 3` and
  `Nat.ceil`, applied to the real number `(n - 1 : ℝ)`.
* `CPWL n` is defined as: continuous functions `f : ℝ^n → ℝ` admitting a *finite*
  polyhedral subdivision of `ℝ^n` (each piece a finite intersection of affine
  halfspaces, i.e. `{x | ∀ i, A.mulVec x i ≤ b i}`) covering all of `ℝ^n`, on each piece
  of which `f` agrees with *some* affine function. This is a genuine
  piecewise-affine-subdivision definition, not a "representable by a ReLU network" or
  "max of affine functions" definition.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (v : Fin m → ℝ) : Fin m → ℝ := fun i => relu (v i)

/-- A function `ℝ^n → ℝ` is affine if it is of the form `x ↦ ⟨a, x⟩ + b`. -/
def IsAffine (n : ℕ) (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), g = fun x => (∑ i, a i * x i) + b

/-- A subset of `ℝ^n` is a (closed) polyhedron if it is a finite intersection of affine
halfspaces `{x | A.mulVec x i ≤ b i}`. -/
def IsPolyhedron (n : ℕ) (P : Set (Fin n → ℝ)) : Prop :=
  ∃ (r : ℕ) (A : Matrix (Fin r) (Fin n) ℝ) (b : Fin r → ℝ),
    P = {x | ∀ i, A.mulVec x i ≤ b i}

/-- The space of continuous piecewise linear (CPWL) functions `ℝ^n → ℝ`: continuous
functions that admit a finite polyhedral subdivision of `ℝ^n` on each piece of which the
function agrees with some affine function. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (r : ℕ) (P : Fin r → Set (Fin n → ℝ)),
      (∀ i, IsPolyhedron n (P i)) ∧
      (⋃ i, P i) = Set.univ ∧
      ∀ i, ∃ g, IsAffine n g ∧ Set.EqOn f g (P i)}

/-- `ComputesK n k f` holds iff `f : ℝ^n → ℝ` is computed by some ReLU network with
*exactly* `k` hidden layers: `k = 0` means `f` is a single affine transformation
(depth 1, no ReLU applied); `k+1` means `f` is obtained by first applying an affine
transformation `ℝ^n → ℝ^m` followed by (componentwise) ReLU, then feeding the result into
a network with `k` hidden layers. -/
def ComputesK : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ (a : Fin n → ℝ) (b : ℝ), f = fun x => (∑ i, a i * x i) + b
  | n, k + 1, f =>
      ∃ (m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ) (g : (Fin m → ℝ) → ℝ),
        ComputesK m k g ∧ f = g ∘ (fun x => reluVec (A.mulVec x + c))

/-- `ReLUn n k`: the functions `ℝ^n → ℝ` representable by a ReLU network with *at most*
`k` hidden layers (see the module docstring for why "at most" rather than "exactly"). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ j ≤ k, ComputesK n j f}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so `n - 1 ≥ 2`). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL n = ReLUn n (⌈log_3 (n-1)⌉ + 1)`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent049


namespace Agent050

/-!
Formalization of Theorem 2 of arXiv:2505.14338
("Better Neural Network Expressivity: Subdividing the Simplex").

Vector encoding: `ℝ^n` is modelled as `Fin n → ℝ`.

`ReLUn n k` is taken to mean "representable by a ReLU network with **at most** `k`
hidden layers" (the standard reading in this literature: adding useless extra
layers, e.g. via an identity affine map, never hurts, so the classes are
monotone increasing in `k`; this is also the reading under which Theorem 1's
consequence "every CPWL function on `R^n` can be represented with
`⌈log_3(n-1)⌉ + 1` hidden layers" and Theorem 2's equality both make sense).
-/

/-- ReLU on the reals. -/
noncomputable def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
noncomputable def reluVec {m : ℕ} (v : Fin m → ℝ) : Fin m → ℝ :=
  fun i => relu (v i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias
vector: `x ↦ A x + c`. -/
structure AffMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- The function `ℝ^a → ℝ^b` computed by an affine transformation. -/
noncomputable def AffMap.eval {a b : ℕ} (T : AffMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, T.A i j * x j) + T.c i

/-- A ReLU network with input dimension `n` and `k` hidden layers, encoded
recursively: a network with `0` hidden layers is a single affine output map
`ℝ^n → ℝ`; a network with `k+1` hidden layers is an affine map `ℝ^n → ℝ^m`
followed by componentwise ReLU, followed by a network with `k` hidden layers
on `ℝ^m`. This directly mirrors the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ... ∘ ReLU ∘ T^(1)` from the paper. -/
inductive ReLUNet : ℕ → ℕ → Type
  | last {n : ℕ} (T : AffMap n 1) : ReLUNet n 0
  | cons {n m k : ℕ} (T : AffMap n m) (rest : ReLUNet m k) : ReLUNet n (k + 1)

/-- The function `ℝ^n → ℝ` computed by a ReLU network. -/
noncomputable def ReLUNet.eval : {n k : ℕ} → ReLUNet n k → (Fin n → ℝ) → ℝ
  | _, _, ReLUNet.last T, x => T.eval x 0
  | _, _, ReLUNet.cons T rest, x => rest.eval (reluVec (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU
network with **at most** `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, ∃ net : ReLUNet n k', f = net.eval }

/-- A function `ℝ^n → ℝ` is affine iff it has the form `x ↦ a · x + c`. -/
def IsAffineFun {n : ℕ} (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (c : ℝ), ∀ x, g x = (∑ j, a j * x j) + c

/-- A set `P ⊆ ℝ^n` is a (closed) polyhedron iff it is a finite intersection of
closed affine half-spaces `{x | a · x ≤ b}`. -/
def IsPolyhedron {n : ℕ} (P : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ),
    P = { x | ∀ i, (∑ j, A i j * x j) ≤ b i }

/-- `CPWL n`: the continuous piecewise-linear functions `ℝ^n → ℝ`.
A function `f` is CPWL iff it is continuous and there is a *finite* polyhedral
subdivision of `ℝ^n` (finitely many polyhedral pieces covering `ℝ^n`) on each
piece of which `f` coincides with some affine function. This is a genuine
piecewise-linearity condition: it is neither "representable by some ReLU
network" nor a max-of-affine normal form. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (P : Fin m → Set (Fin n → ℝ)) (g : Fin m → (Fin n → ℝ) → ℝ),
          (∀ i, IsPolyhedron (P i)) ∧
          (∀ i, IsAffineFun (g i)) ∧
          (⋃ i, P i) = Set.univ ∧
          (∀ i, ∀ x ∈ P i, f x = g i x) }

/-- The depth bound `⌈log_3(n-1)⌉ + 1` hidden layers from Theorem 2, using the
real logarithm base 3 and the natural-number ceiling. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, the CPWL functions on `ℝ^n` coincide exactly
with the functions representable by ReLU networks with (at most)
`⌈log_3(n-1)⌉ + 1` hidden layers. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent050


namespace Agent051

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

"Better Neural Network Expressivity: Subdividing the Simplex"
(Bakaev, Brunck, Hertrich, Stade, Yehudayoff)

**Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`.

## Modelling choices

* We encode `ℝ^n` as `Fin n → ℝ`.
* Affine maps `ℝ^a → ℝ^b` are encoded concretely as `x ↦ A.mulVec x + c` for a matrix `A`
  and a bias vector `c` (structure `AffMap`).
* A "ReLU network with `k` hidden layers computing `f`" is defined recursively on `k`
  (predicate `IsReLUComputable n k f`): with `0` hidden layers, `f` itself must be an
  affine map `ℝ^n → ℝ`; with `k+1` hidden layers, `f` factors as `g ∘ ReLU ∘ T` where `T`
  is an affine map `ℝ^n → ℝ^m`, `ReLU` is applied componentwise, and `g` is computable with
  `k` hidden layers. This is the literal unwinding of the alternating-composition
  definition in the paper.
* `ReLUn n k` is defined as the set of functions computable with **exactly** `k` hidden
  layers (the literal reading of "representable with `k` hidden layers"). Note that a
  ReLU network can always simulate the identity function on one extra hidden layer
  (e.g. `x ↦ ReLU(x) - ReLU(-x)`), so in fact `ReLUn n k ⊆ ReLUn n (k+1)` holds
  mathematically, meaning the "exactly `k`" and "at most `k`" readings coincide as sets;
  we simply pick the more literal "exactly `k`" phrasing.
* `CPWL n` is defined as the set of continuous functions `f : ℝ^n → ℝ` such that there is
  a *finite* family of affine functions with the property that `f` agrees with (at least)
  one member of the family on a neighborhood of every point -- i.e. `f` is genuinely
  locally affine, glued from finitely many affine pieces. This is a real
  piecewise-linearity condition (not "max of affine functions", and not "representable by
  some ReLU network").
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded via `Real.logb 3` and `Nat.ceil`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias vector. -/
structure AffMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- The function computed by an affine map: `x ↦ A x + c`. -/
def AffMap.eval {a b : ℕ} (T : AffMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `IsReLUComputable n k f` means that `f : ℝ^n → ℝ` is computed by a ReLU network with
`n` inputs and exactly `k` hidden layers, i.e. by an alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations with
componentwise ReLU applications, as in the paper's definition of a ReLU network. -/
def IsReLUComputable : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : AffMap n 1, ∀ x, f x = T.eval x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : AffMap n m) (g : (Fin m → ℝ) → ℝ),
        IsReLUComputable m k g ∧ ∀ x, f x = g (fun i => relu (T.eval x i))

/-- `ReLUn n k`: the set of functions `ℝ^n → ℝ` representable by a ReLU network with
exactly `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | IsReLUComputable n k f}

/-- An affine function `ℝ^n → ℝ`, given by a linear functional plus a constant. -/
def IsAffine (n : ℕ) (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x, g x = (∑ i, a i * x i) + b

/-- `CPWL n`: the set of continuous, genuinely piecewise-linear functions `ℝ^n → ℝ`, i.e.
continuous functions that agree, on a neighborhood of every point, with one member of a
single finite family of affine functions. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
        ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ),
          (∀ j, IsAffine n (g j)) ∧
          ∀ x : Fin n → ℝ, ∃ j, ∃ ε > 0, ∀ y, dist y x < ε → f y = g j y}

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so `n - 1 ≥ 2`). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n - 1 : ℕ) : ℝ)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent051


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


namespace Agent053

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

"Better Neural Network Expressivity: Subdividing the Simplex"
(Bakaev, Brunck, Hertrich, Stade, Yehudayoff).

Theorem 2. For n ≥ 3, we have CPWL_n = ReLU_{n, ⌈log_3 (n-1)⌉ + 1}.

We encode ℝ^n as `Fin n → ℝ`.
-/

/-- The ReLU activation function on ℝ. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise (vector) ReLU on ℝ^m. -/
def reluVec {m : ℕ} (v : Fin m → ℝ) : Fin m → ℝ := fun i => relu (v i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix `A` and a bias
vector `c`, computing `x ↦ A * x + c`. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- The function `ℝ^a → ℝ^b` computed by an affine transformation. -/
def AffineMap.apply {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `computesReLUExact k n f` means `f : ℝ^n → ℝ` is computed by a ReLU network with
*exactly* `k` hidden layers, i.e. by an alternating composition

    T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)

of `k + 1` affine transformations `T^(1), …, T^(k+1)` with componentwise ReLU applied
after each of the first `k` of them. The hidden layer widths `n_1, …, n_k` are existentially
quantified (chosen by the network), while the input width is `n` and the output width is `1`
(functions here are real-valued). The definition proceeds by recursion on the number of
hidden layers: with `0` hidden layers a network is a single affine map `ℝ^n → ℝ`; with
`k + 1` hidden layers, a network first applies an affine map `T : ℝ^n → ℝ^m` followed by
componentwise ReLU, then feeds the result into a network with `k` hidden layers. -/
def computesReLUExact : (k : ℕ) → (n : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | 0, n, f => ∃ T : AffineMap n 1, ∀ x, f x = T.apply x 0
  | (k + 1), n, f =>
      ∃ (m : ℕ) (T : AffineMap n m) (g : (Fin m → ℝ) → ℝ),
        computesReLUExact k m g ∧ ∀ x, f x = g (reluVec (T.apply x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers. (This is the standard reading of `ReLU_{n,k}` in the depth-
separation literature: since the identity on ℝ can itself be computed with one hidden ReLU
layer via `x = ReLU(x) - ReLU(-x)`, a network with `j` hidden layers can always be padded
into one with any `k ≥ j` hidden layers computing the same function, so "exactly k" and
"at most k" give the same monotone family of classes, and "at most k" is the version for
which statements like Theorem 1 and Theorem 2 — asserting that *smaller* depths suffice —
are meaningful.) -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ j ≤ k, computesReLUExact j n f}

/-- An affine function `ℝ^n → ℝ`, i.e. `x ↦ ⟨w, x⟩ + b` for some weight vector `w` and
bias `b`. -/
def IsAffineFun (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (w : Fin n → ℝ) (b : ℝ), ∀ x, f x = (∑ i, w i * x i) + b

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: those `f` that
are continuous and admit a finite family of affine "pieces" such that every point of `ℝ^n`
has a neighborhood on which `f` coincides with one of these pieces. This is a genuine
polyhedral-subdivision-flavored definition of CPWL (local agreement with finitely many
affine functions), not a "representable by a ReLU network" or "max of affine functions"
definition. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
        ∃ (N : ℕ) (pieces : Fin N → (Fin n → ℝ) → ℝ),
          (∀ i, IsAffineFun n (pieces i)) ∧
          ∀ x : Fin n → ℝ, ∃ i : Fin N, ∃ ε > 0, ∀ y, dist y x < ε → f y = pieces i y}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so that `n - 1 ≥ 2`
and the logarithm is well-defined and positive). We use the real logarithm `Real.logb 3`
together with `Nat.ceil`. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3 (n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent053


namespace Agent054

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

"Better Neural Network Expressivity: Subdividing the Simplex"
(Bakaev, Brunck, Hertrich, Stade, Yehudayoff).

Theorem 2. For n ≥ 3, we have CPWL_n = ReLU_{n, ⌈log_3(n−1)⌉ + 1}.

## Modelling choices

* `ℝ^n` is modelled as `Vec n := Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is modelled concretely as
  `x ↦ A *ᵥ x + c` for a matrix `A` and a vector `c` (structure `AffineMap`).
* A ReLU network with exactly `k` hidden layers computing `f : Vec n → ℝ` is
  defined by recursion on `k`: with `0` hidden layers it is a single affine
  map into `ℝ`; with `k+1` hidden layers it is an affine map into some hidden
  width `m`, followed by componentwise ReLU, followed by a `k`-hidden-layer
  network on the resulting `m`-dimensional vector. This exactly reproduces
  the alternating composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`
  from the paper, with `k+1` affine maps and `k` applications of ReLU.
* `ReLUn n k` is taken to be the set of functions representable with **at
  most** `k` hidden layers (the standard reading in the depth-hierarchy
  literature, and the one under which `ReLUn n k` is monotone in `k`, so
  that the statement "the exact threshold depth `⌈log_3(n-1)⌉+1` suffices
  and is necessary" is a meaningful, non-vacuous equality with `CPWL n`).
* `CPWL n` is defined as: `f` is continuous **and** there is a finite family
  of closed convex regions covering `ℝ^n`, together with an affine function
  for each region, such that `f` agrees with the corresponding affine
  function on each region. This is a genuine piecewise-linearity condition
  (finite polyhedral-type subdivision + local affine agreement), not a
  "representable by a ReLU network" or "max of affine functions" definition.
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined using the real logarithm
  `Real.logb 3` together with `Nat.ceil`.
-/

/-- We model `ℝ^n` concretely as functions `Fin n → ℝ`. -/
abbrev Vec (n : ℕ) := Fin n → ℝ

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of ReLU to a vector. -/
def reluVec {n : ℕ} (x : Vec n) : Vec n := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix `A`
and a translation vector `c`, acting as `x ↦ A * x + c`. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Vec b

/-- The function computed by an affine transformation. -/
def AffineMap.eval {a b : ℕ} (T : AffineMap a b) (x : Vec a) : Vec b :=
  Matrix.mulVec T.A x + T.c

/-- `NetComputes k n f` means `f : ℝ^n → ℝ` is computed (exactly) by a ReLU
network with `k` hidden layers, i.e. by an alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine
transformations (with freely chosen hidden widths) and `k` componentwise
applications of ReLU. -/
def NetComputes : (k : ℕ) → (n : ℕ) → (Vec n → ℝ) → Prop
  | 0, n, f => ∃ T : AffineMap n 1, f = fun x => T.eval x 0
  | (k + 1), n, f =>
      ∃ (m : ℕ) (T : AffineMap n m) (g : Vec m → ℝ),
        NetComputes k m g ∧ f = fun x => g (reluVec (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU
network with **at most** `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set (Vec n → ℝ) :=
  { f | ∃ k' ≤ k, NetComputes k' n f }

/-- A scalar-valued affine function `ℝ^n → ℝ`. -/
def IsAffineFun (n : ℕ) (f : Vec n → ℝ) : Prop :=
  ∃ (w : Vec n) (b : ℝ), f = fun x => (∑ i, w i * x i) + b

/-- `CPWL n` is the set of continuous, piecewise linear functions `ℝ^n → ℝ`:
functions that are continuous and admit a finite covering of `ℝ^n` by
closed convex regions, on each of which `f` agrees with some affine
function. -/
def CPWL (n : ℕ) : Set (Vec n → ℝ) :=
  { f | Continuous f ∧
      ∃ (m : ℕ) (P : Fin m → Set (Vec n)) (a : Fin m → (Vec n → ℝ)),
        (∀ i, Convex ℝ (P i)) ∧
        (∀ i, IsClosed (P i)) ∧
        (⋃ i, P i) = Set.univ ∧
        (∀ i, IsAffineFun n (a i)) ∧
        (∀ i x, x ∈ P i → f x = a i x) }

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from the statement of Theorem 2. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL n = ReLUn n (⌈log_3(n-1)⌉ + 1)`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent054


namespace Agent055

/-- ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on vectors, encoding `ℝ^m` as `Fin m → ℝ`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias
vector, in the style `x ↦ A * x + c`. -/
structure AffMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation: `x ↦ A * x + c`. -/
def AffMap.eval {a b : ℕ} (T : AffMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, T.A i j * x j) + T.c i

/-- A scalar-valued function `ℝ^n → ℝ` is affine if it has the form `x ↦ a ⬝ x + b`
for some fixed vector `a` and scalar `b`. -/
def IsAffineFun {n : ℕ} (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x, g x = (∑ j, a j * x j) + b

/--
`ComputedByReLUNet n k f` means that `f : ℝ^n → ℝ` is computed by a ReLU network with
*exactly* `k` hidden layers, i.e. by the alternating composition
`T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}`
of `k + 1` affine transformations `T^{(1)}, …, T^{(k+1)}` (with `ReLU` applied
componentwise between consecutive affine transformations), as in the paper's
definition of a ReLU network of depth `k + 1`. The base case `k = 0` (depth `1`,
no hidden layers) is a single affine transformation `ℝ^n → ℝ`, with no ReLU applied.
The recursive case peels off the first affine transformation `T^{(1)} : ℝ^n → ℝ^m`,
applies `ReLU` componentwise, and requires the remainder to be computed by a network
with `k` hidden layers on the intermediate dimension `m`.
-/
def ComputedByReLUNet : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => IsAffineFun f
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : AffMap n m) (g : (Fin m → ℝ) → ℝ),
        ComputedByReLUNet m k g ∧ ∀ x, f x = g (reluVec (T.eval x))

/--
`ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers. We choose the "at most" reading: a network with `j`
hidden layers can always be padded to `j + 1` hidden layers computing the same
function (insert an extra affine transformation that is the identity, preceded by
`ReLU`, using the identity `x = ReLU(x) - ReLU(-x)`), so the exactly-`j` classes
for `j ≤ k` are nested increasingly in `j` and their union is the natural notion of
"representable with `k` hidden layers available", matching the depth-hierarchy
statement of Theorem 2.
-/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ j ≤ k, ComputedByReLUNet n j f}

/--
`CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: those
functions that are continuous, and additionally, at every point, locally agree with
one of finitely many affine functions drawn from a single fixed finite family. This
is a genuine piecewise-linearity condition (finitely many affine "pieces" covering
`ℝ^n`, glued continuously), not a definition in terms of ReLU networks and not a
max-of-affine normal form.
-/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
       ∃ (m : ℕ) (g : Fin m → ((Fin n → ℝ) → ℝ)), (∀ i, IsAffineFun (g i)) ∧
         ∀ x : Fin n → ℝ, ∃ i, ∃ U ∈ nhds x, Set.EqOn f (g i) U}

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so that
`n - 1 ≥ 2`, as a natural number before casting to `ℝ`). -/
def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n - 1 : ℕ) : ℝ)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 : ∀ n : ℕ, n ≥ 3 → CPWL n = ReLUn n (depthBound n) := sorry

end Agent055


namespace Agent056

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

`CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}` for `n ≥ 3`.

## Modelling choices

* Vectors `ℝ^n` are encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is packaged as a matrix `A : Matrix (Fin b) (Fin a) ℝ`
  together with a bias vector `bias : Fin b → ℝ`, evaluated as `x ↦ A.mulVec x + bias`.
* A ReLU network with input dimension `n` and `k` hidden layers and (scalar) output is
  defined as an inductive family `ReLUNet n k`:
  - `output T` : a network with `0` hidden layers, i.e. a single affine map
    `T : AffMap n 1` (this realizes `T^{(1)}`, the depth-`1` case with no hidden layers).
  - `layer T rest` : a network with `k+1` hidden layers, consisting of an affine map
    `T : AffMap n m` (this is `T^{(1)}`) followed by componentwise `ReLU`, followed by a
    network `rest : ReLUNet m k` computing the rest of the alternating composition
    `T^{(k+2)} ∘ ReLU ∘ ⋯ ∘ ReLU ∘ T^{(2)}`.
  Unfolding `ReLUNet.compute` on `layer T₁ (layer T₂ (⋯ (output T_{k+1})))` literally produces
  `T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}` applied to the input, matching the paper's
  definition of what a ReLU network computes.
* `ReLUn n k` is the set of functions representable with **at most** `k` hidden layers
  (i.e. `∃ k' ≤ k`, a network with `k'` hidden layers computing `f`). This is the standard
  convention in the neural-network-depth literature (e.g. Hertrich et al.): it makes
  `ReLUn n k` monotone increasing in `k`, which is what makes an *equality*
  `CPWL_n = ReLU_{n,k}` (rather than merely `⊇`) a sensible and true statement once `k`
  reaches the stated depth bound, since any network can be padded with extra layers that
  implement the identity via `ReLU(x) - ReLU(-x) = x`.
* `CPWL n` is defined mathematically (not via ReLU networks, and not as a "max of finitely
  many affine functions" normal form) as: `f` is continuous, and there is a *finite* family
  of affine functionals `ℝ^n → ℝ` such that every point `x` has a neighborhood on which `f`
  coincides with (at least) one member of the family. This is the standard "finite polyhedral
  subdivision, affine on each piece" reading of continuous piecewise linearity.
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined explicitly using the real logarithm
  `Real.logb 3` and `Nat.ceil`, exactly mirroring the paper's real-valued ceiling expression.
-/

/-- The scalar ReLU function `x ↦ max 0 x`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (v : Fin m → ℝ) : Fin m → ℝ := fun i => relu (v i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias vector. -/
structure AffMap (a b : ℕ) where
  /-- The linear part. -/
  A : Matrix (Fin b) (Fin a) ℝ
  /-- The translation part. -/
  bias : Fin b → ℝ

/-- Evaluation of an affine transformation: `x ↦ A * x + bias`. -/
def AffMap.eval {a b : ℕ} (T : AffMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.bias

/-- A ReLU network with input dimension `n`, `k` hidden layers, and scalar output,
built by peeling off affine transformations and `ReLU` activations one hidden layer at a time,
exactly following the alternating composition
`T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}`
from the paper's definition of a ReLU network. -/
inductive ReLUNet : ℕ → ℕ → Type where
  /-- `0` hidden layers: a single affine map `ℝ^n → ℝ` (this is `T^{(1)}` alone). -/
  | output {n : ℕ} (T : AffMap n 1) : ReLUNet n 0
  /-- `k+1` hidden layers: an affine map to a hidden layer of width `m`, a `ReLU`
  activation, and then a network with `k` hidden layers computing the rest. -/
  | layer {n m k : ℕ} (T : AffMap n m) (rest : ReLUNet m k) : ReLUNet n (k + 1)

/-- The function `ℝ^n → ℝ` computed by a ReLU network, following the alternating composition
of affine maps and componentwise `ReLU`. -/
def ReLUNet.compute {n k : ℕ} : ReLUNet n k → (Fin n → ℝ) → ℝ
  | ReLUNet.output T, x => T.eval x 0
  | ReLUNet.layer T rest, x => rest.compute (reluVec (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
**at most** `k` hidden layers (the standard convention making `ReLUn n ·` monotone in `k`). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, ∃ net : ReLUNet n k', ∀ x, f x = net.compute x }

/-- An affine functional `ℝ^n → ℝ`, given by a coefficient vector and a constant term. -/
structure AffineFunctional (n : ℕ) where
  /-- The linear coefficients. -/
  coeff : Fin n → ℝ
  /-- The constant term. -/
  const : ℝ

/-- Evaluation of an affine functional: `x ↦ ⟨coeff, x⟩ + const`. -/
def AffineFunctional.eval {n : ℕ} (g : AffineFunctional n) (x : Fin n → ℝ) : ℝ :=
  (Finset.univ.sum fun i => g.coeff i * x i) + g.const

/-- `CPWL n` is the space of continuous piecewise-linear functions `ℝ^n → ℝ`: functions that
are continuous and are given, near every point, by one of finitely many affine functionals
(a finite polyhedral subdivision on whose pieces `f` is affine). -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
      ∃ (m : ℕ) (g : Fin m → AffineFunctional n),
        ∀ x : Fin n → ℝ, ∃ i : Fin m, ∀ᶠ y in nhds x, f y = (g i).eval y }

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from the paper, as a natural number, using the real
base-`3` logarithm and the ceiling function. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent056


namespace Agent057

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):  for `n ≥ 3`,  `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`.

Modelling choices (see summary at the end of the task too):
* Vectors `ℝ^n` are modelled as `Fin n → ℝ`.
* Affine maps `ℝ^a → ℝ^b` are modelled concretely and explicitly as `x ↦ A * x + c` via a
  custom structure `AffMap` (a matrix `A` and bias vector `c`), to avoid any risk of
  silently picking up Mathlib's `Continuous`/`Convex`-heavy general affine map API for
  something that is meant to be an elementary, concrete object.
* "Computed by a ReLU network with `k` hidden layers" is defined as an inductive predicate
  `ComputesReLU n m k f`, built by induction on `k`: `k = 0` is a bare affine map
  (`depth = 1`, i.e. `T^{(1)}`, no hidden layer), and the `k+1` case prepends an affine map
  followed by a componentwise ReLU in front of a `k`-hidden-layer network. This directly
  encodes the alternating composition
  `T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}` from the paper.
* `ReLUn n k` is taken to mean representable with **at most** `k` hidden layers (not
  exactly `k`): this is the reading under which the classes are increasing in `k` and under
  which Theorem 2's single bound `⌈log_3(n-1)⌉ + 1` can equal all of `CPWL_n` (rather than
  merely some strict subset that jumps around non-monotonically with `k`).
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of polyhedral
  pieces (each cut out by finitely many affine inequalities) covering `ℝ^n`, on each of
  which `f` agrees with some affine function. This is a genuine piecewise-linearity
  condition (finite polyhedral subdivision + affine on each piece), not a "representable by
  some ReLU network" nor a "max of affine functions" definition.
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined via the real logarithm `Real.logb 3` and
  `Nat.ceil` (`⌈·⌉₊`), matching the paper's `⌈log_3(n−1)⌉ + 1` literally.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^n`. -/
def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix `A` and a bias
vector `c`, computing `x ↦ A * x + c`. -/
structure AffMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an `AffMap`. -/
def AffMap.eval {a b : ℕ} (T : AffMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `ComputesReLU n m k f` means: the function `f : ℝ^n → ℝ^m` is computed by a ReLU
network with `k` hidden layers, i.e. `f` is the alternating composition
`T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}` of `k + 1` affine transformations
`T^{(1)}, …, T^{(k+1)}` with componentwise ReLU applied after each of the first `k` of
them. The `base` case (`k = 0`) is a single affine transformation (depth `1`, no hidden
layer); the `step` case peels off the first affine transformation and ReLU, leaving a
network with one fewer hidden layer. -/
inductive ComputesReLU : (n m k : ℕ) → ((Fin n → ℝ) → (Fin m → ℝ)) → Prop
  | base {n m : ℕ} (T : AffMap n m) : ComputesReLU n m 0 T.eval
  | step {n p m k : ℕ} (T : AffMap n p) (g : (Fin p → ℝ) → (Fin m → ℝ))
      (hg : ComputesReLU p m k g) :
      ComputesReLU n m (k + 1) (g ∘ reluVec ∘ T.eval)

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with at
most `k` hidden layers (output dimension `m = 1`). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, ComputesReLU n 1 k' (fun x _ => f x)}

/-- A polyhedron in `ℝ^n`: the intersection of finitely many closed affine half-spaces
`{x | a i x ≤ b i}`. -/
def IsPolyhedron (n : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (a : ι → (Fin n → ℝ) →ₗ[ℝ] ℝ) (b : ι → ℝ),
    S = ⋂ i, {x | a i x ≤ b i}

/-- `f : ℝ^n → ℝ` is continuous and piecewise linear: it is continuous, and there is a
finite polyhedral subdivision of `ℝ^n` (a finite family of polyhedra covering `ℝ^n`) on
each piece of which `f` agrees with some affine function. -/
def IsCPWL (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  Continuous f ∧
    ∃ (ι : Type) (_ : Fintype ι) (S : ι → Set (Fin n → ℝ)) (A : ι → (Fin n → ℝ) →ᵃ[ℝ] ℝ),
      (∀ i, IsPolyhedron n (S i)) ∧
        (⋃ i, S i) = Set.univ ∧
        (∀ i, ∀ x ∈ S i, f x = A i x)

/-- The set of continuous piecewise linear functions `ℝ^n → ℝ`. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | IsCPWL n f}

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from Theorem 2. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent057


namespace Agent058

open Filter

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We encode `ℝ^n` concretely as `Fin n → ℝ`.

Modelling choices (see final summary):
* Affine maps `ℝ^a → ℝ^b` are given concretely by a matrix and a bias vector.
* A "ReLU network with `k` hidden layers" is encoded via a width function on `ℕ`
  (built from the fixed input dimension `n` and a free choice of hidden widths)
  together with a dependent family of affine layers, composed with `reluVec` inserted
  after every layer except the last.
* `ReLUn n k` is the set of functions representable with **at most** `k` hidden
  layers (monotone increasing in `k`), which is the standard reading making
  `ReLU_{n,k}` an increasing filtration of `CPWL_n` and matches Theorem 1's
  statement "`MAX_{3^n+2} ∈ ReLU_{n+1}`".
* `CPWL n` is defined as: continuous, and locally (in a neighborhood of every
  point) equal to one of finitely many affine functions. This is a genuine
  piecewise-linearity condition, not a "max of affine functions" normal form and
  not "representable by some ReLU network".
* The depth bound uses the real logarithm `Real.logb 3` together with `Nat.ceil`.
-/

/-- The ReLU activation function on `ℝ`. -/
noncomputable def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector in `ℝ^m`. -/
noncomputable def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ :=
  fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias
vector: `x ↦ A * x + c`. -/
structure AffineMapRn (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine map on a vector. -/
noncomputable def AffineMapRn.eval {a b : ℕ} (T : AffineMapRn a b) (x : Fin a → ℝ) :
    Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- Given the input dimension `n` and a choice of hidden widths `hidden : ℕ → ℕ`
(where `hidden i` is meant to be the width of hidden layer `i`), `mkWidths n hidden`
is the width function `widths : ℕ → ℕ` with `widths 0 = n` (definitionally) and
`widths (i+1) = hidden i`. -/
def mkWidths (n : ℕ) (hidden : ℕ → ℕ) : ℕ → ℕ
  | 0 => n
  | (i + 1) => hidden i

/-- `netApply widths T k m x` evaluates the first `m` layers `T 0, ..., T (m-1)` of a
network with layer-width function `widths` and layer family `T`, applying `relu`
after every layer *except* layer `k` (the intended final layer, `T^(k+1)` in the
paper's notation, indexed `k` here since layers are `0`-indexed). Composing up to
`m = k + 1` therefore computes
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`, i.e. a network with `k` hidden
layers. -/
noncomputable def netApply (widths : ℕ → ℕ)
    (T : (i : ℕ) → AffineMapRn (widths i) (widths (i + 1))) (k : ℕ) :
    (m : ℕ) → (Fin (widths 0) → ℝ) → (Fin (widths m) → ℝ)
  | 0, x => x
  | (m + 1), x =>
      let y := (T m).eval (netApply widths T k m x)
      if m + 1 ≤ k then reluVec y else y

/-- The set of functions `ℝ^n → ℝ` representable by a ReLU network with *at most*
`k` hidden layers: there is some `j ≤ k`, a choice of `j` hidden widths, and a
family of `j + 1` affine layers `T^(1), ..., T^(j+1)` (of matching dimensions,
with output dimension `1`) whose alternating ReLU composition computes `f`. -/
noncomputable def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ (j : ℕ), j ≤ k ∧
      ∃ (hidden : ℕ → ℕ) (hwj : mkWidths n hidden (j + 1) = 1)
        (T : (i : ℕ) → AffineMapRn (mkWidths n hidden i) (mkWidths n hidden (i + 1))),
        f = fun x => netApply (mkWidths n hidden) T j (j + 1) x
          (Fin.cast hwj.symm (0 : Fin 1))}

/-- The set of continuous piecewise-linear functions `ℝ^n → ℝ`: `f` is continuous,
and there is a *finite* family of affine functions such that every point of `ℝ^n`
has a neighborhood on which `f` agrees with one member of the family. -/
noncomputable def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (g : Fin m → AffineMapRn n 1),
      ∀ x : Fin n → ℝ, ∃ i : Fin m, ∀ᶠ y in nhds x, f y = (g i).eval y 0}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, using the real logarithm
base `3` and `Nat.ceil`. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, every continuous piecewise-linear function on `ℝ^n`
is representable by a ReLU network with `⌈log_3 (n - 1)⌉ + 1` hidden layers, and
conversely. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent058


namespace Agent059

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):  for `n ≥ 3`,  `CPWL n = ReLUn n (⌈log_3 (n-1)⌉ + 1)`.

## Modelling choices

* Vectors `ℝ^n` are encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is given concretely by a weight function
  `A : Fin b → Fin a → ℝ` (playing the role of a `b × a` matrix) and a bias
  `bias : Fin b → ℝ`, acting by `x ↦ A * x + bias`.
* A ReLU network with `k` hidden layers computing `f : ℝ^n → ℝ` is encoded
  recursively (`ReLURepresentable`): with `0` hidden layers, `f` must itself be an
  affine function (this is the single transformation `T^(1) : ℝ^n → ℝ`); with
  `k+1` hidden layers, `f` factors as `g ∘ ReLU ∘ T` where `T : ℝ^n → ℝ^m` is an
  affine transformation and `g : ℝ^m → ℝ` is representable with `k` hidden layers.
  Unwinding the recursion recovers exactly the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper.
* `ReLUn n k` is taken to be the functions representable with **at most** `k`
  hidden layers (`∃ j ≤ k, ReLURepresentable n j f`), not exactly `k`. This is the
  standard reading (a network with `j` hidden layers can always be padded to `k ≥ j`
  hidden layers, e.g. using `x = ReLU x - ReLU (-x)` as an identity pass-through
  layer), and it is also the reading under which the stated equality
  `CPWL n = ReLUn n (⌈log_3 (n-1)⌉ + 1)` can be true: e.g. affine functions lie in
  `CPWL n` but are representable with `0` hidden layers, not exactly
  `⌈log_3 (n-1)⌉ + 1` of them.
* `CPWL n` is defined as: `f` is continuous, and there is a finite polyhedral
  subdivision of `ℝ^n` (finitely many closed polyhedra, each cut out by finitely
  many affine inequalities, whose union is all of `ℝ^n`) on each piece of which `f`
  agrees with some affine function. This is a genuine piecewise-linearity condition,
  not a "representable by some ReLU network" definition and not a max-of-affine
  normal form.
* The depth bound is `Nat.ceil (Real.logb 3 (n - 1)) + 1`, matching
  `⌈log_3(n-1)⌉ + 1` with the real base-3 logarithm and the real ceiling.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `Fin m → ℝ`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- A concrete affine transformation `ℝ^a → ℝ^b`, given by a weight function
`A` (playing the role of a `b × a` matrix) and a bias vector, acting as
`x ↦ A * x + bias`. -/
structure AffineMap (a b : ℕ) where
  A : Fin b → Fin a → ℝ
  bias : Fin b → ℝ

/-- Evaluation of an `AffineMap`. -/
def AffineMap.eval {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, T.A i j * x j) + T.bias i

/-- `f : ℝ^n → ℝ` is an affine (real-valued) function. -/
def IsAffineFun {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (w : Fin n → ℝ) (c : ℝ), ∀ x, f x = (∑ j, w j * x j) + c

/-- `f` is representable by a ReLU network `ℝ^n → ℝ` with exactly `k` hidden
layers: with `0` hidden layers `f` must itself be affine (the single affine
transformation `T^(1)`); with `k + 1` hidden layers, `f` factors as
`g ∘ ReLU ∘ T` for an affine `T : ℝ^n → ℝ^m` and `g` representable with `k`
hidden layers. Unwinding this recursion gives precisely the alternating
composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`. -/
def ReLURepresentable : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => IsAffineFun f
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : AffineMap n m) (g : (Fin m → ℝ) → ℝ),
        ReLURepresentable m k g ∧ f = fun x => g (reluVec (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU
network with **at most** `k` hidden layers (see the module docstring for why
"at most", rather than "exactly", is the right reading here). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ j ≤ k, ReLURepresentable n j f }

/-- A closed polyhedron in `ℝ^n`, cut out by finitely many affine
inequalities `⟨a i, x⟩ ≤ b i`. -/
def IsPolyhedron {n : ℕ} (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (a : Fin m → (Fin n → ℝ)) (b : Fin m → ℝ),
    S = {x | ∀ i, (∑ j, a i j * x j) ≤ b i}

/-- `CPWL n`: the continuous, piecewise-linear functions `ℝ^n → ℝ`. `f` is
continuous, and there is a finite polyhedral subdivision of `ℝ^n` (finitely
many closed polyhedra whose union is all of `ℝ^n`) on each piece of which `f`
agrees with some affine function. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
      ∃ (m : ℕ) (S : Fin m → Set (Fin n → ℝ)) (g : Fin m → (Fin n → ℝ) → ℝ),
        (∀ i, IsPolyhedron (S i)) ∧
        (∀ i, IsAffineFun (g i)) ∧
        (⋃ i, S i) = Set.univ ∧
        (∀ i, ∀ x ∈ S i, f x = g i x) }

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from the theorem, using the real
base-3 logarithm and the real (`Nat.ceil`) ceiling. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent059


namespace Agent060

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

  "Better Neural Network Expressivity: Subdividing the Simplex"
  Bakaev, Brunck, Hertrich, Stade, Yehudayoff.

  Theorem 2. For n ≥ 3, we have CPWL_n = ReLU_{n, ⌈log_3(n−1)⌉ + 1}.

## Modelling choices (see summary at the bottom of the file / final report)

* Vectors `ℝ^n` are modelled as `Fin n → ℝ`.
* Affine transformations `ℝ^a → ℝ^b` are modelled concretely as `x ↦ A.mulVec x + bias`
  for a matrix `A` and bias vector `bias`.
* "Representable with `k` hidden layers" is modelled as an inductive-style existential
  (`represents n k f`) capturing the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` exactly, by peeling off the first affine
  map + ReLU and recursing on the remaining `k` hidden layers.
* `ReLUn n k` is taken to be the functions representable with **at most** `k` hidden
  layers (i.e. with some `k' ≤ k`). This is the reading that makes Theorem 2 a sensible
  equality: extra hidden layers can always be padded in via the identity trick
  `x = ReLU x - ReLU (-x)`, so the "exactly k" and "at most k" classes coincide in
  substance, but "at most k" is the reading under which `ReLUn n k` is monotone in `k`
  and matches the informal statement "representable with k hidden layers" (using no more
  than the allotted depth).
* `CPWL n` is defined genuinely: `f` is continuous, and there is a *finite* family of
  affine functions such that every point of `ℝ^n` has an open neighbourhood on which `f`
  agrees with one member of the family. This is a real piecewise-linearity condition
  (finitely many affine pieces, glued continuously), not a restatement of "computable by
  a ReLU network" and not a max-of-affine normal form.
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined literally via `Real.logb 3` and
  `Nat.ceil` (`⌈·⌉₊`), avoiding any need to relate it to `Nat.clog`.
-/

/-- Vectors in `ℝ^n`, modelled as functions `Fin n → ℝ`. -/
abbrev Vec (n : ℕ) := Fin n → ℝ

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector. -/
def reluVec {n : ℕ} (x : Vec n) : Vec n := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix `A` and a bias
vector, computing `x ↦ A * x + bias`. -/
structure AffMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  bias : Vec b

/-- Evaluation of an affine transformation. -/
def AffMap.eval {a b : ℕ} (T : AffMap a b) (x : Vec a) : Vec b :=
  T.A.mulVec x + T.bias

/-- `represents n k f` holds if `f : ℝ^n → ℝ` is computed by a ReLU network with exactly
`k` hidden layers, i.e. `f` arises as the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations
`T^(1), …, T^(k+1)` with `k` componentwise ReLU applications interleaved (matching the
definition of a ReLU network with `k` hidden layers, depth `k + 1`, from the paper).
We define this by recursion on `k`, peeling off the first affine map together with its
following ReLU, and recursing on the remaining `k` hidden layers of the tail network. -/
def represents : (n : ℕ) → (k : ℕ) → (Vec n → ℝ) → Prop
  | n, 0, f => ∃ T : AffMap n 1, ∀ x, f x = T.eval x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : AffMap n m) (g : Vec m → ℝ),
        represents m k g ∧ ∀ x, f x = g (reluVec (T.eval x))

/-- A function `ℝ^n → ℝ` is affine if it has the form `x ↦ (a ⬝ x) + b` for some vector
`a` of coefficients and scalar `b`. -/
def IsAffine {n : ℕ} (g : Vec n → ℝ) : Prop :=
  ∃ (a : Vec n) (b : ℝ), ∀ x : Vec n, g x = (∑ i, a i * x i) + b

/-- `ReLUn n k`, the set of functions `ℝ^n → ℝ` representable by a ReLU network with at
most `k` hidden layers (see the module docstring for why "at most" is the right reading
for Theorem 2). -/
def ReLUn (n k : ℕ) : Set (Vec n → ℝ) :=
  { f | ∃ k' ≤ k, represents n k' f }

/-- `CPWL n`, the set of continuous piecewise-linear functions `ℝ^n → ℝ`: `f` is
continuous, and there is a finite family of affine functions such that every point of
`ℝ^n` has an open neighbourhood on which `f` agrees with one member of the family. -/
def CPWL (n : ℕ) : Set (Vec n → ℝ) :=
  { f | Continuous f ∧
      ∃ S : Finset (Vec n → ℝ), (∀ g ∈ S, IsAffine g) ∧
        ∀ x : Vec n, ∃ g ∈ S, ∃ U : Set (Vec n), IsOpen U ∧ x ∈ U ∧ Set.EqOn f g U }

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from Theorem 2, defined literally via the real
logarithm `Real.logb 3` and `Nat.ceil`. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 : ∀ n : ℕ, n ≥ 3 → CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent060


namespace Agent061

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):  For `n ≥ 3`, `CPWL n = ReLUn n (⌈log_3 (n-1)⌉ + 1)`.

Modelling choices:
* `ℝ^m` is encoded as `Fin m → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is a function of the form `x ↦ A.mulVec x + c`
  for a matrix `A` and a vector `c` (`IsAffineMap`); the special case of a scalar-valued
  affine map `ℝ^a → ℝ` is `IsAffineFn`.
* `relu` is `max 0 ·` on `ℝ`, applied componentwise as `reluVec`.
* `NetComputes k n f` says `f : ℝ^n → ℝ` is computed by *some* ReLU network with
  exactly `k` hidden layers, via the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` described in the paper. It is defined by
  recursion on `k`: with `0` hidden layers the network is a single affine map; with
  `k+1` hidden layers, the input first passes through an affine map into some
  intermediate dimension `m`, then ReLU, and the rest is computed by a network with `k`
  hidden layers on `ℝ^m`.
* `ReLUn n k` is taken to be functions representable with **at most** `k` hidden layers
  (not exactly `k`): since one can always pad a network with extra affine/ReLU layers
  that act as the identity, the "at most" and "exactly, for k large enough" classes
  coincide in spirit, but "at most" is the reading under which `ReLUn n k` forms an
  increasing chain in `k` and Theorem 2 (which asserts these classes eventually cover
  all of `CPWL n`) is the natural, true statement.
* `CPWL n` is defined as continuous functions that are *locally* equal to a member of
  some finite family of affine functions, near every point — a genuine finite
  polyhedral / piecewise-affine condition, not a "max of affine pieces" normal form and
  not "representable by a ReLU network".
* The depth bound `⌈log_3 (n-1)⌉ + 1` is encoded via the real logarithm `Real.logb 3`
  and `Nat.ceil`.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- `f : ℝ^a → ℝ^b` is an affine transformation: `f x = A * x + c` for some matrix `A`
and vector `c`. -/
def IsAffineMap {a b : ℕ} (f : (Fin a → ℝ) → (Fin b → ℝ)) : Prop :=
  ∃ (A : Matrix (Fin b) (Fin a) ℝ) (c : Fin b → ℝ), ∀ x, f x = A.mulVec x + c

/-- A scalar-valued affine function `ℝ^n → ℝ`. -/
def IsAffineFn {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x : Fin n → ℝ, f x = (∑ i, a i * x i) + b

/-- `NetComputes k n f` : `f : ℝ^n → ℝ` is computed by a ReLU network with exactly
`k` hidden layers, i.e. by the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations. -/
def NetComputes : ℕ → (n : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | 0, _n, f => IsAffineFn f
  | k + 1, n, f =>
      ∃ (m : ℕ) (T : (Fin n → ℝ) → (Fin m → ℝ)) (g : (Fin m → ℝ) → ℝ),
        IsAffineMap T ∧ NetComputes k m g ∧ ∀ x, f x = g (reluVec (T x))

/-- The set of functions `ℝ^n → ℝ` representable by a ReLU network with **at most**
`k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, NetComputes k' n f}

/-- `f : ℝ^n → ℝ` is continuous piecewise linear: it is continuous, and there is a
finite family of affine functions such that near every point `f` agrees with one of
them. -/
def IsCPWL {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  Continuous f ∧
    ∃ S : Finset ((Fin n → ℝ) → ℝ),
      (∀ h ∈ S, IsAffineFn h) ∧
        ∀ x : Fin n → ℝ, ∃ h ∈ S, ∀ᶠ y in nhds x, f y = h y

/-- The space of continuous piecewise linear functions `ℝ^n → ℝ`. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) := {f | IsCPWL f}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from the theorem, for `n ≥ 3` (so `n - 1 ≥ 2`
as a real number). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3 (n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent061


namespace Agent062

/-
  Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network
  Expressivity: Subdividing the Simplex"):

    For n ≥ 3,  CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}.

  Modelling choices (see summary at the bottom / final chat message):
  * ℝ^n is encoded as `Fin n → ℝ`.
  * Affine maps `ℝ^a → ℝ^b` are encoded concretely as `x ↦ A * x + bias`
    for a matrix `A` and vector `bias`.
  * A ReLU network with exactly `k` hidden layers computing `f` is defined
    by structural recursion on `k` via the inductive predicate `NetComputes`,
    mirroring the alternating composition
      T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)
    from the paper. The hidden widths `n_1, …, n_k` are existentially
    quantified (they are unconstrained parameters of the network).
  * `ReLUn n k` is taken to be the set of functions representable with
    *at most* `k` hidden layers. This is the reading under which Theorem 2
    is a meaningful (non-monotone-trivial) equality: `ReLUn n k` is then
    manifestly monotone in `k`, matching the standard convention in the
    depth-separation literature (extra layers can always simulate fewer,
    e.g. by using an affine layer that acts as the identity).
  * `CPWL n` is defined genuinely: `f` is continuous, and there is a finite
    polyhedral subdivision of `ℝ^n` (each piece cut out by finitely many
    linear inequalities) together with a finite family of affine functions,
    one per piece, that `f` agrees with on that piece.
  * The depth bound `⌈log_3(n-1)⌉ + 1` is encoded literally using
    `Real.logb 3` and `Nat.ceil`.
-/

/-- The scalar ReLU function. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ :=
  fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias vector. -/
structure Affine (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  bias : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def Affine.eval {a b : ℕ} (T : Affine a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.bias

/--
  `NetComputes n k f` means: `f : ℝ^n → ℝ` is computed by a ReLU network with
  exactly `k` hidden layers, i.e. by an alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine
  transformations with pointwise ReLU in between. The base case `k = 0` is a
  single affine transformation `ℝ^n → ℝ` (no hidden layer, no ReLU). The
  hidden-layer widths are implicit existential parameters of the network.
-/
inductive NetComputes : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | zero {n : ℕ} (T : Affine n 1) :
      NetComputes n 0 (fun x => T.eval x 0)
  | succ {n m k : ℕ} (T : Affine n m) (g : (Fin m → ℝ) → ℝ)
      (hg : NetComputes m k g) :
      NetComputes n (k + 1) (fun x => g (reluVec (T.eval x)))

/--
  `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU
  network with *at most* `k` hidden layers (see the discussion above for why
  this, rather than "exactly `k`", is the reading used here).
-/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, NetComputes n k' f }

/-- An affine (real-valued) function `ℝ^n → ℝ`, given via its coefficients and constant term. -/
def IsAffineFun {n : ℕ} (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (c : ℝ), ∀ x, g x = (∑ i, a i * x i) + c

/--
  A polyhedron in `ℝ^n`: the solution set of finitely many linear
  inequalities `⟨L j, x⟩ ≤ b j`.
-/
def IsPolyhedron {n : ℕ} (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (L : Fin m → (Fin n → ℝ)) (b : Fin m → ℝ),
    S = { x | ∀ j, (∑ i, L j i * x i) ≤ b j }

/--
  `CPWL n`: the continuous, piecewise-linear functions `ℝ^n → ℝ`. A function
  `f` belongs to this set iff it is continuous and there is a finite
  polyhedral subdivision of `ℝ^n` (finitely many polyhedral pieces covering
  all of `ℝ^n`) together with a matching finite family of affine functions,
  one per piece, such that `f` agrees with the corresponding affine function
  on each piece.
-/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (S : Fin m → Set (Fin n → ℝ)) (g : Fin m → (Fin n → ℝ) → ℝ),
          (∀ i, IsPolyhedron (S i)) ∧
          (∀ i, IsAffineFun (g i)) ∧
          (⋃ i, S i) = Set.univ ∧
          (∀ i x, x ∈ S i → f x = g i x) }

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from Theorem 2, for `n ≥ 3`. -/
def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent062


namespace Agent063

open scoped BigOperators

/-- The ReLU activation function on `ℝ`. -/
def reluR (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => reluR (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given explicitly by a matrix `A` (encoded as a
function `Fin b → Fin a → ℝ`) and a bias vector `c`: `x ↦ A x + c`. -/
def affineApply {a b : ℕ} (A : Fin b → Fin a → ℝ) (c : Fin b → ℝ) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j : Fin a, A i j * x j) + c i

/-- `f : ℝ^n → ℝ` is a scalar affine function, i.e. what a ReLU network with `0` hidden
layers (a single affine transformation `ℝ^n → ℝ^1`, identified with `ℝ`) computes. -/
def IsAffine (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (c : Fin n → ℝ) (b : ℝ), ∀ x, f x = (∑ i : Fin n, c i * x i) + b

/-- `Represents n k f` : `f : ℝ^n → ℝ` is computed by a ReLU network with *exactly* `k`
hidden layers, in the sense of the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations
`T^(1), …, T^(k+1)` (of possibly different widths), with componentwise ReLU applied after
each of the first `k` of them.

Defined by recursion on `k`: with `0` hidden layers the network is a single affine map
`ℝ^n → ℝ` (`T^(1)` alone, no ReLU applied). With `k + 1` hidden layers, the first affine
map `T^(1) : ℝ^n → ℝ^m` (of some width `m`) is applied, then ReLU is applied componentwise,
and the remaining `k` hidden layers compute some `g : ℝ^m → ℝ` from the result, matching
`f = g ∘ ReLU ∘ T^(1)`. -/
def Represents : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => IsAffine n f
  | n, (k + 1), f =>
      ∃ (m : ℕ) (A : Fin m → Fin n → ℝ) (bvec : Fin m → ℝ) (g : (Fin m → ℝ) → ℝ),
        Represents m k g ∧ ∀ x, f x = g (reluVec (affineApply A bvec x))

/-- `ReLUn n k` : the functions `ℝ^n → ℝ` representable by a ReLU network with *at most*
`k` hidden layers. We read `ReLU_{n,k}` as "at most `k`" rather than "exactly `k`": this is
the standard convention in the expressivity literature, it makes the class monotone in
`k`, and it is the reading under which Theorem 2's equality `CPWL_n = ReLU_{n,k}` for a
*single, fixed* depth `k = ⌈log_3(n-1)⌉ + 1` can hold — e.g. affine functions
(representable with `0` hidden layers) must lie in `ReLU_{n,k}` for every `k ≥ 0`, which
holds definitionally only under the "at most" reading. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, Represents n k' f}

/-- A closed polyhedron in `ℝ^n`: a finite intersection of affine half-spaces
`{x | a_j ⬝ x + b_j ≤ 0}`. -/
def IsPolyhedron (n : ℕ) (P : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (a : Fin m → Fin n → ℝ) (b : Fin m → ℝ),
    P = {x | ∀ j : Fin m, (∑ i : Fin n, a j i * x i) + b j ≤ 0}

/-- `f : ℝ^n → ℝ` is continuous and piecewise linear: `f` is continuous, and there is a
finite family of closed polyhedra covering all of `ℝ^n`, on each of which `f` agrees with
some affine function. This is a genuine finite polyhedral subdivision, not merely
"representable by some ReLU network" and not a max-of-affine normal form. -/
def IsCPWL (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  Continuous f ∧
    ∃ (m : ℕ) (P : Fin m → Set (Fin n → ℝ)) (g : Fin m → (Fin n → ℝ) → ℝ),
      (∀ j, IsPolyhedron n (P j)) ∧
      (∀ j, IsAffine n (g j)) ∧
      (⋃ j, P j) = Set.univ ∧
      (∀ j, ∀ x ∈ P j, f x = g j x)

/-- `CPWL n` : the set of continuous piecewise linear functions `ℝ^n → ℝ`. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) := {f | IsCPWL n f}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so that
`n - 1 ≥ 2 > 0` and the real logarithm behaves as expected). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) : CPWL n = ReLUn n (depthBound n) := sorry

end Agent063


namespace Agent064

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We work with vectors `ℝ^n` encoded as `Fin n → ℝ`.

## Modelling choices

* An affine transformation `ℝ^a → ℝ^b` is given by a matrix `A : Matrix (Fin b) (Fin a) ℝ`
  and a bias vector `c : Fin b → ℝ`, computing `x ↦ A x + c`.
* A ReLU network with `k` hidden layers and input dimension `n` is encoded as a list `L` of
  `k + 1` such affine layers (matching the `k + 1` affine transformations
  `T^(1), ..., T^(k+1)` in the paper), where ReLU is applied componentwise after every layer
  *except* the last one. The layers carry their own declared input/output dimensions; a
  network is only considered to *represent* `f` if these dimensions actually chain together
  correctly starting from `n` and ending at `1` (see `isRepresented` / `evalLayers` below).
  We use the "exactly `k` hidden layers" reading of `ReLU_{n,k}`: since layer widths are
  otherwise unconstrained, a network with fewer hidden layers can always be padded to one
  with more (e.g. via an extra identity-simulating layer `y = ReLU(y) - ReLU(-y)`), so this
  reading coincides with "at most `k`" and is the more literal reading of "representable with
  `k` hidden layers".
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of affine
  functions such that every point has an open neighbourhood on which `f` coincides with one
  member of the family. This is a genuine local-piecewise-affinity condition, not a
  max-of-affine normal form and not "representable by some network".
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded using `Real.logb 3` and `Nat.ceil` (`⌈·⌉₊`).
-/

/-- ReLU on `ℝ`. -/
def reluR (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluV {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => reluR (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, i.e. `x ↦ A x + c`. -/
structure Affine (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def Affine.eval {a b : ℕ} (T : Affine a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, T.A i j * x j) + T.c i

/-- A single layer of a ReLU network: an affine map together with its declared input and
output dimensions. -/
structure Layer where
  inDim : ℕ
  outDim : ℕ
  map : Affine inDim outDim

/-- Evaluate a list of layers as the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ... ∘ ReLU ∘ T^(1)`, i.e. ReLU is applied after every layer except
the last one in the list. The input/output vectors are dimension-tagged (`Σ'`-packaged) so
that the definition is total; if a layer's declared input dimension does not match the
actual incoming dimension, evaluation returns a dummy `0`-dimensional value (this can never
match a genuine `1`-dimensional output, so it never causes a network with mismatched
dimensions to spuriously "represent" a function). -/
def evalLayers : List Layer → (Σ' a : ℕ, Fin a → ℝ) → (Σ' b : ℕ, Fin b → ℝ)
  | [], v => v
  | (T :: []), ⟨a', x⟩ =>
      if h : a' = T.inDim then
        ⟨T.outDim, T.map.eval (h ▸ x)⟩
      else
        ⟨0, fun i => i.elim0⟩
  | (T :: T2 :: rest), ⟨a', x⟩ =>
      if h : a' = T.inDim then
        evalLayers (T2 :: rest) ⟨T.outDim, reluV (T.map.eval (h ▸ x))⟩
      else
        ⟨0, fun i => i.elim0⟩

/-- `f : ℝ^n → ℝ` is computed (represented) by a ReLU network with exactly `k` hidden
layers, i.e. there is a list of `k + 1` affine layers whose alternating ReLU-composition,
started from the actual input dimension `n`, computes `f` and ends in dimension `1`. -/
def isRepresented (n k : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ L : List Layer, L.length = k + 1 ∧
    ∀ x : Fin n → ℝ, evalLayers L ⟨n, x⟩ = (⟨1, fun _ => f x⟩ : Σ' b : ℕ, Fin b → ℝ)

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
exactly `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) := {f | isRepresented n k f}

/-- `f` is affine on `ℝ^n` with coefficients `a` and intercept `b`. -/
def IsAffineWith (n : ℕ) (a : Fin n → ℝ) (b : ℝ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ y, f y = (∑ j, a j * y j) + b

/-- `CPWL n`: the continuous, piecewise-linear functions `ℝ^n → ℝ`. We require continuity
together with the existence of a *finite* family of affine functions such that every point
of `ℝ^n` has an open neighbourhood on which `f` agrees with one member of the family. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (a : Fin m → (Fin n → ℝ)) (b : Fin m → ℝ),
      ∀ x : Fin n → ℝ, ∃ i : Fin m, ∃ U : Set (Fin n → ℝ),
        IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, f y = (∑ j, a i j * y j) + b i}

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from Theorem 2, with `n - 1` taken as a natural
number (valid since `n ≥ 3` in the theorem, so `n - 1 ≥ 2`). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n - 1 : ℕ) : ℝ)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent064


namespace Agent065

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):  for `n ≥ 3`,  `CPWL n = ReLUn n (⌈log_3 (n-1)⌉ + 1)`.

Modelling choices (see the summary at the end of the accompanying report):
* `ℝ^n` is encoded as `Fin n → ℝ`.
* `ReLUn n k` is the set of functions representable by a network with *exactly* `k`
  hidden layers (matching the paper's literal definition of `ReLU_{n,k}`).
* `CPWL n` is defined via continuity plus a genuine finite local-affine-pieces
  condition, independent of the network machinery.
-/

/-- The ReLU activation function on `ℝ`. -/
noncomputable def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^n`. -/
noncomputable def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias
vector: `x ↦ A x + bias`. -/
structure Affine (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  bias : Fin b → ℝ

/-- The function `ℝ^a → ℝ^b` computed by an affine transformation. -/
def Affine.apply {a b : ℕ} (T : Affine a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.bias

/-- A ReLU network with input dimension `n` and `k` hidden layers, i.e. `k + 1`
affine transformations `T^(1), ..., T^(k+1)` of matching consecutive dimensions
`dims 0 = n, dims 1, ..., dims k, dims (k+1) = 1`.  `layer i` is `T^(i+1)`,
the affine map from layer `i` to layer `i + 1`. -/
structure ReLUNetwork (n k : ℕ) where
  dims : ℕ → ℕ
  dims_zero : dims 0 = n
  dims_last : dims (k + 1) = 1
  layer : (i : ℕ) → Affine (dims i) (dims (i + 1))

/-- The activation vector at layer `i` of the network on input `x` (for `i ≤ k+1`):
the input at `i = 0`, and otherwise the affine transformation of the previous layer's
activations, followed by ReLU unless this is the final (output) layer `k+1` — this
implements the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`. -/
noncomputable def ReLUNetwork.forward {n k : ℕ} (N : ReLUNetwork n k) :
    (i : ℕ) → (Fin n → ℝ) → (Fin (N.dims i) → ℝ)
  | 0, x => fun j => x (Fin.cast N.dims_zero j)
  | i + 1, x =>
      let out := (N.layer i).apply (N.forward i x)
      if i + 1 = k + 1 then out else reluVec out

/-- The scalar output of the network on input `x` (the network's final layer has
width 1). -/
noncomputable def ReLUNetwork.output {n k : ℕ} (N : ReLUNetwork n k) (x : Fin n → ℝ) :
    ℝ :=
  N.forward (k + 1) x (Fin.cast N.dims_last.symm (0 : Fin 1))

/-- A network `N` with `k` hidden layers *computes* / *represents* `f : ℝ^n → ℝ` if
its output agrees with `f` on every input. -/
def ReLUNetwork.computes {n k : ℕ} (N : ReLUNetwork n k) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x, N.output x = f x

/-- `ReLUn n k`: the functions `ℝ^n → ℝ` representable by a ReLU network with
*exactly* `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ N : ReLUNetwork n k, N.computes f}

/-- An affine (degree-1 polynomial) function `ℝ^n → ℝ`. -/
def IsAffineFun {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x, f x = (∑ i, a i * x i) + b

/-- `CPWL n`: the continuous piecewise-linear functions `ℝ^n → ℝ`, i.e. continuous
functions that, near every point, agree with one of a finite family of affine
functions. This is the genuine geometric definition (a finite collection of affine
"pieces" covering `ℝ^n`, matching `f` locally), independent of ReLU networks and not
phrased as a max-of-affine normal form. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ),
      (∀ i, IsAffineFun (g i)) ∧ ∀ x, ∃ i, ∀ᶠ y in nhds x, f y = g i y}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, as a natural number, using
the real logarithm `Real.logb 3` and `Nat.ceil`. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL n = ReLUn n (⌈log_3 (n - 1)⌉ + 1)`. -/
theorem theorem2 : ∀ n : ℕ, n ≥ 3 → CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent065


/-
Formalization of Theorem 2 of arXiv:2505.14338
("Better Neural Network Expressivity: Subdividing the Simplex")

Modelling choices (agent 066):
* Vectors ℝ^n are encoded as `Fin n → ℝ`.
* Affine maps ℝ^a → ℝ^b are encoded concretely as a matrix `A : Matrix (Fin b) (Fin a) ℝ`
  together with a bias vector `b : Fin b → ℝ`, evaluated via `A.mulVec x + b`.
* "Computed by a ReLU network with k hidden layers" is formalized by recursion on k:
  a depth-1 network (0 hidden layers) is a single affine map into `Fin 1 → ℝ` (we read off
  its unique coordinate); a network with `k+1` hidden layers first applies an affine map
  into some hidden width `m`, then componentwise ReLU, and then continues as a network
  with `k` hidden layers computing `ℝ^m → ℝ`. This exactly mirrors the alternating
  composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ... ∘ ReLU ∘ T^(1)` from the paper.
* `ReLUn n k` is taken to mean representable with **at most** `k` hidden layers (not
  exactly `k`). This is the standard reading and the one that makes Theorem 2 true: since
  a `k`-hidden-layer function can always be re-expressed with `k+1` hidden layers (e.g. by
  using an extra layer computing `x ↦ ReLU(x) - ReLU(-x) = x` componentwise before
  continuing), the classes `ReLUn n k` are monotone increasing in `k`, and the theorem's
  equality is with the class of functions using at most the stated number of layers.
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of affine maps
  `g : Fin m → (ℝ^n →ᵃ[ℝ] ℝ)` such that `f` agrees with some `g i` on a neighborhood of
  every point `x`. This is a genuine local-piecewise-affine condition (not a max-of-affine
  normal form, and not "representable by some ReLU network"), matching the standard
  definition of continuous piecewise linear functions via a finite family of affine pieces.
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined directly via `Real.logb 3` and `Nat.ceil`.
-/

namespace Agent066

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (v : Fin m → ℝ) : Fin m → ℝ := fun i => relu (v i)

/-- `ReLUComputable n k f` means: `f : ℝ^n → ℝ` is computed by a ReLU network with `k`
hidden layers, i.e. by the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ... ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations
`T^(1) : ℝ^n → ℝ^{n_1}, ..., T^(k+1) : ℝ^{n_k} → ℝ`, with componentwise ReLU applied after
each of the first `k` affine maps. We recurse on `k`: the base case `k = 0` is a single
affine map `ℝ^n → ℝ` (depth 1, no hidden layers); the successor case peels off the first
affine map (into some hidden width `m`), applies ReLU, and recurses with `k` hidden
layers on the resulting `ℝ^m → ℝ` network. -/
def ReLUComputable : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f =>
      ∃ (A : Matrix (Fin 1) (Fin n) ℝ) (b : Fin 1 → ℝ),
        ∀ x : Fin n → ℝ, f x = (A.mulVec x + b) 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (g : (Fin m → ℝ) → ℝ),
        ReLUComputable m k g ∧
        ∀ x : Fin n → ℝ, f x = g (reluVec (A.mulVec x + b))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers (see the module docstring for why "at most" is the reading
that makes Theorem 2 true). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, ReLUComputable n k' f}

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: those that
are continuous and agree, in a neighborhood of every point, with one member of some fixed
*finite* family of affine functions. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
        ∃ (m : ℕ) (g : Fin m → ((Fin n → ℝ) →ᵃ[ℝ] ℝ)),
          ∀ x : Fin n → ℝ, ∃ i : Fin m, f =ᶠ[nhds x] (g i)}

/-- The depth bound from Theorem 2: `⌈log_3(n - 1)⌉ + 1` hidden layers. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL n = ReLUn n (⌈log_3(n-1)⌉ + 1)`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent066


namespace Agent067

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

**Modelling choices** (see summary at call site):
* Vectors `ℝ^n` are encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is encoded concretely as `x ↦ W.mulVec x + c` for a
  matrix `W : Matrix (Fin b) (Fin a) ℝ` and bias `c : Fin b → ℝ`.
* "Representable with `k` hidden layers" (`Represents`) is defined by recursion on `k`,
  directly mirroring the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper, peeling off the first affine
  map / ReLU pair at each recursive step. `ReLUn n k` is the set of functions representable
  with *exactly* `k` hidden layers (the direct reading of "the subset of `CPWL_n`
  representable with `k` hidden layers"); note that padding with an extra trivial
  identity-simulating hidden layer (via `ReLU(x) - ReLU(-x) = x`) shows this is in fact
  monotone in `k`, so "exactly `k`" and "at most `k`" agree for `k ≥ 1`, making this choice
  harmless for the truth of the theorem.
* `CPWL n` is defined as: `f` is continuous, and there is a *finite family* of affine
  functions (indexed by `Fin m` for some `m`) such that every point `x` has a neighbourhood
  on which `f` coincides with (at least) one member of the family. This is a genuine
  piecewise-linearity condition (local agreement with a finite affine atlas), not a
  max-of-affine normal form and not "representable by a ReLU network".
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded with the real `Real.logb 3` and `Nat.ceil`
  (`⌈·⌉₊`), applied to `(n : ℝ) - 1`.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^n`. -/
def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => relu (x i)

/-- Evaluation of an affine transformation `ℝ^a → ℝ^b` given by a matrix `W` and bias `c`. -/
def affineEval {a b : ℕ} (W : Matrix (Fin b) (Fin a) ℝ) (c : Fin b → ℝ) (x : Fin a → ℝ) :
    Fin b → ℝ :=
  W.mulVec x + c

/-- `Represents n k f` means `f : ℝ^n → ℝ` is computed by a ReLU network with `k` hidden
layers, i.e. `f = T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` for some affine transformations
`T^(1), …, T^(k+1)` of compatible (existentially quantified, except the input dimension `n`
and output dimension `1`) widths.

The recursion peels off the first affine map `T^(1) : ℝ^n → ℝ^m` together with the
following `ReLU`, leaving a function `h` of the remaining `k - 1` layers on the
(existentially quantified) hidden width `m`. The base case `k = 0` is a single affine map
`ℝ^n → ℝ` (`T^(1)`, with no `ReLU` applied). -/
def Represents : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ w : Fin n → ℝ, ∃ b : ℝ, f = fun x => (∑ i, w i * x i) + b
  | n, k + 1, f =>
      ∃ m : ℕ, ∃ W : Matrix (Fin m) (Fin n) ℝ, ∃ c : Fin m → ℝ, ∃ h : (Fin m → ℝ) → ℝ,
        Represents m k h ∧ f = fun x => h (reluVec (affineEval W c x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
exactly `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Represents n k f}

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: `f` is
continuous, and there is a finite family of affine functions, indexed by `Fin m`, such that
every point of `ℝ^n` has a neighbourhood on which `f` agrees with one member of the family. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
        ∃ m : ℕ, ∃ w : Fin m → Fin n → ℝ, ∃ b : Fin m → ℝ,
          ∀ x : Fin n → ℝ, ∃ i : Fin m,
            ∀ᶠ y in nhds x, f y = (∑ j, w i j * y j) + b i}

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from the paper, for `n ≥ 3` (so `n - 1 ≥ 2`). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent067


namespace Agent068

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

  Theorem 2. For n ≥ 3, CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}.

## Modelling choices

* The *input/output* space `ℝ^n` for the functions in `CPWL n` and `ReLUn n k` is encoded
  as `Fin n → ℝ`.
* Internally, the *hidden layers* of a ReLU network are encoded using the ambient
  "infinite vector" type `Vec := ℕ → ℝ`. An affine transformation is data consisting of a
  matrix `A : ℕ → ℕ → ℝ` and a bias vector, evaluated by summing over the first `inDim`
  coordinates only (`inDim` supplied at evaluation time). This avoids having to carry
  dependent equality proofs / `cast`s between `Fin (width i) → ℝ` types at every layer of
  the network, while still faithfully modelling "matrix times vector plus bias" affine
  maps between spaces of the prescribed (finite) dimensions.
* `ReLUn n k` is defined using the **"at most k hidden layers"** reading (i.e. as a union
  over `k' ≤ k` of the functions computable with *exactly* `k'` hidden layers). This is the
  reading that makes Theorem 2 true as a literal set equality: `ReLUn n k` must be
  monotone (increasing) in `k`, since e.g. all affine functions (0 hidden layers) lie in
  `CPWL n` and hence must lie in `ReLUn n K` for the specific depth bound `K`, and
  more generally the right-hand side of the theorem should contain everything representable
  with fewer than the stated number of hidden layers too.
* `CPWL n` is defined directly as: `f` is continuous, and there is a *finite* family of
  convex regions covering `ℝ^n` together with a matching finite family of affine functions,
  such that `f` agrees with the corresponding affine function on each region. This is a
  genuine piecewise-linearity condition (a finite polyhedral-type subdivision on each piece
  of which `f` is affine) and is deliberately *not* phrased as "representable by some ReLU
  network" nor as a max-of-affine-functions normal form.
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded using `Real.logb 3` and `Nat.ceil`.
-/

/-- The ambient space used internally for the (possibly high-dimensional) hidden layers of
a ReLU network: an "infinite vector", i.e. a function `ℕ → ℝ`, of which only finitely many
coordinates are ever actually used by a given network. -/
abbrev Vec := ℕ → ℝ

/-- The ReLU activation function `ReLU(x) = max{0, x}`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector. -/
def reluVec (x : Vec) : Vec := fun i => relu (x i)

/-- An affine transformation, given concretely as a matrix `A` (`A i j` is the `(i,j)`
entry) together with a bias vector. Evaluation is with respect to an explicit input
dimension `inDim`, so that `T.eval inDim x` computes `A * x + bias`, restricting the matrix
product to the first `inDim` coordinates of `x` (the mathematically relevant ones for an
input space of dimension `inDim`). -/
structure AffineMap where
  A : ℕ → ℕ → ℝ
  bias : Vec

/-- Evaluate an affine transformation `x ↦ A * x + bias`, with `A * x` summed over the
first `inDim` coordinates of `x` (the input dimension of this affine map). -/
def AffineMap.eval (T : AffineMap) (inDim : ℕ) (x : Vec) : Vec :=
  fun i => (Finset.range inDim).sum (fun j => T.A i j * x j) + T.bias i

/-- Apply `i` layers of "affine transformation followed by componentwise ReLU" to an input
vector, given a sequence `width : ℕ → ℕ` of layer widths (`width 0` is the input dimension)
and a sequence `T : ℕ → AffineMap` of affine transformations (`T j` maps from dimension
`width j` to dimension `width (j+1)`). -/
def networkForward (width : ℕ → ℕ) (T : ℕ → AffineMap) : ℕ → Vec → Vec
  | 0, x => x
  | (i + 1), x => reluVec ((T i).eval (width i) (networkForward width T i x))

/-- The scalar output computed by a network with `k` hidden layers: apply `k` layers of
affine-then-ReLU (via `networkForward`), then one final affine transformation `T k`
*without* a following ReLU, and read off the (single, by convention coordinate `0`) output
coordinate. This realizes the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper, with `T^(i)` corresponding to
`T (i-1)` here. -/
def networkCompute (width : ℕ → ℕ) (T : ℕ → AffineMap) (k : ℕ) (x : Vec) : ℝ :=
  ((T k).eval (width k) (networkForward width T k x)) 0

/-- Embed a finite-dimensional vector `x : Fin n → ℝ` into the ambient space `Vec`, padding
with zeros outside the first `n` coordinates. -/
def toVec (n : ℕ) (x : Fin n → ℝ) : Vec :=
  fun i => if h : i < n then x ⟨i, h⟩ else 0

/-- A ReLU network with input dimension `n` and exactly `k` hidden layers: a sequence of
layer widths `width 0, …, width (k+1)` with `width 0 = n` (the input dimension) and
`width (k+1) = 1` (the network outputs a scalar), together with the `k+1` affine
transformations `T 0, …, T k` of the alternating composition. -/
structure ReLUNetwork (n k : ℕ) where
  width : ℕ → ℕ
  hw0 : width 0 = n
  hwlast : width (k + 1) = 1
  T : ℕ → AffineMap

/-- The function `ℝ^n → ℝ` computed by a ReLU network. -/
def ReLUNetwork.compute (net : ReLUNetwork n k) (x : Fin n → ℝ) : ℝ :=
  networkCompute net.width net.T k (toVec n x)

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers (the union over `k' ≤ k` of those representable with exactly
`k'` hidden layers). See the module docstring for why "at most" (rather than "exactly") is
the reading under which Theorem 2 is a true statement. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, ∃ net : ReLUNetwork n k', f = net.compute }

/-- A function `ℝ^n → ℝ` is affine if it has the form `x ↦ ⟨a, x⟩ + b` for some vector `a`
and scalar `b`. -/
def IsAffineFun (n : ℕ) (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x : Fin n → ℝ, g x = (Finset.univ.sum fun i => a i * x i) + b

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: those `f` that
are continuous and admit a *finite* subdivision of `ℝ^n` into convex regions, together with
a matching finite family of affine functions, such that `f` agrees with the corresponding
affine function on each region of the subdivision. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (pieces : Fin m → (Fin n → ℝ) → ℝ) (region : Fin m → Set (Fin n → ℝ)),
          (∀ i, IsAffineFun n (pieces i)) ∧
          (∀ i, Convex ℝ (region i)) ∧
          (⋃ i, region i) = Set.univ ∧
          (∀ i (x : Fin n → ℝ), x ∈ region i → f x = pieces i x) }

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from the paper, for `n ≥ 3` (so `n - 1 ≥ 2 > 0` and
the logarithm is well-behaved). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) : CPWL n = ReLUn n (depthBound n) := sorry

end Agent068


namespace Agent069

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely as `x ↦ A * x + c`. -/
structure AffineMap' (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def AffineMap'.apply {a b : ℕ} (T : AffineMap' a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/--
A ReLU network from `ℝ^a` to `ℝ^b` with `k` hidden layers, encoded as the alternating
composition of `k + 1` affine transformations `T^(1), ..., T^(k+1)` with a ReLU applied
componentwise after each of the first `k` of them, and no ReLU after the last one. This
matches the definition of "depth `k + 1`" / "`k` hidden layers" from Section 1 of the
paper: `ReLUNet a b 0` is a single affine map (depth 1, 0 hidden layers), and
`ReLUNet.cons T rest` prepends one affine map `T` followed by a ReLU to a network `rest`
with one fewer hidden layer than the whole.
-/
inductive ReLUNet : ℕ → ℕ → ℕ → Type
  | last {a b : ℕ} (T : AffineMap' a b) : ReLUNet a b 0
  | cons {a b c k : ℕ} (T : AffineMap' a b) (rest : ReLUNet b c k) : ReLUNet a c (k + 1)

/-- The function `ℝ^a → ℝ^b` computed by a ReLU network. -/
def ReLUNet.eval : {a b k : ℕ} → ReLUNet a b k → (Fin a → ℝ) → (Fin b → ℝ)
  | _, _, _, ReLUNet.last T, x => T.apply x
  | _, _, _, ReLUNet.cons T rest, x => rest.eval (reluVec (T.apply x))

/--
`ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers (rather than *exactly* `k`). We choose "at most" because
the classes are monotone in `k`: a network with `k` hidden layers can always be padded
to `k + 1` hidden layers computing the same function, e.g. by widening a layer with an
extra pair of neurons computing `relu(x)` and `relu(-x)` for a coordinate `x` and having
the next affine map recombine them as `relu(x) - relu(-x) = x` before continuing as
before. Under the "exactly `k`" reading, `ReLUn n k` and `ReLUn n (k+1)` need not be
comparable and the set equality in Theorem 2 would generally fail; under "at most `k`"
the theorem correctly expresses that `⌈log_3(n-1)⌉ + 1` hidden layers are both
necessary and sufficient to represent every function in `CPWL_n`.
-/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, ∃ net : ReLUNet n 1 k', ∀ x, f x = net.eval x 0}

/-- An affine function `ℝ^n → ℝ`, i.e. `x ↦ a ⬝ x + b`. -/
def IsAffineFunc {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x, f x = (∑ i, a i * x i) + b

/--
`CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: those that are
continuous and, near every point, agree with one of finitely many affine functions. This
is a genuine piecewise-linearity condition (local agreement with a finite family of
affine pieces), not a statement about ReLU-representability or a max-of-affine normal
form.
-/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ), (∀ i, IsAffineFunc (g i)) ∧
      ∀ x, ∃ i, ∀ᶠ y in nhds x, f y = g i y}

/-- The depth bound `⌈log_3(n-1)⌉ + 1` appearing in Theorem 2. -/
def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉+1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent069


namespace Agent070

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex").

Modelling choices:
* Vectors `ℝ^n` are encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is encoded concretely as a pair `(A, c)` of a
  matrix and a bias vector, evaluating to `x ↦ A *ᵥ x + c`.
* A ReLU network with `k` hidden layers computing `f : (Fin n → ℝ) → ℝ` is encoded via
  the inductive relation `NetworkComputes n k f`, which directly mirrors the alternating
  composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper: the base case
  `k = 0` is a single affine map `n → 1` (no ReLU, one affine transformation, matching
  "depth 1 / 0 hidden layers"), and the inductive step peels off the first affine map
  `T^(1) : n → m`, applies `ReLU` componentwise, and feeds the result into a network with
  one fewer hidden layer.
* `ReLUn n k` is taken to be the functions representable with **at most** `k` hidden
  layers (`∃ j ≤ k`), not *exactly* `k`. This is the reading under which `ReLUn n k` is
  monotone in `k` (a hierarchy) and under which Theorem 2's equality
  `CPWL n = ReLUn n (depthBound n)` can hold as an equality of sets: with the "exactly k"
  reading, functions representable with fewer than `depthBound n` layers (e.g. any affine
  function, representable with `0` hidden layers) would be wrongly excluded from the
  right-hand side.
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of affine
  functions such that every point of `ℝ^n` has a neighbourhood on which `f` coincides
  with one member of the family (a genuine local piecewise-linearity / polyhedral-pieces
  condition, not a max-of-affine normal form and not "representable by some network").
* The depth bound `⌈log_3 (n - 1)⌉ + 1` is encoded using the real logarithm
  `Real.logb 3` together with `Nat.ceil`, applied to the real number `(n : ℝ) - 1`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias
vector. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation: `x ↦ A x + c`. -/
def AffineMap.eval {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (T.A.mulVec x) i + T.c i

/-- `NetworkComputes n k f` says that `f : ℝ^n → ℝ` is computed by a ReLU network with
`k` hidden layers, i.e. by an alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations with
componentwise `ReLU` in between, the last transformation landing in `ℝ^1`.

The base case `k = 0` is a single affine transformation `ℝ^n → ℝ^1` with no `ReLU`
applied (a network with `0` hidden layers / depth `1`). The successor case peels off the
first affine transformation `T^(1) : ℝ^n → ℝ^m`, applies `ReLU` componentwise, and
requires the rest of the network (on the remaining `j` hidden layers) to compute the
resulting function of the `ReLU`'d intermediate vector. -/
inductive NetworkComputes : (n : ℕ) → (k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | base (n : ℕ) (T : AffineMap n 1) :
      NetworkComputes n 0 (fun x => T.eval x 0)
  | step (n m j : ℕ) (T : AffineMap n m) (g : (Fin m → ℝ) → ℝ)
      (hg : NetworkComputes m j g) :
      NetworkComputes n (j + 1) (fun x => g (reluVec (T.eval x)))

/-- `ReLUn n k`: the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ j, j ≤ k ∧ NetworkComputes n j f }

/-- An affine (degree-`≤ 1` polynomial) function `ℝ^n → ℝ`. -/
def IsAffine {n : ℕ} (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x : Fin n → ℝ, g x = (∑ i, a i * x i) + b

/-- `CPWL n`: the set of continuous, piecewise-linear functions `ℝ^n → ℝ`, i.e.
continuous functions `f` for which there is a *finite* family of affine functions such
that every point `x` has a neighbourhood on which `f` agrees with one member of the
family. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (g : Fin m → ((Fin n → ℝ) → ℝ)),
          (∀ i, IsAffine (g i)) ∧
          ∀ x : Fin n → ℝ, ∃ i, ∀ᶠ y in nhds x, f y = g i y }

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so `n - 1 ≥ 2`). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3 (n - 1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent070


namespace Agent071

/-!
Formalization of Theorem 2 of arXiv:2505.14338
("Better Neural Network Expressivity: Subdividing the Simplex").

Encoding choices (see summary at the end of the task):
* `ℝ^n` is encoded as `Fin n → ℝ`.
* `ReLUn n k` is the set of functions computable by a ReLU network with **at most**
  `k` hidden layers (the standard convention in this literature, which makes
  `ReLUn n k` monotone in `k` and makes the statement of Theorem 2 meaningful).
* `CPWL n` is defined via continuity plus a genuine *local* piecewise-affine condition:
  there is a finite family of affine functions such that every point has a
  neighbourhood on which `f` agrees with one member of the family.
* The depth bound `⌈log_3 (n-1)⌉ + 1` is encoded with the real logarithm
  `Real.logb 3` and `Nat.ceil`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias
vector, as `x ↦ A x + c`. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def AffineMap.eval {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, T.A i j * x j) + T.c i

/-- `f : ℝ^n → ℝ` is computed by a ReLU network with **exactly** `k` hidden layers:
there is a sequence of layer widths `w 0 = n, w 1, ..., w k, w (k+1) = 1` and
`k + 1` affine transformations `T i : ℝ^{w i} → ℝ^{w (i+1)}`, `i = 0, ..., k`, such
that, starting from the input `x`, alternately applying `T i` and (except after the
final, output-producing, affine map) componentwise ReLU produces a sequence of
vectors `z 0, ..., z (k+1)` with `z 0 = x`, `z (k+1)` one-dimensional, and
`f x = z (k+1)`. This mirrors the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ... ∘ ReLU ∘ T^(1)` from the paper. -/
def ComputesWithHiddenLayers (n k : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (w : Fin (k + 2) → ℕ) (h0 : w 0 = n) (hL : w (Fin.last (k + 1)) = 1)
    (T : (i : Fin (k + 1)) → AffineMap (w i.castSucc) (w i.succ)),
    ∀ x : Fin n → ℝ, ∃ z : (i : Fin (k + 2)) → Fin (w i) → ℝ,
      z 0 = x ∘ Fin.cast h0 ∧
      (∀ i : Fin (k + 1), i.val < k →
        z i.succ = reluVec ((T i).eval (z i.castSucc))) ∧
      (∀ i : Fin (k + 1), i.val = k →
        z i.succ = (T i).eval (z i.castSucc)) ∧
      f x = z (Fin.last (k + 1)) (Fin.cast hL.symm 0)

/-- The set of functions `ℝ^n → ℝ` representable by a ReLU network with **at most**
`k` hidden layers. (Using "at most" rather than "exactly" is the standard reading
of `ReLU_{n,k}` in this literature; it is the reading that makes `ReLU_{n,k}`
monotone in `k`, as needed for the union over `k` to sensibly exhaust `CPWL_n`.) -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, ComputesWithHiddenLayers n k' f }

/-- An affine (i.e. degree ≤ 1 polynomial) function `ℝ^n → ℝ`. -/
def IsAffineFun {n : ℕ} (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x, g x = (∑ i, a i * x i) + b

/-- The space of continuous piecewise-linear (CPWL) functions `ℝ^n → ℝ`: continuous
functions that, near every point, coincide with one member of some fixed finite
family of affine functions. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ),
          (∀ j, IsAffineFun (g j)) ∧
          ∀ x : Fin n → ℝ, ∃ j : Fin m, ∃ U ∈ nhds x, Set.EqOn f (g j) U }

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so that
`(n : ℝ) - 1 ≥ 2`). -/
def depthBound (n : ℕ) : ℕ := ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent071


namespace Agent072

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

  "Better Neural Network Expressivity: Subdividing the Simplex"
  (Bakaev, Brunck, Hertrich, Stade, Yehudayoff)

Theorem 2. For n ≥ 3, we have CPWL_n = ReLU_{n, ⌈log_3(n−1)⌉ + 1}.

## Modelling choices

* Vectors `ℝ^n` are encoded as `Fin n → ℝ` (with its Pi topology / module structure).
* An affine transformation `ℝ^a → ℝ^b` is modelled concretely as a pair `(A, c)` of a
  matrix `A : Matrix (Fin b) (Fin a) ℝ` and a bias vector `c : Fin b → ℝ`, evaluated as
  `x ↦ A.mulVec x + c`.
* "Computed by a ReLU network with `k` hidden layers" is defined by structural recursion
  on `k`, directly mirroring the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper: a 0-hidden-layer network is
  a single affine map to `ℝ^1`; a `(k+1)`-hidden-layer network first applies an affine map
  `T : ℝ^n → ℝ^m`, then componentwise ReLU, then feeds the result into a `k`-hidden-layer
  network.
* `ReLUn n k` is taken to be the set of functions representable with **at most** `k`
  hidden layers (`∃ k' ≤ k, …`), not *exactly* `k`. This is the reading under which
  Theorem 2 is true: the right-hand side must be monotone in `k` (any function computable
  with fewer layers is in particular computable with more, e.g. by the standard
  `x = ReLU(x) − ReLU(−x)` identity-padding trick), and the "exactly `n` hidden layers"
  reading would generally fail to contain all of `CPWL_n` at the boundary value `n`, or
  would fail to be well-behaved as `n` increases, without extra padding lemmas.
* `CPWL n` is defined genuinely: `f` is continuous **and** there is a finite polyhedral
  subdivision of `ℝ^n` (each piece cut out by finitely many affine inequalities) together
  with an affine functional per piece that `f` agrees with on that piece. This is a real
  piecewise-linearity condition, independent of the ReLU-network machinery.
* The depth bound `⌈log_3(n−1)⌉ + 1` is defined using the real logarithm `Real.logb 3`
  composed with `Nat.ceil` (written `⌈·⌉₊`), exactly matching the informal statement,
  rather than via `Nat.clog`.
-/

/-- The scalar ReLU function. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^n`. -/
def reluV {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias
vector: `x ↦ A * x + c`. -/
structure AffineT (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def AffineT.eval {a b : ℕ} (T : AffineT a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `IsReLUNet n k f` means `f : ℝ^n → ℝ` is computed by a ReLU network with `k` hidden
layers, i.e. by an alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`
of `k + 1` affine transformations with `k` interleaved componentwise ReLUs. Defined by
recursion on `k`, peeling off the first affine map / ReLU pair from the input side. -/
def IsReLUNet : (n : ℕ) → (k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : AffineT n 1, f = fun x => T.eval x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : AffineT n m) (g : (Fin m → ℝ) → ℝ),
        IsReLUNet m k g ∧ f = fun x => g (reluV (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, IsReLUNet n k' f }

/-- A subset of `ℝ^n` is a (closed) polyhedron if it is a finite intersection of
halfspaces `{x | a_i · x ≤ b_i}`. -/
def isPolyhedron (n : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (a : Fin m → Fin n → ℝ) (b : Fin m → ℝ),
    S = {x | ∀ i, (∑ j, a i j * x j) ≤ b i}

/-- An affine functional `ℝ^n → ℝ`, i.e. `x ↦ c · x + d`. -/
def isAffineFunctional (n : ℕ) (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (c : Fin n → ℝ) (d : ℝ), g = fun x => (∑ j, c j * x j) + d

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: continuous
functions admitting a finite polyhedral subdivision of `ℝ^n` on each piece of which the
function agrees with some affine functional. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
      ∃ (m : ℕ) (P : Fin m → Set (Fin n → ℝ)) (g : Fin m → (Fin n → ℝ) → ℝ),
        (∀ i, isPolyhedron n (P i)) ∧
        (∀ i, isAffineFunctional n (g i)) ∧
        (⋃ i, P i) = Set.univ ∧
        (∀ i, ∀ x ∈ P i, f x = g i x) }

/-- The depth bound `⌈log_3(n − 1)⌉ + 1` from the paper. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n−1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent072


namespace Agent073

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):

  For n ≥ 3,  CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}.

Modelling choices (see summary at the end of the file):
* Vectors `ℝ^n` are encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is encoded concretely by a matrix and a bias
  vector, `x ↦ A * x + c`.
* "Computed by a ReLU network with `k` hidden layers" is encoded by the recursive
  predicate `IsReLURep`, unwinding exactly the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper.
* `ReLUn n k` uses *exactly* `k` hidden layers (matching the literal recursive
  unwinding of the definition of `ReLU_{n,k}` in the paper).
* `CPWL n` is defined by continuity together with local agreement, at every point,
  with one of finitely many affine functions -- a genuine piecewise-linearity
  condition that does not presuppose any max-of-affine normal form or ReLU
  representability.
-/

/-- The ReLU function on `ℝ`. -/
noncomputable def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`, encoded as `Fin m → ℝ`. -/
noncomputable def reluVec {m : ℕ} (v : Fin m → ℝ) : Fin m → ℝ := fun i => relu (v i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix `A` and a bias
vector `c`, computing `x ↦ A * x + c`. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def AffineMap.eval {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `IsReLURep n m k f` means the function `f : ℝ^n → ℝ^m` is computed by a ReLU
network with `k` hidden layers, i.e. by the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations
`T^(1), …, T^(k+1)` (with `T^(1) : ℝ^n → ℝ^{n_1}`, …, `T^(k+1) : ℝ^{n_k} → ℝ^m` for
some sequence of intermediate widths `n_1, …, n_k`).

The base case `k = 0` (depth `1`, no hidden layers) is a single affine map. The
recursive case peels off the first affine map `T^(1) : ℝ^n → ℝ^p` and the ReLU applied
to it, leaving a network with `k` hidden layers computing the rest. -/
noncomputable def IsReLURep : (n m k : ℕ) → ((Fin n → ℝ) → (Fin m → ℝ)) → Prop
  | n, m, 0, f => ∃ T : AffineMap n m, f = T.eval
  | n, m, (k + 1), f =>
      ∃ (p : ℕ) (T : AffineMap n p) (g : (Fin p → ℝ) → (Fin m → ℝ)),
        IsReLURep p m k g ∧ f = g ∘ (reluVec ∘ T.eval)

/-- `ReLUn n k`: the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*exactly* `k` hidden layers. We view `f : ℝ^n → ℝ` as the `ℝ^1`-valued function
`x ↦ (fun _ => f x)`. -/
noncomputable def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | IsReLURep n 1 k (fun x (_ : Fin 1) => f x) }

/-- `CPWL n`: the continuous piecewise-linear functions `ℝ^n → ℝ`. We say `f` is CPWL
if it is continuous and there is a *finite* set of affine functions `ℝ^n → ℝ` such that
every point of `ℝ^n` has a neighbourhood on which `f` coincides with one of them. -/
noncomputable def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ S : Finset (AffineMap n 1),
          ∀ x : Fin n → ℝ, ∃ T ∈ S, ∃ U ∈ nhds x, ∀ y ∈ U, f y = T.eval y 0 }

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from Theorem 2, with `log_3` the real
logarithm to base `3` and `⌈·⌉` the natural-number ceiling of a real number. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent073


namespace Agent074

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

"Better Neural Network Expressivity: Subdividing the Simplex"
(Bakaev, Brunck, Hertrich, Stade, Yehudayoff).

We encode `ℝ^n` concretely as `Fin n → ℝ`.

## Modelling choices

* `ReLU` networks are encoded as an inductive family `ReLUNet a k`, indexed by the input
  dimension `a` and the number `k` of hidden layers. A network with `k` hidden layers is
  either
    - (`k = 0`) a single affine transformation `T : ℝ^a → ℝ^1` (no ReLU at all), or
    - (`k = k' + 1`) an affine transformation `T : ℝ^a → ℝ^m` followed by a componentwise
      `ReLU`, followed by a network with `k'` hidden layers and input dimension `m`.
  This directly mirrors the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ... ∘ ReLU ∘ T^(1)` from the paper, built up recursively from
  the first layer inward.
* `ReLUn n k` is taken to be the set of functions representable with **at most** `k` hidden
  layers (not *exactly* `k`). This is the standard convention (and the one under which
  `ReLUn n k` is monotone in `k`, so `Theorem 2`, an equality of sets at a single value of
  `k`, is even a sensible/true statement): every CPWL function needs *at most* the stated
  number of hidden layers, and conversely every function representable with at most that
  many hidden layers is CPWL.
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* cover of `ℝ^n` by
  polyhedra (each cut out by finitely many affine inequalities) on each of which `f` agrees
  with *some* affine function. This is a genuine piecewise-linearity condition (finite
  polyhedral subdivision + local affineness) and is not defined via representability by a
  ReLU network, nor via a max-of-affine-functions normal form.
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded using the real logarithm `Real.logb 3` and
  `Nat.ceil`, matching the paper's real-valued ceiling of a real logarithm.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias vector. -/
structure AffineTransform (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  bias : Fin b → ℝ

/-- The function computed by an affine transformation: `x ↦ A * x + bias`. -/
def AffineTransform.toFun {a b : ℕ} (T : AffineTransform a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.bias

/-- A ReLU network with input dimension `a` and `k` hidden layers, encoded recursively as
the alternating composition of affine transformations and componentwise ReLU, ending in a
single affine transformation to the scalar output. -/
inductive ReLUNet : ℕ → ℕ → Type
  | output {a : ℕ} (T : AffineTransform a 1) : ReLUNet a 0
  | layer {a m k : ℕ} (T : AffineTransform a m) (rest : ReLUNet m k) : ReLUNet a (k + 1)

/-- The real-valued function `ℝ^a → ℝ` computed by a ReLU network. -/
def ReLUNet.eval : {a k : ℕ} → ReLUNet a k → (Fin a → ℝ) → ℝ
  | _, _, ReLUNet.output T, x => T.toFun x 0
  | _, _, ReLUNet.layer T rest, x => rest.eval (reluVec (T.toFun x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, ∃ net : ReLUNet n k', f = net.eval }

/-- `f : ℝ^n → ℝ` is an affine function, given concretely by a linear functional (as a
dot product with a vector) plus a constant. -/
def IsAffineFun (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (c : ℝ), ∀ x, f x = c + ∑ j, a j * x j

/-- A polyhedron in `ℝ^n`: a set cut out by finitely many affine inequalities. -/
def IsPolyhedron (n : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (a : ι → Fin n → ℝ) (b : ι → ℝ),
    S = { x | ∀ i, ∑ j, a i j * x j ≤ b i }

/-- `CPWL n`: continuous functions `ℝ^n → ℝ` that are affine on each piece of some finite
polyhedral subdivision of `ℝ^n`. This is a genuine piecewise-linearity condition, not a
max-of-affine normal form and not "representable by a ReLU network". -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
      ∃ (ι : Type) (_ : Fintype ι) (P : ι → Set (Fin n → ℝ)),
        (∀ i, IsPolyhedron n (P i)) ∧
        (⋃ i, P i) = Set.univ ∧
        ∀ i, ∃ g, IsAffineFun n g ∧ Set.EqOn f g (P i) }

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from the paper, as a natural number. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent074


namespace Agent075

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

"Better Neural Network Expressivity: Subdividing the Simplex"
(Bakaev, Brunck, Hertrich, Stade, Yehudayoff)

Theorem 2. For n ≥ 3, CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}.

## Modelling choices

* Vectors `ℝ^n` are encoded as `Fin n → ℝ`.
* Affine transformations `ℝ^a → ℝ^b` are encoded concretely and explicitly as a weight
  matrix `Fin b → Fin a → ℝ` together with a bias vector `Fin b → ℝ`, applied as
  `x ↦ A * x + c`.
* A ReLU network with exactly `k` hidden layers and input dimension `a` is encoded as an
  inductive type `ReLUNet a k`: either a single final affine map `a → 1` (the case `k = 0`,
  i.e. depth 1, no hidden layers), or an affine map `a → b` followed by `ReLU`, followed by
  a network with `k` hidden layers and input dimension `b` (the case `k + 1` hidden
  layers). This directly mirrors the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ... ∘ ReLU ∘ T^(1)` from the paper, with the intermediate
  widths existentially quantified inside the inductive constructor.
* `ReLUn n k` is read as *exactly* `k` hidden layers (not "at most"): a function is in
  `ReLUn n k` iff it is computed by *some* `ReLUNet n k`, and `k` is baked into the type of
  `ReLUNet`. This is the literal reading of `ReLU_{n,k}` in the paper. It does not lose
  generality relative to an "at most k" reading: any network with fewer hidden layers can be
  padded out to exactly `k` hidden layers by inserting extra affine "identity" layers of the
  form `x ↦ ReLU(x) - ReLU(-x)` type tricks realized via two extra ReLU layers, so the two
  readings describe the same sets of functions; we simply commit to the exact-`k` reading
  since it is the more literal transcription of the paper's notation.
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of affine
  functions `g_1, ..., g_m : ℝ^n → ℝ` such that every point `x` has a neighborhood on which
  `f` coincides with (at least) one of the `g_i`. This is a genuine local
  piecewise-linearity condition (finitely many affine "pieces", covering neighborhoods of
  every point) and is *not* defined as "representable by a ReLU network" nor as a max/min of
  affine functions, so Theorem 2 is a nontrivial statement about this definition.
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded using the real logarithm `Real.logb 3` and
  `Nat.ceil` (`⌈·⌉₊`), which for `n ≥ 3` (so `n - 1 ≥ 2 > 0`) coincides with the intended
  ceiling of the real number `log_3(n-1)`.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector in `ℝ^n` (encoded as `Fin n → ℝ`). -/
def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a weight matrix and a bias
vector: `x ↦ A * x + c`. -/
structure AffineTransform (a b : ℕ) where
  weight : Fin b → Fin a → ℝ
  bias : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def AffineTransform.eval {a b : ℕ} (T : AffineTransform a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun j => (∑ i, T.weight j i * x i) + T.bias j

/-- A ReLU network with input dimension `a` and *exactly* `k` hidden layers, computing a
real-valued (output dimension 1) function. `ReLUNet a 0` is a single affine map `a → 1`
(depth 1, zero hidden layers). `ReLUNet a (k+1)` is an affine map `a → b` (for some
intermediate width `b`), followed implicitly by a `ReLU`, followed by a network with `k`
hidden layers on input dimension `b`. This directly mirrors
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ... ∘ ReLU ∘ T^(1)`. -/
inductive ReLUNet : ℕ → ℕ → Type where
  | last {a : ℕ} (T : AffineTransform a 1) : ReLUNet a 0
  | cons {a b k : ℕ} (T : AffineTransform a b) (rest : ReLUNet b k) : ReLUNet a (k + 1)

/-- The function `ℝ^a → ℝ` computed by a ReLU network. -/
def ReLUNet.eval : {a k : ℕ} → ReLUNet a k → (Fin a → ℝ) → ℝ
  | _, _, .last T, x => T.eval x 0
  | _, _, .cons T rest, x => rest.eval (reluVec (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
input dimension `n` and *exactly* `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ net : ReLUNet n k, ∀ x, f x = net.eval x }

/-- A function `ℝ^n → ℝ` is affine if it has the form `x ↦ ⟨w, x⟩ + b`. -/
def IsAffineFn {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (w : Fin n → ℝ) (b : ℝ), ∀ x, f x = (∑ i, w i * x i) + b

/-- `CPWL n` is the set of continuous piecewise-linear functions `ℝ^n → ℝ`: those that are
continuous and locally agree, on a neighborhood of every point, with one of finitely many
affine functions. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ),
          (∀ i, IsAffineFn (g i)) ∧
          ∀ x : Fin n → ℝ, ∃ i, ∃ U ∈ nhds x, Set.EqOn f (g i) U }

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from Theorem 2. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent075


namespace Agent076

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We encode `ℝ^n` as `Fin n → ℝ`.  A ReLU network with `k` hidden layers is modelled
*recursively*: a network with `0` hidden layers is a single affine map `ℝ^n → ℝ`
(the last affine transformation `T^(k+1)`); a network with `k+1` hidden layers first
applies an affine map `T : ℝ^n → ℝ^m` to some (existentially chosen) hidden width `m`,
then componentwise ReLU, and then feeds the result into a network with `k` hidden
layers.  This directly mirrors the alternating composition

    T^(k+1) ∘ ReLU ∘ T^(k) ∘ ... ∘ ReLU ∘ T^(1)

from the paper, without needing to fix the hidden widths `n_1, ..., n_k` in advance:
they are existentially quantified at each layer, matching "some ReLU network with
k hidden layers" rather than a network of a fixed prescribed shape.

We read `ReLU_{n,k}` as "representable with **at most** `k` hidden layers" (the
standard convention: adding layers can never hurt, since ReLU networks can implement
the identity on an extra hidden layer via `x = ReLU(x) - ReLU(-x)`; this is also the
reading under which Theorem 2, an *equality* of sets, is the correct statement).
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ :=
  fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely as `x ↦ A *ᵥ x + c`
for a matrix `A` and a translation vector `c`. -/
def IsAffineMap {a b : ℕ} (T : (Fin a → ℝ) → (Fin b → ℝ)) : Prop :=
  ∃ (A : Matrix (Fin b) (Fin a) ℝ) (c : Fin b → ℝ), ∀ x, T x = A.mulVec x + c

/-- A scalar-valued affine function `ℝ^n → ℝ`, i.e. `x ↦ c + Σᵢ aᵢ xᵢ`. -/
def IsAffineScalar {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (c : ℝ), ∀ x, f x = c + ∑ i, a i * x i

/-- `f : ℝ^n → ℝ` is computed by *some* ReLU network with exactly `k` hidden layers:
recursively, `k = 0` means `f` itself is the final affine map `T^(k+1)`, and
`k = k' + 1` means `f` is obtained by first applying an affine map into some hidden
width `m`, then ReLU, then a network with `k'` hidden layers. -/
def ComputesWithHiddenLayers : ℕ → (n : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | 0, n, f => IsAffineScalar (n := n) f
  | (k' + 1), n, f =>
      ∃ (m : ℕ) (T : (Fin n → ℝ) → (Fin m → ℝ)) (g : (Fin m → ℝ) → ℝ),
        IsAffineMap T ∧ ComputesWithHiddenLayers k' m g ∧ ∀ x, f x = g (reluVec (T x))

/-- `ReLUn n k` : the CPWL functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, ComputesWithHiddenLayers k' n f}

/-- `f : ℝ^n → ℝ` is continuous piecewise linear: it is continuous, and there is a
*finite* family of affine functions such that `f` agrees with (at least) one of them
on a neighborhood of every point. This is a genuine local piecewise-linearity
condition (a finite polyhedral-type subdivision witness), not a "max of affine"
normal form and not a restatement of ReLU-representability. -/
def IsCPWL (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  Continuous f ∧
    ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ),
      (∀ i, IsAffineScalar (n := n) (g i)) ∧
      ∀ x : Fin n → ℝ, ∃ i : Fin m, f =ᶠ[nhds x] g i

/-- `CPWL n` : the set of continuous piecewise linear functions `ℝ^n → ℝ`. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | IsCPWL n f}

/-- The depth bound `⌈log_3 (n − 1)⌉ + 1` from the paper, as a natural number,
using the real logarithm `Real.logb 3` and `Nat.ceil`. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n−1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent076


namespace Agent077

/- ================================================================
   Vector encoding: we use `Fin n → ℝ` for ℝ^n throughout.
   ================================================================ -/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m = Fin m → ℝ`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/- ================================================================
   Affine transformations `ℝ^a → ℝ^b`, given concretely by a matrix
   and a bias vector: `x ↦ A * x + c`.
   ================================================================ -/

/-- An affine transformation `ℝ^a → ℝ^b`, given by a matrix `A` and a bias `c`. -/
structure Affine (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def Affine.eval {a b : ℕ} (T : Affine a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/- ================================================================
   ReLU networks.

   A ReLU network with `k` hidden layers computes
     T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)
   i.e. `k` hidden layers means `k + 1` affine transformations in total,
   with a ReLU applied after each of the first `k` of them, and none
   after the last (output) transformation, matching the paper's
   definition of a ReLU network of "depth k+1".

   We define `Computes n k f` by recursion on `k`, peeling off the
   first affine map (and its following ReLU) at each step; the base
   case `k = 0` is a single affine map with no ReLU at all (matching
   depth `0 + 1 = 1`).
   ================================================================ -/

/-- `Computes n k f` means `f : ℝ^n → ℝ` is computed by a ReLU network with
`k` hidden layers, i.e. by `k + 1` affine transformations, alternating with
ReLU applied after each of the first `k` of them. -/
def Computes : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : Affine n 1, ∀ x, f x = T.eval x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T1 : Affine n m) (g : (Fin m → ℝ) → ℝ),
        Computes m k g ∧ ∀ x, f x = g (reluVec (T1.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU
network with **at most** `k` hidden layers. (We use "at most" rather than
"exactly": a network with `k'` hidden layers can always be padded, by
inserting trivial affine identity layers, to a network with any `k ≥ k'`
hidden layers computing the same function, so "at most k" is the reading
under which `ReLU_{n,k}` forms an increasing family in `k` and Theorem 2,
identifying `CPWL_n` with a single specific depth, can hold as a genuine
set equality.) -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, Computes n k' f}

/- ================================================================
   CPWL functions.

   `f : ℝ^n → ℝ` is CPWL if it is continuous and there is a *finite*
   family of affine functions such that every point of `ℝ^n` has a
   neighborhood on which `f` coincides with one member of the family.
   This is a genuine finite-piecewise-affine condition (a finite atlas
   of local affine pieces), not a "max of affine functions" normal form
   and not a "representable by some ReLU network" definition.
   ================================================================ -/

/-- An affine function `ℝ^a → ℝ`, given concretely by its linear part and bias. -/
def IsAffineMap {a : ℕ} (g : (Fin a → ℝ) → ℝ) : Prop :=
  ∃ (w : Fin a → ℝ) (b : ℝ), ∀ x, g x = (∑ i, w i * x i) + b

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`:
those that are continuous and locally agree with one of finitely many affine
functions around every point. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
        ∃ (m : ℕ) (g : Fin m → ((Fin n → ℝ) → ℝ)),
          (∀ i, IsAffineMap (g i)) ∧
          ∀ x : Fin n → ℝ, ∃ i, ∃ ε > 0, ∀ y, dist y x < ε → f y = g i y}

/- ================================================================
   The depth bound ⌈log₃(n - 1)⌉ + 1, using the real logarithm and
   `Nat.ceil`.
   ================================================================ -/

/-- The depth bound `⌈log₃(n - 1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so that
`(n : ℝ) - 1 ≥ 2 > 0` and the real logarithm behaves as expected). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/- ================================================================
   Theorem 2.
   ================================================================ -/

theorem theorem2 : ∀ n : ℕ, n ≥ 3 → CPWL n = ReLUn n (depthBound n) := sorry

end Agent077


namespace Agent078

/-
Design choices (see summary at the end of the task for a short recap):

* Vectors `ℝ^n` are modelled as `Fin n → ℝ`.
* Because a ReLU network's hidden layers can have arbitrary, layer-dependent widths, and
  Lean's dependent `Fin (width i) → ℝ` types make composing a *variable-length* sequence of
  layers with matching types annoying, we represent the values flowing through the network
  (inputs, hidden activations, outputs) uniformly as functions `ℕ → ℝ` ("infinite sequences",
  only finitely many coordinates of which are ever "active" for a given layer). The `width`
  field of a network records, for each layer, how many of these coordinates are meaningful;
  matrices/biases are like`wise indexed by natural numbers. This is purely a bookkeeping
  device to avoid dependent-type casts; mathematically it is the same notion of a ReLU
  network with layer widths `n = n_0, n_1, ..., n_k, n_{k+1} = 1`.
* `ReLUn n k` is defined as *at most* `k` hidden layers (there exists `k' ≤ k` and a network
  with exactly `k'` hidden layers computing `f`). This is the standard convention in the
  depth-separation literature, and it is the reading under which `ReLUn n k` is monotone in
  `k` (a `k`-hidden-layer network can always be padded to `k+1` hidden layers, e.g. using the
  identity `x = ReLU(x) - ReLU(-x)`), matching the "every CPWL function can be represented
  with ... hidden layers" phrasing used for Theorem 1's corollary and Theorem 2 itself.
* `CPWL n` is defined honestly as: `f` is continuous, and there is a *finite* family of
  genuinely affine functions `g_1, ..., g_m : ℝ^n → ℝ` such that every point `x` has a
  neighbourhood on which `f` coincides with one of the `g_i`. This is a standard, non-trivial
  characterization of continuous piecewise-linear functions; it does not mention ReLU
  networks and is not a max-of-affine normal form.
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded using `Real.logb 3` and `Nat.ceil` (`⌈·⌉₊`).
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise (vector) application of ReLU, for any index type `ι`. -/
def reluVec {ι : Type*} (x : ι → ℝ) : ι → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given explicitly by a matrix `A` and a bias `c`,
as `x ↦ A * x + c`. This is the canonical shape of the affine maps `T^{(i)}` in a ReLU
network. -/
def affineMap {a b : ℕ} (A : Fin b → Fin a → ℝ) (c : Fin b → ℝ) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun j => (∑ i, A j i * x i) + c j

/-- A ReLU network with input dimension `n` and `k` hidden layers, i.e. `k + 1` affine
transformations `T^{(1)}, ..., T^{(k+1)}` with layer widths `width 0 = n`, `width (k+1) = 1`.
Layer values (input, hidden activations, output) are represented as functions `ℕ → ℝ`, with
`width i` recording how many leading coordinates are meaningful at layer `i`; the matrix
`A i` and bias `b i` describe the affine map `T^{(i+1)} : ℝ^{width i} → ℝ^{width (i+1)}`. -/
structure ReLUNetwork (n k : ℕ) where
  width : ℕ → ℕ
  width_zero : width 0 = n
  width_last : width (k + 1) = 1
  A : ℕ → ℕ → ℕ → ℝ
  b : ℕ → ℕ → ℝ

/-- Apply the `i`-th affine transformation `T^{(i+1)}` of a `ReLUNetwork`, from the
`width i`-many active coordinates of `x` to the `width (i+1)`-many coordinates of the
output. -/
def ReLUNetwork.layerMap {n k : ℕ} (net : ReLUNetwork n k) (i : ℕ) (x : ℕ → ℝ) : ℕ → ℝ :=
  fun j => (∑ l ∈ Finset.range (net.width i), net.A i j l * x l) + net.b i j

/-- The value at every hidden layer / output of a `ReLUNetwork`, obtained by alternately
applying the affine transformations `T^{(1)}, ..., T^{(k+1)}` and componentwise ReLU, as in
`T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ... ∘ ReLU ∘ T^{(1)}`. ReLU is applied after every affine
transformation except the last one (`T^{(k+1)}`, i.e. layer index `k`). `netForward net m`
is the state of the network after applying the first `m` affine transformations (and the
ReLUs interleaved with them). -/
def ReLUNetwork.netForward {n k : ℕ} (net : ReLUNetwork n k) : ℕ → (ℕ → ℝ) → (ℕ → ℝ)
  | 0, x => x
  | m + 1, x =>
      let pre := net.layerMap m (net.netForward m x)
      if m + 1 = k + 1 then pre else reluVec pre

/-- Embed a vector `Fin n → ℝ` as a sequence `ℕ → ℝ`, zero outside the first `n`
coordinates. -/
def toSeq {n : ℕ} (x : Fin n → ℝ) : ℕ → ℝ :=
  fun i => if h : i < n then x ⟨i, h⟩ else 0

/-- A `ReLUNetwork` *computes* / *represents* a function `f : ℝ^n → ℝ` if feeding it any
input `x` and reading off the single output coordinate (coordinate `0` of the width-1 final
layer) yields `f x`. -/
def ReLUNetwork.Computes {n k : ℕ} (net : ReLUNetwork n k) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x : Fin n → ℝ, f x = net.netForward (k + 1) (toSeq x) 0

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with *at
most* `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, ∃ net : ReLUNetwork n k', net.Computes f }

/-- A function `ℝ^n → ℝ` is (genuinely) affine if it has the form `x ↦ a ⬝ x + c`. -/
def IsAffine (n : ℕ) (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (c : ℝ), ∀ x : Fin n → ℝ, g x = (∑ i, a i * x i) + c

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: those that are
continuous and admit a *finite* family of affine functions such that every point has a
neighbourhood on which `f` agrees with one member of the family. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ),
          (∀ i, IsAffine n (g i)) ∧
          ∀ x : Fin n → ℝ, ∃ i, ∀ᶠ y in nhds x, f y = g i y }

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from Theorem 2. -/
def depthBound (n : ℕ) : ℕ := ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent078


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


namespace Agent080

/-!
# Theorem 2 of arXiv:2505.14338 (Bakaev–Brunck–Hertrich–Stade–Yehudayoff)

We formalize the *statement* of Theorem 2:

  For n ≥ 3,  CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}.

## Modelling choices

* Vectors `ℝ^m` are encoded as `Fin m → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is encoded concretely and explicitly as a matrix
  `A : Fin b → Fin a → ℝ` together with a bias vector `c : Fin b → ℝ`, evaluated as
  `x ↦ A * x + c` (written out with `Finset.sum`), see `AffineMap` / `AffineMap.eval`.
* `relu` is `max 0 ·` on `ℝ`, and `reluVec` applies it componentwise.
* A ReLU network with `k` hidden layers computing `f : ℝ^n → ℝ` is modelled by the
  recursively-peeled proposition `IsReLUComputable n k f`: peeling off the first affine
  map `T^{(1)} : ℝ^n → ℝ^m` and the first ReLU leaves a function `g` on `ℝ^m` that is
  itself computable with `k - 1` hidden layers; the base case `k = 0` is a single affine
  map `ℝ^n → ℝ^1` (i.e. `T^{(k+1)}` with no ReLU applied after it), matching the
  alternating composition `T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}` from the paper.
  We take `ReLU_{n,k}` to mean functions representable with **exactly** `k` hidden
  layers (the literal reading of "representable with k hidden layers" in Section 1 of the
  paper), rather than "at most k".
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of affine
  functions `ℝ^n → ℝ` such that every point `x` has a neighbourhood on which `f` agrees
  with one of these affine functions (a genuine local-piecewise-linearity condition, not
  a max-of-affine normal form and not "representable by a ReLU network").
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined via the real logarithm `Real.logb 3` and
  `Nat.ceil`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix `A` (as a function
`Fin b → Fin a → ℝ`) and a bias vector `c : Fin b → ℝ`, computing `x ↦ A * x + c`. -/
structure AffineMap (a b : ℕ) where
  A : Fin b → Fin a → ℝ
  c : Fin b → ℝ

/-- Evaluation of an `AffineMap` at a point. -/
def AffineMap.eval {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun j => (∑ i, T.A j i * x i) + T.c j

/-- `IsReLUComputable n k f` says that `f : ℝ^n → ℝ` is computed by a ReLU network with
exactly `k` hidden layers, i.e. `f = T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}` for
some affine maps `T^{(1)}, …, T^{(k+1)}` of matching (but otherwise arbitrary) intermediate
widths. We peel off the first affine map and the first ReLU at each recursive step. -/
def IsReLUComputable : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : AffineMap n 1, f = fun x => T.eval x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : AffineMap n m) (g : (Fin m → ℝ) → ℝ),
        IsReLUComputable m k g ∧ f = fun x => g (reluVec (T.eval x))

/-- `ReLUn n k`, the set of functions `ℝ^n → ℝ` representable by a ReLU network with
exactly `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) := {f | IsReLUComputable n k f}

/-- An affine function `ℝ^n → ℝ`, expressed via an `AffineMap n 1`. -/
def IsAffineFun (n : ℕ) (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ T : AffineMap n 1, g = fun x => T.eval x 0

/-- `CPWL n`, the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: `f` is
continuous, and there is a finite family of affine functions such that every point has a
neighbourhood on which `f` coincides with one of them. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (ι : Type) (_ : Fintype ι) (g : ι → (Fin n → ℝ) → ℝ),
      (∀ i, IsAffineFun n (g i)) ∧ ∀ x : Fin n → ℝ, ∃ i, f =ᶠ[nhds x] g i}

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so `n - 1 ≥ 2 > 0`). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent080


namespace Agent081

/-!
# Theorem 2 of arXiv:2505.14338 (Bakaev–Brunck–Hertrich–Stade–Yehudayoff)

We formalize the *statement* of Theorem 2: for `n ≥ 3`,
`CPWL n = ReLUn n (⌈log_3 (n - 1)⌉ + 1)`.

## Modelling choices

* Vectors in `ℝ^n` are encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is encoded concretely as a pair `(A, c)` with
  `A : Matrix (Fin b) (Fin a) ℝ` and `c : Fin b → ℝ`, acting by `x ↦ A.mulVec x + c`.
* A ReLU network with `k` hidden layers computing `f : (Fin n → ℝ) → ℝ` is encoded
  *recursively* on `k`: with `0` hidden layers, `f` itself must be an affine map
  `ℝ^n → ℝ`; with `k + 1` hidden layers, there is some hidden width `m`, an affine map
  `T : ℝ^n → ℝ^m`, and a function `g : ℝ^m → ℝ` computed by a network with `k` hidden
  layers, such that `f x = g (relu (T x))`. This directly mirrors the alternating
  composition `T^(k+1) ∘ ReLU ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper, with `k + 1` affine
  transformations total.
* `ReLUn n k` is read as *at most* `k` hidden layers (functions representable with some
  `k' ≤ k` hidden layers). This is the reading under which the depth-hierarchy statement
  `CPWL_n = ReLU_{n,d(n)}` is the natural one: the paper's informal restatement says
  "every CPWL function ... can be represented with `⌈log_3(n-1)⌉+1` hidden layers", i.e.
  that many hidden layers *suffice*, which is exactly the "at most k" reading. (Under an
  "exactly k" reading the statement would additionally need every CPWL function to
  require *at least* that many layers, which is not claimed.)
* `CPWL n` is defined mathematically as: `f` is continuous, and there is a *finite*
  cover of `ℝ^n` by closed halfspace-polyhedra on each of which `f` agrees with some
  affine function. This is a genuine piecewise-linearity condition, independent of the
  notion of ReLU-representability, and not phrased as a max-of-affine normal form.
* The depth bound `⌈log_3 (n-1)⌉ + 1` is encoded with the real logarithm `Real.logb 3`
  and `Nat.ceil`.
-/

/-- `relu` on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^n`. -/
def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a
translation vector, acting as `x ↦ A * x + c`. -/
structure Affine (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def Affine.eval {a b : ℕ} (T : Affine a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `NetworkComputes n k f` means `f : ℝ^n → ℝ` is computed by *some* ReLU network with
exactly `k` hidden layers, i.e. by an alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations with
componentwise ReLU applied after each of the first `k` of them. We define this by
recursion on `k`: with `0` hidden layers `f` is itself an affine map (just `T^(1)`);
with `k + 1` hidden layers, the first affine map `T^(1) : ℝ^n → ℝ^m` (for some hidden
width `m`) followed by `ReLU` feeds into a network with `k` hidden layers computing the
rest (`T^(2), …, T^(k+2)`). -/
def NetworkComputes : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : Affine n 1, ∀ x, f x = T.eval x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : Affine n m) (g : (Fin m → ℝ) → ℝ),
        NetworkComputes m k g ∧ ∀ x, f x = g (reluVec (T.eval x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers (see the discussion above for why "at most" is the reading
that makes Theorem 2 true). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, NetworkComputes n k' f}

/-- A subset of `ℝ^n` cut out by finitely many affine (non-strict) inequalities, i.e. a
closed halfspace-polyhedron. -/
def IsHalfspacePolyhedron {n : ℕ} (P : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (a : Fin m → Fin n → ℝ) (b : Fin m → ℝ),
    P = {x | ∀ j, ∑ i, a j i * x i ≤ b j}

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: those that
are continuous and admit a finite cover of `ℝ^n` by closed halfspace-polyhedra, on each
of which the function agrees with some affine function. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (P : Fin m → Set (Fin n → ℝ)) (g : Fin m → Affine n 1),
      (⋃ i, P i) = Set.univ ∧
      (∀ i, IsHalfspacePolyhedron (P i)) ∧
      ∀ i, ∀ x ∈ P i, f x = (g i).eval x 0}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so `n - 1 ≥ 2`). -/
def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉+1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent081


namespace Agent082

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We work with `ℝ^n` encoded as `Fin n → ℝ`.

## Modelling choices (see summary at call site)

* `ReLUn n k` is defined as functions representable by a ReLU network with **at most** `k`
  hidden layers (`∃ k' ≤ k, NetComputes n k' f`), not *exactly* `k`. This is the standard
  reading in the literature: since one can always pad a network with extra layers that act
  as the identity (e.g. via `x ↦ relu x - relu (-x)` recombinations), the class of
  representable functions is monotone increasing in the number of hidden layers, and
  Theorem 2 is naturally stated about the smallest depth that suffices for *all* of
  `CPWL_n`, which forces monotonicity for the equality to be meaningful.
* `NetComputes n k f` is defined by recursion on `k`, peeling off the *first* affine map and
  ReLU at each step, directly mirroring the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper.
* Affine transformations `ℝ^a → ℝ^b` are modelled concretely as a matrix-vector pair
  `(A, c)` with `A : Matrix (Fin b) (Fin a) ℝ`, `c : Fin b → ℝ`, acting by
  `x ↦ A.mulVec x + c`.
* `CPWL n` is defined as: `f` is continuous **and** there is a finite family of affine
  functions such that `f` locally agrees with (at least) one of them in a neighbourhood of
  every point. This is a genuine piecewise-linearity condition (a finite family of affine
  "pieces" covering `ℝ^n` via local agreement), not a max-of-affine normal form and not
  "representable by some ReLU network".
* The depth bound `⌈log_3 (n-1)⌉ + 1` is encoded using `Real.logb 3` and `Nat.ceil`.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (v : Fin m → ℝ) : Fin m → ℝ := fun i => relu (v i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely as `x ↦ A * x + c`. -/
structure AffineMap' (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def AffineMap'.eval {a b : ℕ} (T : AffineMap' a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/--
`NetComputes n k f` means `f : ℝ^n → ℝ` is computed by a ReLU network with exactly `k`
hidden layers, i.e. `f` is the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations with
componentwise ReLU applications, for some choice of hidden layer widths.

Defined by recursion on `k`, peeling off the first affine map `T^(1) : ℝ^n → ℝ^m` and the
following ReLU at each step; the base case `k = 0` is a single affine map `ℝ^n → ℝ`
(no ReLUs, i.e. `T^(1)` alone).
-/
def NetComputes : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : AffineMap' n 1, ∀ x, f x = T.eval x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : AffineMap' n m) (g : (Fin m → ℝ) → ℝ),
        NetComputes m k g ∧ ∀ x, f x = g (reluVec (T.eval x))

/--
`ReLUn n k`, the set of functions `ℝ^n → ℝ` representable by a ReLU network with **at most**
`k` hidden layers.
-/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, NetComputes n k' f }

/-- An affine function `ℝ^n → ℝ`, i.e. `x ↦ ⟨a, x⟩ + b`. -/
def IsAffineFun {n : ℕ} (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x, g x = (∑ i, a i * x i) + b

/--
`CPWL n`, the set of continuous piecewise linear functions `ℝ^n → ℝ`: `f` is continuous, and
there is a finite family of affine functions such that every point has a neighbourhood on
which `f` agrees with (at least) one member of the family.
-/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
      ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ),
        (∀ j, IsAffineFun (g j)) ∧
        ∀ x : Fin n → ℝ, ∃ j, ∃ U ∈ nhds x, ∀ y ∈ U, f y = g j y }

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent082


namespace Agent083

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We encode `ℝ^n` concretely as `Fin n → ℝ`.

## Modelling choices (see summary at the end of the task for more detail)

* Vectors: `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is given by a matrix `A : Matrix (Fin b) (Fin a) ℝ`
  together with a bias vector `c : Fin b → ℝ`, applied as `x ↦ A.mulVec x + c`.
* A ReLU network with `k` hidden layers and input dimension `n` is modelled by the inductive
  family `ReLUNet n k`, which is literally the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper: the base case `output` is a single
  affine map `ℝ^n → ℝ^1` (0 hidden layers), and `layer` prepends one affine map followed by a
  `ReLU`, increasing the hidden-layer count by one. The hidden widths `n_1, …, n_k` are existentially
  quantified (arbitrary natural numbers), matching the informal definition.
* `ReLUn n k` is the set of functions representable with **at most** `k` hidden layers (i.e. by
  some `ReLUNet n j` with `j ≤ k`). This is the reading that makes Theorem 2 a faithful
  "sufficiency + necessity of depth `⌈log_3(n-1)⌉+1`" statement: `ReLUn n k` is monotone in `k`
  by construction, matching the standard convention in the depth-separation literature (a
  network realizable with fewer hidden layers is certainly realizable with at most `k` for any
  larger `k`, since the definition itself quantifies over `j ≤ k`).
* `CPWL n` requires continuity together with a genuine finite polyhedral-type subdivision: a
  finite family of convex, closed pieces covering `ℝ^n` on each of which `f` agrees with some
  affine function.
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined using `Real.logb 3` and `Nat.ceil` (`⌈·⌉₊`)
  applied to the real number `(n : ℝ) - 1`.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias vector. -/
structure AffineTransform (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- The function `ℝ^a → ℝ^b` computed by an affine transformation: `x ↦ A * x + c`. -/
def AffineTransform.apply {a b : ℕ} (T : AffineTransform a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- A ReLU network with input dimension `n` and exactly `k` hidden layers, modelled as the
literal alternating composition `T^(k+1) ∘ ReLU ∘ ⋯ ∘ ReLU ∘ T^(1)`.
The hidden widths are existentially present as the (arbitrary) indices `m` occurring in `layer`. -/
inductive ReLUNet : ℕ → ℕ → Type where
  /-- `k = 0` hidden layers: a single affine map `ℝ^n → ℝ^1` (no ReLU applied). -/
  | output {n : ℕ} (T : AffineTransform n 1) : ReLUNet n 0
  /-- Prepend one affine map `ℝ^n → ℝ^m` followed by a ReLU, then continue with a network
  that has `k` further hidden layers and input dimension `m`. -/
  | layer {n m k : ℕ} (T : AffineTransform n m) (rest : ReLUNet m k) : ReLUNet n (k + 1)

/-- The function `ℝ^n → ℝ` computed by a ReLU network, i.e.
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`. -/
def ReLUNet.eval {n k : ℕ} (net : ReLUNet n k) (x : Fin n → ℝ) : ℝ :=
  match net with
  | ReLUNet.output T => T.apply x 0
  | ReLUNet.layer T rest => rest.eval (reluVec (T.apply x))

/-- A function is representable with *exactly* `k` hidden layers if it is computed by some
`ReLUNet n k`. -/
def IsRepresentableExact (n k : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ net : ReLUNet n k, ∀ x, f x = net.eval x

/-- `ReLUn n k`: the set of functions `ℝ^n → ℝ` representable with **at most** `k` hidden
layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ j ≤ k, IsRepresentableExact n j f}

/-- A function `ℝ^n → ℝ` is affine if it has the form `x ↦ ⟨a, x⟩ + b`. -/
def IsAffineMap (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x, f x = (∑ i, a i * x i) + b

/-- `CPWL n`: continuous functions `ℝ^n → ℝ` that admit a finite subdivision of `ℝ^n` into
convex, closed pieces covering all of `ℝ^n`, on each of which `f` agrees with an affine
function. This is a genuine piecewise-linearity condition (a finite polyhedral-type
subdivision), not a "representable by some ReLU network" or "max of affine functions"
definition. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (pieces : Fin m → Set (Fin n → ℝ)) (affines : Fin m → ((Fin n → ℝ) → ℝ)),
      (∀ i, IsAffineMap n (affines i)) ∧
      (∀ i, Convex ℝ (pieces i)) ∧
      (∀ i, IsClosed (pieces i)) ∧
      (⋃ i, pieces i) = Set.univ ∧
      (∀ i, ∀ x ∈ pieces i, f x = affines i x)}

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so `n - 1 ≥ 2` as a real
number). -/
def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL n = ReLUn n (⌈log_3(n-1)⌉ + 1)`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent083


namespace Agent085

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

  "Better Neural Network Expressivity: Subdividing the Simplex"
  (Bakaev, Brunck, Hertrich, Stade, Yehudayoff)

  Theorem 2. For n ≥ 3, CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}.

## Modelling choices

* Vectors `ℝ^m` are encoded as `Fin m → ℝ`.
* Affine maps `ℝ^a → ℝ^b` are given concretely by a matrix `A : Matrix (Fin b) (Fin a) ℝ`
  together with a bias vector `bias : Fin b → ℝ`, acting by `x ↦ A.mulVec x + bias`.
* A ReLU network with `k` hidden layers computing `f : ℝ^n → ℝ` is modelled *recursively*
  on `k`: with `0` hidden layers, `f` itself must be affine (a single affine transformation
  `T^(1)`, matching "depth 1"); with `k+1` hidden layers, `f` factors as
  `f x = g (relu (T x))` where `T : ℝ^n → ℝ^m` is affine, `relu` is applied componentwise,
  and `g : ℝ^m → ℝ` is computed by a network with `k` hidden layers. Unrolling this recursion
  reproduces exactly the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper, with `k+1` affine
  transformations and `k` applications of ReLU.
* `ReLUn n k` is the set of functions computed by *some* network with *exactly* `k` hidden
  layers. Note that (by the standard "ReLU(x) - ReLU(-x) = x" padding trick, not proved
  here) the family `ReLUn n k` is increasing in `k`, so "exactly k" and "at most k" describe
  the *same* set `ReLUn n k`; we use the "exactly k" reading since it is the more direct
  transcription of the recursive definition above.
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of affine
  functions `ℝ^n → ℝ` such that `f` locally (in a neighbourhood of every point) agrees with
  one member of the family. This is the "finite family of affine functions that `f` locally
  agrees with" option suggested by the spec; it is a genuine piecewise-linearity condition,
  not a max-of-affine normal form and not "representable by some ReLU network".
* The depth bound `⌈log_3(n-1)⌉ + 1` is defined via `Real.logb 3` and `Nat.ceil` on the real
  number `(n : ℝ) - 1`.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias vector. -/
structure AffineMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  bias : Fin b → ℝ

/-- The function `ℝ^a → ℝ^b` computed by an affine transformation. -/
def AffineMap.apply {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.bias

/-- `f : ℝ^n → ℝ` is an affine (scalar-valued) function, i.e. computed by a single affine
transformation `ℝ^n → ℝ^1` (identified with `ℝ`). This is the `k = 0` (no hidden layers,
depth 1) base case of a ReLU network. -/
def IsAffine1 (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ w : Fin n → ℝ, ∃ c : ℝ, ∀ x : Fin n → ℝ, f x = (∑ i, w i * x i) + c

/-- `Computes n k f` : the function `f : ℝ^n → ℝ` is computed by a ReLU network with `k`
hidden layers, i.e. by an alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations with
componentwise ReLU. Defined recursively on `k`: the base case `k = 0` is a bare affine
transformation (a single `T^(1)`, no ReLU applied), and the `k + 1` case peels off the first
affine transformation `T^(1) : ℝ^n → ℝ^m`, applies ReLU, and requires the remainder to be
computed by a network with `k` hidden layers on `ℝ^m`. -/
def Computes : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => IsAffine1 n f
  | n, k + 1, f =>
      ∃ (m : ℕ) (T : AffineMap n m) (g : (Fin m → ℝ) → ℝ),
        Computes m k g ∧ ∀ x : Fin n → ℝ, f x = g (reluVec (T.apply x))

/-- `ReLUn n k` : the set of functions `ℝ^n → ℝ` representable by a ReLU network with
(exactly, equivalently at most, by monotonicity in `k`) `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Computes n k f}

/-- `CPWL n` : the continuous piecewise-linear functions `ℝ^n → ℝ`, defined as those
functions that are continuous and locally agree, in a neighbourhood of every point, with
one member of some finite family of affine functions. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (w : Fin m → (Fin n → ℝ)) (c : Fin m → ℝ),
      ∀ x : Fin n → ℝ, ∃ i : Fin m,
        ∀ᶠ y in nhds x, f y = (∑ j, w i j * y j) + c i}

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from Theorem 2, for `n ≥ 3` (so `n - 1 ≥ 2 > 0`). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent085


namespace Agent086

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):

  For n ≥ 3,  CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}.

Modelling choices (see summary at the end of the task report):
  * `ℝ^n` is encoded as `Fin n → ℝ`.
  * Affine transformations `ℝ^a → ℝ^b` are encoded concretely via a matrix `A : Fin b →
    Fin a → ℝ` and bias `c : Fin b → ℝ`, through the predicate `IsAffine`.
  * "Computed by a ReLU network with exactly k hidden layers" is defined recursively via
    `NetComputes`, mirroring the alternating composition
    `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper.
  * `ReLUn n k` is taken to mean *at most* `k` hidden layers (a union over `k' ≤ k` of the
    "exactly `k'`" sets), which is the reading under which Theorem 2 is a true statement
    (and is in any case equivalent to "exactly k, for k large enough" since extra layers
    can always be padded out using `ReLU(x) - ReLU(-x) = x`).
  * `CPWL n` is defined as: continuous, and admitting a finite polyhedral subdivision of
    `ℝ^n` (each piece cut out by finitely many affine inequalities) on each piece of which
    `f` agrees with an affine formula. This is a genuine piecewise-linearity condition, not
    a restatement of ReLU-representability and not a max-of-affine normal form.
  * The depth bound `⌈log_3(n-1)⌉ + 1` is encoded literally using `Real.logb 3` and
    `Nat.ceil`.
-/

/-- The ReLU function on `ℝ`. -/
def reluR (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `reluR` to a vector `ℝ^p`. -/
def reluVec {p : ℕ} (v : Fin p → ℝ) : Fin p → ℝ := fun i => reluR (v i)

/-- `f : ℝ^n → ℝ^m` is an affine transformation, i.e. `f x = A x + c` for some matrix `A`
and bias vector `c`. -/
def IsAffine (n m : ℕ) (f : (Fin n → ℝ) → (Fin m → ℝ)) : Prop :=
  ∃ (A : Fin m → Fin n → ℝ) (c : Fin m → ℝ),
    ∀ (x : Fin n → ℝ) (j : Fin m),
      f x j = Finset.sum Finset.univ (fun i => A j i * x i) + c j

/-- `NetComputes k n m f` means that `f : ℝ^n → ℝ^m` is computed by a ReLU network with
input dimension `n`, output dimension `m`, and *exactly* `k` hidden layers, i.e. `f` is the
alternating composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine
transformations with componentwise ReLU applications in between, as in Section 1 of the
paper. Defined by recursion on `k`. -/
def NetComputes : (k n m : ℕ) → ((Fin n → ℝ) → (Fin m → ℝ)) → Prop
  | 0, n, m, f => IsAffine n m f
  | k + 1, n, m, f =>
      ∃ (h : ℕ) (T : (Fin n → ℝ) → (Fin h → ℝ)) (g : (Fin h → ℝ) → (Fin m → ℝ)),
        IsAffine n h T ∧ NetComputes k h m g ∧ f = fun x => g (reluVec (T x))

/-- The set of functions `ℝ^n → ℝ` representable by a ReLU network with *exactly* `k`
hidden layers. Output dimension is `1`; we read off the single coordinate. -/
def ReLUnExact (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | NetComputes k n 1 (fun x (_ : Fin 1) => f x) }

/-- `ReLUn n k`, the set of functions `ℝ^n → ℝ` representable with *at most* `k` hidden
layers (a network with fewer hidden layers can always be extended to one with more, by
inserting identity layers realized as `ReLU(x) - ReLU(-x) = x`; taking the "at most"
reading is what makes the equality in Theorem 2 correct). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, f ∈ ReLUnExact n k' }

/-- A polyhedral subset of `ℝ^n`: the solution set of finitely many affine inequalities. -/
def IsPolyhedralSet (n : ℕ) (P : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (A : Fin m → Fin n → ℝ) (c : Fin m → ℝ),
    P = { x : Fin n → ℝ | ∀ j, Finset.sum Finset.univ (fun i => A j i * x i) ≤ c j }

/-- `CPWL n`: the continuous, piecewise linear functions `ℝ^n → ℝ`, i.e. those that are
continuous and admit a finite polyhedral subdivision of `ℝ^n` on each piece of which the
function agrees with an affine formula. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (ι : ℕ) (P : Fin ι → Set (Fin n → ℝ)) (A : Fin ι → Fin n → ℝ) (b : Fin ι → ℝ),
          (∀ j, IsPolyhedralSet n (P j)) ∧
          (⋃ j, P j) = Set.univ ∧
          (∀ j, ∀ x ∈ P j, f x = Finset.sum Finset.univ (fun i => A j i * x i) + b j) }

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from Theorem 2, encoded via the real logarithm
`Real.logb 3` and `Nat.ceil`. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉+1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent086


namespace Agent087

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We model `ℝ^n` as `Fin n → ℝ`.  An affine transformation `ℝ^a → ℝ^b` is modelled
concretely as `x ↦ A.mulVec x + b` for a matrix `A : Matrix (Fin b) (Fin a) ℝ` and a
translation vector `b : Fin b → ℝ`.

A ReLU network with `k` hidden layers computing `f : ℝ^n → ℝ` is modelled by the
predicate `Represents n k f`, defined by recursion on `k`:

* `k = 0` : `f` itself is an affine functional `ℝ^n → ℝ` (this is the case of a
  single affine transformation `T^(1)` with no hidden layers at all, matching the
  paper's convention that depth `k+1` with `k` hidden layers).
* `k+1`   : `f` is obtained by first applying an affine transformation
  `x ↦ A.mulVec x + b : ℝ^n → ℝ^m` (this is `T^(1)`), then applying `ReLU`
  componentwise, and then computing the rest of the network (with `k` hidden
  layers, i.e. `T^(2), ..., T^(k+2)` composed with the remaining `ReLU`s) on the
  result.

We read `ReLU_{n,k}` **literally** as "representable by a network with *exactly*
`k` hidden layers" (not "at most `k`"), matching the paper's phrasing "the subset
of `CPWL_n` representable with `k` hidden layers". Note that with this
definition `ReLUn n k` is in fact still monotone in `k` (one can always pad a
network with an extra hidden layer that implements the identity on the split
positive/negative parts of a vector), so this reading does not conflict with
`CPWL n = ReLUn n (⌈log_3 (n-1)⌉ + 1)` being the intended, literal equality of
sets from the paper.

`CPWL n` is defined honestly as: `f` is continuous, and there is a *finite*
family of affine functionals such that `f` locally agrees with (at least) one of
them in a neighbourhood of every point (a genuine finite polyhedral/local
piecewise-affine condition, not "representable by some ReLU network" and not a
max-of-affine normal form).
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of `relu` to a vector in `ℝ^m`. -/
def reluVec {m : ℕ} (v : Fin m → ℝ) : Fin m → ℝ := fun i => relu (v i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a
translation vector: `x ↦ A.mulVec x + b`. -/
def affineMap {a b : ℕ} (A : Matrix (Fin b) (Fin a) ℝ) (c : Fin b → ℝ) :
    (Fin a → ℝ) → (Fin b → ℝ) :=
  fun x => A.mulVec x + c

/-- A scalar-valued function `ℝ^n → ℝ` is affine if it has the form
`x ↦ ⟪c, x⟫ + b` for some vector `c` and scalar `b`. -/
def IsAffine (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (c : Fin n → ℝ) (b : ℝ), f = fun x => (∑ i, c i * x i) + b

/-- `Represents n k f` means `f : ℝ^n → ℝ` is computed by a ReLU network with
exactly `k` hidden layers, i.e. by an alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations
with componentwise `ReLU` in between. -/
def Represents (n : ℕ) : ℕ → ((Fin n → ℝ) → ℝ) → Prop
  | 0, f => IsAffine n f
  | k + 1, f =>
      ∃ (m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ)
        (g : (Fin m → ℝ) → ℝ),
        Represents m k g ∧ f = fun x => g (reluVec (affineMap A c x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU
network with exactly `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Represents n k f}

/-- `CPWL n` is the space of continuous, piecewise-linear functions `ℝ^n → ℝ`:
`f` is continuous and there is a finite family of affine functionals such that
`f` coincides with one of them on a neighbourhood of every point of `ℝ^n`. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
        ∃ (r : ℕ) (a : Fin r → (Fin n → ℝ) → ℝ),
          (∀ i, IsAffine n (a i)) ∧
          ∀ x : Fin n → ℝ, ∃ i, ∀ᶠ y in nhds x, f y = a i y}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from the paper, for `n ≥ 3` (so that
`n - 1 ≥ 2 > 0` and the real logarithm behaves as expected). -/
def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent087


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


namespace Agent089

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

"Better Neural Network Expressivity: Subdividing the Simplex"
(Bakaev, Brunck, Hertrich, Stade, Yehudayoff).

Theorem 2. For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`.

We encode `ℝ^n` as `Fin n → ℝ`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise application of ReLU to a vector in `Fin n → ℝ`. -/
def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias
vector: `x ↦ A * x + b`. -/
def AffineFun (a b : ℕ) := Matrix (Fin b) (Fin a) ℝ × (Fin b → ℝ)

/-- Evaluation of an affine transformation. -/
def AffineFun.eval {a b : ℕ} (T : AffineFun a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.1.mulVec x + T.2

/-- `NNComputesExact n k f` means `f : ℝ^n → ℝ` is computed by a ReLU network with
*exactly* `k` hidden layers, i.e. `f` arises as the alternating composition

    T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)

of `k + 1` affine transformations `T^(1), …, T^(k+1)` with matching intermediate
dimensions `n = n_0, n_1, …, n_k, n_{k+1} = 1`.

The recursion peels off the first affine map `T^(1) : ℝ^n → ℝ^m` together with the
subsequent ReLU, and recurses on the remaining network (with `k` hidden layers,
computing `ℝ^m → ℝ`) that produces the final affine map `T^(k+1)` in its base case. -/
def NNComputesExact : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : AffineFun n 1, ∀ x, f x = T.eval x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : AffineFun n m) (g : (Fin m → ℝ) → ℝ),
        NNComputesExact m k g ∧ ∀ x, f x = g (reluVec (T.eval x))

/-- `ReLUn n k`, the set of functions `ℝ^n → ℝ` representable by a ReLU network with
*at most* `k` hidden layers. We take the "at most" reading (rather than "exactly `k`")
because a network with `j ≤ k` hidden layers can always be padded to have `k` hidden
layers (e.g. by adding trivial extra affine/ReLU layers), so `ReLU_{n,k}` is naturally
increasing in `k`; this is also the reading under which Theorem 2's equality
`CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉+1}` is the correct statement (it must in particular
contain low-complexity functions such as affine functions, which need only `0` hidden
layers). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ j : ℕ, j ≤ k ∧ NNComputesExact n j f}

/-- An affine (degree-`≤ 1` polynomial) function `ℝ^n → ℝ`. -/
def IsAffine (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x, f x = (∑ i, a i * x i) + b

/-- `CPWL n`, the space of continuous piecewise-linear functions `ℝ^n → ℝ`: those `f`
that are continuous and are, locally around every point, equal to one of finitely many
globally-fixed affine functions. This is a genuine piecewise-affine condition (a finite
polyhedral-type subdivision into pieces on which `f` is affine), independent of any
notion of ReLU network. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
       ∃ S : Finset ((Fin n → ℝ) → ℝ),
         (∀ ℓ ∈ S, IsAffine n ℓ) ∧
         ∀ x : Fin n → ℝ, ∃ ℓ ∈ S, ∃ U ∈ nhds x, ∀ y ∈ U, f y = ℓ y}

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from Theorem 2, encoded using the real
logarithm `Real.logb 3` and `Nat.ceil`. -/
def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent089


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


namespace Agent091

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

"Better Neural Network Expressivity: Subdividing the Simplex"
(Bakaev, Brunck, Hertrich, Stade, Yehudayoff)

Theorem 2. For n ≥ 3, we have CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}.

## Modelling choices

* Vectors `ℝ^n` are modelled as `Fin n → ℝ`.
* Affine maps `ℝ^a → ℝ^b` are modelled concretely as a pair `(weights, bias)` with
  `weights : Fin b → Fin a → ℝ` and `bias : Fin b → ℝ`, evaluated as `A * x + b`.
* A ReLU network with `k` hidden layers computing `f : ℝ^n → ℝ` is modelled by
  structural recursion on `k`: with `0` hidden layers it is a single affine map
  `ℝ^n → ℝ`; with `k+1` hidden layers it is an affine map `ℝ^n → ℝ^m` into some
  (existentially quantified) hidden width `m`, followed by componentwise ReLU,
  followed by a network with `k` hidden layers on the result. This literally
  encodes the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper.
* `ReLUn n k` is taken to be the set of functions representable with **at most**
  `k` hidden layers (not exactly `k`). This is the reading that makes the theorem
  true as an equality of sets: `ReLUn n k` is manifestly monotone increasing in
  `k` under this reading, its union over all `k` is exactly `CPWL n` (every CPWL
  function is representable by *some* network), and Theorem 1 provides the
  matching lower/upper bound machinery to pin down exactly the threshold
  `k = ⌈log_3(n-1)⌉ + 1` at which the increasing chain first reaches all of
  `CPWL n`. (Under the "exactly k" reading the same equality can also be argued
  via the standard identity-padding trick `x = ReLU(x) - ReLU(-x)`, but "at most"
  is the more direct and standard reading for this kind of depth-hierarchy
  statement, so we adopt it.)
* `CPWL n` is defined mathematically (not via ReLU networks!) as: `f` is
  continuous, and there is a *finite* collection of pieces, each cut out by a
  finite system of affine (half-space) inequalities, whose union is all of
  `ℝ^n`, such that on each piece `f` agrees with some affine function.  This is
  a genuine finite polyhedral subdivision condition.
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded using `Nat.clog 3 (n - 1) + 1`.
  For `b ≥ 2` and `m ≥ 1`, `Nat.clog b m` is (by Mathlib's characterization,
  `Nat.pow_pred_clog_lt_self` / `Nat.le_pow_clog`) the least `k` with `m ≤ b ^ k`,
  which is exactly `⌈Real.logb b m⌉₊` for `m ≥ 1`, `b ≥ 2`; since `n ≥ 3` we have
  `n - 1 ≥ 2 ≥ 1` so this coincides with the intended real ceiling of `log_3(n-1)`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ :=
  fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a weight matrix
(as a function `Fin b → Fin a → ℝ`) and a bias vector `Fin b → ℝ`. -/
def AffineFun (a b : ℕ) : Type := (Fin b → Fin a → ℝ) × (Fin b → ℝ)

/-- Evaluate an affine transformation: `x ↦ A * x + bias`. -/
def AffineFun.eval {a b : ℕ} (T : AffineFun a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, T.1 i j * x j) + T.2 i

/-- `NetFunc n k f` : the function `f : ℝ^n → ℝ` is *exactly* computed by some ReLU
network with `n` inputs and `k` hidden layers, i.e. `f` is the alternating
composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine
transformations with componentwise ReLU, where all intermediate widths `n_1, …, n_k`
are existentially quantified natural numbers. -/
def NetFunc : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : AffineFun n 1, ∀ x, f x = T.eval x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : AffineFun n m) (g : (Fin m → ℝ) → ℝ),
        NetFunc m k g ∧ ∀ x, f x = g (reluVec (T.eval x))

/-- `ReLUn n k` : the set of functions `ℝ^n → ℝ` representable by a ReLU network
with **at most** `k` hidden layers. (See the module docstring for why "at most"
rather than "exactly" is the reading that makes Theorem 2 a true equality.) -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, NetFunc n k' f}

/-- A half-space `{x | ⟨c, x⟩ ≤ d}` in `ℝ^n`. -/
structure Halfspace (n : ℕ) where
  c : Fin n → ℝ
  d : ℝ

/-- The set of points satisfying a half-space inequality. -/
def Halfspace.set {n : ℕ} (H : Halfspace n) : Set (Fin n → ℝ) :=
  {x | (∑ i, H.c i * x i) ≤ H.d}

/-- `f : ℝ^n → ℝ` is continuous piecewise linear: it is continuous, and there is a
finite collection of `p` pieces, the `i`-th piece cut out by a finite system of
`m i` half-space inequalities, whose union covers all of `ℝ^n`, on each of which
`f` agrees with some affine function. This is a genuine finite polyhedral
subdivision condition (not a "max of affine functions" normal form, and not
phrased in terms of ReLU networks). -/
def IsCPWL (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  Continuous f ∧
  ∃ (p : ℕ) (m : Fin p → ℕ) (H : ∀ i, Fin (m i) → Halfspace n) (A : Fin p → AffineFun n 1),
    (⋃ i, ⋂ j, (H i j).set) = Set.univ ∧
    ∀ i (x : Fin n → ℝ), (∀ j, x ∈ (H i j).set) → f x = (A i).eval x 0

/-- `CPWL n` : the set of continuous piecewise linear functions `ℝ^n → ℝ`. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | IsCPWL n f}

/-- The depth bound `⌈log_3(n - 1)⌉ + 1`, encoded via `Nat.clog`. -/
def depthBound (n : ℕ) : ℕ := Nat.clog 3 (n - 1) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent091


namespace Agent092

/-!
# Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity: Subdividing the Simplex")

We formalize:  for `n ≥ 3`,  `CPWL n = ReLUn n (⌈log_3 (n-1)⌉ + 1)`.

## Modelling choices

* `ℝ^n` is encoded as `Fin n → ℝ`.
* An affine map `ℝ^a → ℝ^b` is a pair `(A, c)` with `A : Matrix (Fin b) (Fin a) ℝ` and
  `c : Fin b → ℝ`, evaluated as `x ↦ A.mulVec x + c`.
* A "ReLU network with exactly `k` hidden layers" from `ℝ^a` to `ℝ` is encoded as an
  inductive chain `NetworkChain a k`: either a single affine map `a → 1` (0 hidden
  layers), or an affine map `a → b` followed by `ReLU` and a chain of length `k` from
  `b` (giving `k + 1` hidden layers). This literally mirrors the alternating
  composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper.
* `ReLUn n k` is the set of functions representable by *some* `NetworkChain n k`, i.e.
  representable with **exactly** `k` hidden layers (the literal reading of the paper's
  "the subset of CPWL_n representable with k hidden layers").
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of affine
  functions `ℝ^n → ℝ` such that every point has a neighborhood on which `f` coincides
  with one member of the family. This is a genuine local-piecewise-affine condition,
  not a max-of-affine normal form and not "representable by a ReLU network".
* The depth bound `⌈log_3 (n-1)⌉ + 1` is encoded with `Real.logb 3` and `Nat.ceil`.
-/

/-- The scalar ReLU function. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given by a matrix and a translation vector. -/
def AffineMap (a b : ℕ) : Type := Matrix (Fin b) (Fin a) ℝ × (Fin b → ℝ)

/-- Evaluate an affine transformation. -/
def affineEval {a b : ℕ} (T : AffineMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.1.mulVec x + T.2

/-- An affine *function* `ℝ^n → ℝ` (an affine map into `ℝ^1`, read off at the unique
coordinate). -/
def AffineFunc (n : ℕ) : Type := AffineMap n 1

/-- Evaluate an affine function. -/
def AffineFunc.eval {n : ℕ} (g : AffineFunc n) (x : Fin n → ℝ) : ℝ :=
  affineEval g x 0

/-- `NetworkChain a k` encodes the data of a ReLU network computing a function
`ℝ^a → ℝ` with exactly `k` hidden layers, i.e. the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations
`T^(1), …, T^(k+1)` with componentwise `ReLU` in between. -/
inductive NetworkChain : ℕ → ℕ → Type where
  /-- Zero hidden layers: a single affine map `a → 1`. -/
  | last {a : ℕ} (T : AffineMap a 1) : NetworkChain a 0
  /-- One more hidden layer: an affine map `a → b`, then `ReLU`, then a chain of
  length `k` on `ℝ^b`. -/
  | cons {a b k : ℕ} (T : AffineMap a b) (rest : NetworkChain b k) : NetworkChain a (k + 1)

/-- The function `ℝ^a → ℝ` computed by a `NetworkChain`. -/
def NetworkChain.eval : {a k : ℕ} → NetworkChain a k → (Fin a → ℝ) → ℝ
  | _, _, .last T, x => affineEval T x 0
  | _, _, .cons T rest, x => rest.eval (reluVec (affineEval T x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
**exactly** `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ c : NetworkChain n k, f = c.eval}

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: `f` is
continuous, and there is a finite family of affine functions such that `f` agrees with
one of them on a neighborhood of every point. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (g : Fin m → AffineFunc n), ∀ x : Fin n → ℝ, ∃ i : Fin m,
      ∀ᶠ y in nhds x, f y = (g i).eval y}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from the theorem, for `n ≥ 3` (so `n - 1 ≥ 2`
as a real number). -/
def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent092


namespace Agent093

/-! ## Basic building blocks -/

/-- The ReLU activation on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `Fin m → ℝ`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias
vector: `x ↦ A x + c`. -/
def AffineMap' (a b : ℕ) := (Fin b → Fin a → ℝ) × (Fin b → ℝ)

/-- Evaluate an affine transformation. -/
def AffineMap'.apply {a b : ℕ} (T : AffineMap' a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, T.1 i j * x j) + T.2 i

/-- An affine *functional* `ℝ^n → ℝ`, i.e. an affine map into `ℝ^1`. -/
def AffFun (n : ℕ) := AffineMap' n 1

/-- Evaluate an affine functional. -/
def AffFun.eval {n : ℕ} (L : AffFun n) (x : Fin n → ℝ) : ℝ := AffineMap'.apply L x 0

/-! ## ReLU networks -/

/--
`Layers a ws b` encodes the data of a chain of affine transformations, alternating with
ReLU, that takes `ℝ^a` to `ℝ^b` and passes through hidden layers whose widths are listed
(in order) in `ws`. This is exactly the data of a ReLU network
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` with `k = ws.length` hidden layers, as in the
paper's definition of a ReLU network of depth `k + 1`.
-/
inductive Layers : ℕ → List ℕ → ℕ → Type
  | last {a b : ℕ} (T : AffineMap' a b) : Layers a [] b
  | cons {a b : ℕ} {ws : List ℕ} (m : ℕ) (T : AffineMap' a m) (rest : Layers m ws b) :
      Layers a (m :: ws) b

/-- The function `ℝ^a → ℝ^b` computed by a chain of layers: the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`. -/
def Layers.apply {a b : ℕ} {ws : List ℕ} : Layers a ws b → (Fin a → ℝ) → (Fin b → ℝ)
  | .last T, x => T.apply x
  | .cons _ T rest, x => rest.apply (reluVec (T.apply x))

/--
`f : ℝ^n → ℝ` is computed by a ReLU network with *at most* `k` hidden layers if there is a
list of hidden-layer widths of length `≤ k` and a matching chain of affine
transformations, alternating componentwise with ReLU, whose composition (followed by
reading off the single real output coordinate) equals `f`.

Modelling choice: we use *at most* `k` hidden layers rather than *exactly* `k`. Adding
extra hidden layers can never shrink the class of representable functions (one can always
insert an identity-computing hidden layer, e.g. via `x ↦ (x, -x) ↦ ReLU(x, -x) ↦ x`), so
`ReLU_{n,k}` is monotone increasing in `k`; this is the reading under which an *equality*
`CPWL_n = ReLU_{n,k}` with a specific value of `k` (rather than only `⊆`) is a meaningful,
nontrivial statement, and is the standard reading in this literature.
-/
def IsReLUComputable (n k : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ ws : List ℕ, ws.length ≤ k ∧ ∃ L : Layers n ws 1, f = fun x => L.apply x 0

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with at
most `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) := {f | IsReLUComputable n k f}

/-! ## Continuous piecewise linear functions -/

/-- A closed, convex polyhedral subset of `ℝ^n`, cut out by finitely many affine
inequalities `(H i).eval x ≤ 0`. -/
def IsPolyhedron (n : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (H : Fin m → AffFun n), S = {x | ∀ i, (H i).eval x ≤ 0}

/--
`CPWL n` is the set of continuous, piecewise linear functions `ℝ^n → ℝ`: functions `f`
that are continuous and admit a finite polyhedral subdivision of `ℝ^n` (finitely many
polyhedral pieces whose union is all of `ℝ^n`) on each piece of which `f` agrees with some
affine function. This is a genuine geometric piecewise-linearity condition, not simply
"expressible by some ReLU network" nor a max-of-affine-functions normal form.
-/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (S : Fin m → Set (Fin n → ℝ)) (L : Fin m → AffFun n),
      (⋃ i, S i) = Set.univ ∧
      (∀ i, IsPolyhedron n (S i)) ∧
      (∀ i, ∀ x ∈ S i, f x = (L i).eval x)}

/-! ## The depth bound `⌈log_3 (n - 1)⌉ + 1` -/

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2 (meaningful for `n ≥ 3`, so that
`n - 1 ≥ 2 > 0`). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-! ## Theorem 2 -/

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent093


namespace Agent094

open scoped BigOperators

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias
vector: `x ↦ A x + c`. -/
def affineApply {a b : ℕ} (A : Matrix (Fin b) (Fin a) ℝ) (c : Fin b → ℝ)
    (x : Fin a → ℝ) : Fin b → ℝ :=
  A.mulVec x + c

/-- A function `ℝ^n → ℝ` is affine if it can be written as `x ↦ c + ⟨a, x⟩` for some
weight vector `a` and bias `c`. -/
def IsAffine (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (c : ℝ), f = fun x => c + ∑ i, a i * x i

/-- `f : ℝ^n → ℝ` is computed by a ReLU network with **exactly** `k` hidden layers.
This formalizes the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper, defined recursively on
`k`: with `0` hidden layers, `f` is just a single affine transformation `T^(1)`
(the case `k = 0`, depth `1`); with `k + 1` hidden layers, `f` is obtained by first
applying an affine transformation `T^(1) : ℝ^n → ℝ^m` into some intermediate width
`m`, then a componentwise ReLU, and then a network with `k` hidden layers on the
result. -/
def ComputedWithHiddenLayers : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => IsAffine n f
  | n, (k + 1), f =>
      ∃ (m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ) (g : (Fin m → ℝ) → ℝ),
        ComputedWithHiddenLayers m k g ∧ f = fun x => g (reluVec (affineApply A c x))

/-- `ReLUn n k`: the set of functions `ℝ^n → ℝ` representable by a ReLU network with
**at most** `k` hidden layers.

Modelling choice: we use "at most `k`" rather than "exactly `k`". Any affine
transformation can implement the identity map after applying ReLU (via the
"doubling trick" `x ↦ (x, -x) ↦ (relu x, relu(-x)) ↦ relu x - relu(-x) = x`, itself
an extra hidden layer), so a function computable with `k` hidden layers is always
also computable with `k + 1` hidden layers; the "exactly `k`" and "at most `k`"
readings therefore describe the same nested family of sets, and "at most" is the
standard convention in the expressivity literature (and the one under which
`ReLU_{n,k} ⊆ ReLU_{n,k+1}` holds, matching the intended reading of Theorem 2 as an
equality of sets of functions attainable *within* a hidden-layer budget). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, ComputedWithHiddenLayers n k' f}

/-- `CPWL n`: the continuous, piecewise-linear functions `ℝ^n → ℝ`. We require `f` to
be continuous, together with a *single finite family* of affine "pieces" `g 0, …,
g (m-1)` such that `f` agrees with one of these pieces on a neighborhood of every
point of `ℝ^n` (a genuine finite polyhedral-type piecewise-affine condition, not a
"representable by a ReLU network" or max-of-affine reformulation). -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ),
      (∀ i, IsAffine n (g i)) ∧
      ∀ x : Fin n → ℝ, ∃ i, ∃ U ∈ nhds x, Set.EqOn f (g i) U}

/-- The depth bound `⌈log_3(n-1)⌉ + 1` from Theorem 2, as a natural number, computed
via the real logarithm `Real.logb 3` and `Nat.ceil`. -/
def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉+1}`, i.e. the CPWL
functions on `ℝ^n` are exactly those representable by a ReLU network with at most
`⌈log_3(n-1)⌉ + 1` hidden layers. -/
theorem theorem2 : ∀ n : ℕ, n ≥ 3 → CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent094


namespace Agent095

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

We encode `ℝ^n` as `Fin n → ℝ`.

* `relu` / `reluVec` : the scalar and componentwise ReLU.
* `Affine a b` : an affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a
  bias vector, `x ↦ A *ᵥ x + c`.
* `HiddenLayers k f` : an inductive judgement saying that the vector-valued function `f`
  is computed by an alternating composition of `k + 1` affine maps and `k` interleaved
  (componentwise) ReLUs, i.e. by a ReLU network with `k` hidden layers, following the
  definition
      T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1).
  The `base` constructor is the case of a single affine map (0 hidden layers, depth 1);
  `step` prepends one more affine-then-ReLU layer.
* `ComputedByReLUNetwork n k f` : a real-valued `f : ℝ^n → ℝ` is computed by some
  `HiddenLayers k` network whose 1-dimensional output is read off as a scalar.
* `ReLUn n k` : functions computed with **at most** `k` hidden layers. We choose "at most"
  rather than "exactly", since a network with `k` hidden layers can always be padded to
  `k' ≥ k` hidden layers computing the very same function (each extra layer can implement
  the identity on ℝ via `relu(x) - relu(-x) = x`, using two neurons per coordinate). Hence
  the classes `ReLU_{n,k}` are increasing in `k`, and reading Theorem 2's `ReLU_{n,d(n)}`
  as "at most `d(n)` hidden layers" is the reading under which the equality
  `CPWL_n = ReLU_{n,d(n)}` can hold (it says `d(n)` hidden layers suffice, and no CPWL_n
  function needs more).
* `CPWL n` : continuous functions `ℝ^n → ℝ` that are affine on each piece of a finite cover
  of `ℝ^n` by closed convex sets (a genuine finite polyhedral-type subdivision condition,
  not defined via ReLU-representability or a max-of-affine normal form).
* `depthBound n` : the quantity `⌈log_3 (n - 1)⌉ + 1`, using the real logarithm
  `Real.logb 3` and `Nat.ceil`.
-/

/-- The scalar ReLU function. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix `A` and bias `c`,
computing `x ↦ A *ᵥ x + c`. -/
structure Affine (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def Affine.eval {a b : ℕ} (T : Affine a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- `HiddenLayers k f` means the vector-valued function `f : ℝ^n → ℝ^m` is computed by a
ReLU network with `k` hidden layers, i.e. by the alternating composition
`T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine transformations. -/
inductive HiddenLayers : (k : ℕ) → {n m : ℕ} → ((Fin n → ℝ) → (Fin m → ℝ)) → Prop
  | base {n m : ℕ} (T : Affine n m) : HiddenLayers 0 T.eval
  | step {n m p : ℕ} (k : ℕ) (T : Affine n m) (g : (Fin m → ℝ) → (Fin p → ℝ))
      (hg : HiddenLayers k g) :
      HiddenLayers (k + 1) (fun x => g (reluVec (T.eval x)))

/-- A real-valued function `f : ℝ^n → ℝ` is computed by a ReLU network with `k` hidden
layers if it arises as the (unique) output coordinate of some `HiddenLayers k` network
with output dimension `1`. -/
def ComputedByReLUNetwork (n k : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ g : (Fin n → ℝ) → (Fin 1 → ℝ), HiddenLayers k g ∧ ∀ x, f x = g x 0

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
**at most** `k` hidden layers (see the module docstring for why "at most" is the right
reading here). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, ComputedByReLUNetwork n k' f}

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: those that are
continuous and admit a finite cover of `ℝ^n` by closed convex pieces on each of which the
function agrees with some affine function. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (a : Fin m → (Fin n → ℝ)) (b : Fin m → ℝ) (S : Fin m → Set (Fin n → ℝ)),
      (⋃ j, S j) = Set.univ ∧
      (∀ j, IsClosed (S j)) ∧
      (∀ j, Convex ℝ (S j)) ∧
      ∀ j, ∀ x ∈ S j, f x = (∑ i, a j i * x i) + b j}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, using the real logarithm to base
`3` and `Nat.ceil`. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n - 1 : ℕ) : ℝ)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3 (n - 1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent095


namespace Agent096

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network
Expressivity: Subdividing the Simplex"):

  For n ≥ 3,  CPWL_n = ReLU_{n, ⌈log_3 (n-1)⌉ + 1}.

## Modelling choices

* Vectors `ℝ^n` are encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is a pair `(A, c)` of a matrix and a
  bias vector, applied as `x ↦ A.mulVec x + c` (`AffMap`).
* A ReLU network with `k` hidden layers and input/output dimensions `a`, `b`
  is encoded as an inductively-defined "typed list" `ReLUNet a b k` of `k + 1`
  affine maps, chained together with a componentwise ReLU after every layer
  except the last, matching the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper.
* `ReLUn n k` is read as *at most* `k` hidden layers (the union over
  `k' ≤ k` of functions computed by some `k'`-hidden-layer network). This is
  the standard convention: it makes `ReLUn n` monotone in `k`
  (`ReLUn n k ⊆ ReLUn n (k+1)`, since any network can be padded with extra
  layers), which is implicitly needed for statements like Theorem 2 to be
  meaningful as an equality at a *specific* depth bound, rather than merely
  the smallest depth at which equality first occurs.
* `CPWL n` is defined honestly as: `f` is continuous, and there is a finite
  family of affine functions such that every point has a neighborhood on
  which `f` coincides with one of them (a genuine local-affine-pieces
  condition, not "representable by a ReLU network" and not a global
  max-of-affine normal form).
* The depth bound `⌈log_3 (n - 1)⌉ + 1` is encoded with `Real.logb 3` and
  `Nat.ceil` (`⌈·⌉₊`), applied to the real number `(n : ℝ) - 1`.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^n`. -/
def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given by a matrix `A` and bias `c`,
computing `x ↦ A * x + c`. -/
structure AffMap (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def AffMap.eval {a b : ℕ} (T : AffMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.c

/-- A ReLU network with input dimension `a`, output dimension `b`, and `k`
hidden layers, encoded as a chain of `k + 1` affine maps. `last T` is the
final (output) affine transformation with no ReLU applied afterwards;
`step T rest` prepends an affine transformation followed by a ReLU. -/
inductive ReLUNet : ℕ → ℕ → ℕ → Type
  | last {a b : ℕ} (T : AffMap a b) : ReLUNet a b 0
  | step {a b c k : ℕ} (T : AffMap a b) (rest : ReLUNet b c k) : ReLUNet a c (k + 1)

/-- The function `ℝ^a → ℝ^b` computed by a ReLU network, i.e. the alternating
composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)`. -/
def ReLUNet.eval {a b k : ℕ} (N : ReLUNet a b k) (x : Fin a → ℝ) : Fin b → ℝ :=
  match N with
  | .last T => T.eval x
  | .step T rest => rest.eval (reluVec (T.eval x))

/-- `f : ℝ^n → ℝ` is computed by *some* ReLU network with *exactly* `k`
hidden layers. -/
def NetComputesExact (n k : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ N : ReLUNet n 1 k, ∀ x : Fin n → ℝ, f x = N.eval x 0

/-- `ReLUn n k`: the CPWL functions `ℝ^n → ℝ` representable by a ReLU network
with *at most* `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, NetComputesExact n k' f }

/-- `CPWL n`: the continuous, piecewise-linear functions `ℝ^n → ℝ`. A
function is CPWL if it is continuous and there is a finite family of affine
functions such that every point of `ℝ^n` has a neighborhood on which `f`
agrees with one member of the family. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (g : Fin m → AffMap n 1),
          ∀ x : Fin n → ℝ, ∃ i : Fin m, ∀ᶠ y in nhds x, f y = (g i).eval y 0 }

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from the paper, as a natural
number: `Nat.ceil` of the real logarithm base `3` of `(n : ℝ) - 1`, plus
one hidden layer accounting for the "+1" in "⌈log_3(n-1)⌉ + 1". -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 : ∀ n : ℕ, n ≥ 3 → CPWL n = ReLUn n (depthBound n) := sorry

end Agent096


namespace Agent097

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):

  For n ≥ 3, CPWL_n = ReLU_{n, ⌈log_3 (n-1)⌉ + 1}.

We encode `ℝ^n` as `Fin n → ℝ`.
-/

/-- The scalar ReLU function `x ↦ max 0 x`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`, encoded as `Fin m → ℝ`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ := fun i => relu (x i)

/-- `T : ℝ^a → ℝ^b` is an affine transformation if it has the form `x ↦ A * x + c`
for some matrix `A` and vector `c`. -/
def IsAffineTransformation (a b : ℕ) (T : (Fin a → ℝ) → (Fin b → ℝ)) : Prop :=
  ∃ (A : Matrix (Fin b) (Fin a) ℝ) (c : Fin b → ℝ), ∀ x, T x = A.mulVec x + c

/-- `f : ℝ^n → ℝ` is computed by a ReLU network with exactly `k` hidden layers if there
is a chain of affine transformations `T^(1), ..., T^(k+1)` with intermediate widths
`n_1, ..., n_k` such that

  `f = T^(k+1) ∘ ReLU ∘ T^(k) ∘ ... ∘ ReLU ∘ T^(1)`.

This is defined by recursion on `k`, peeling off the *first* affine map / ReLU pair each
time: with `k+1` hidden layers, we first apply an affine map `T : ℝ^n → ℝ^m` followed by
`ReLU`, and the remaining computation on `ℝ^m` is a `k`-hidden-layer network. The base
case `k = 0` is a network with no hidden layers, i.e. `f` itself is affine
(a single affine output transformation `T^(1) : ℝ^n → ℝ^1`). -/
def ComputesWithHiddenLayers : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f =>
      ∃ T : (Fin n → ℝ) → (Fin 1 → ℝ),
        IsAffineTransformation n 1 T ∧ ∀ x, f x = T x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : (Fin n → ℝ) → (Fin m → ℝ)) (g : (Fin m → ℝ) → ℝ),
        IsAffineTransformation n m T ∧
        ComputesWithHiddenLayers m k g ∧
        ∀ x, f x = g (reluVec (T x))

/-- `ReLUn n k`: the functions `ℝ^n → ℝ` representable by a ReLU network with *at most*
`k` hidden layers. (We use "at most", the standard reading in the depth-separation
literature: since it need not be true that every `k`-layer-representable function is also
representable with *exactly* `k+1` layers, taking `ReLUn n k` to mean "exactly k" would
make it non-monotone in `k`, which is not the intended reading and would not match how
the class `ReLU_{n,k}` is used in the statement of Theorem 2.) -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ j ≤ k, ComputesWithHiddenLayers n j f}

/-- `f : ℝ^n → ℝ` is continuous and piecewise linear if it is continuous and there is a
finite family of affine functions `x ↦ ⟪A i, x⟫ + b i` such that `f` agrees with one of
them on a neighborhood of every point (a genuine local piecewise-affine condition, not a
"max of affine" normal form and not a reference to ReLU networks). -/
def IsCPWL (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  Continuous f ∧
  ∃ (m : ℕ) (A : Fin m → (Fin n → ℝ)) (b : Fin m → ℝ),
    ∀ x : Fin n → ℝ, ∃ i : Fin m, ∀ᶠ y in nhds x, f y = (∑ j, A i j * y j) + b i

/-- `CPWL n`: the space of continuous piecewise linear functions `ℝ^n → ℝ`. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) := {f | IsCPWL n f}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1`, using the real logarithm base 3 and the
natural-number ceiling. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent097


namespace Agent098

/-!
Formalization of Theorem 2 of arXiv:2505.14338 ("Better Neural Network Expressivity:
Subdividing the Simplex"):

  For n ≥ 3,  CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}.

## Modelling choices

* `ℝ^n` is encoded as `Fin n → ℝ`.
* Affine transformations `ℝ^a → ℝ^b` are encoded concretely as a matrix `A` together with a
  bias vector `b`, via `x ↦ A.mulVec x + b`.
* A ReLU network with *exactly* `k` hidden layers computing `f : ℝ^n → ℝ` is defined by
  recursion on `k`: with `0` hidden layers it is a single affine map `ℝ^n → ℝ^1`; with
  `k+1` hidden layers it is an affine map `ℝ^n → ℝ^m` followed by componentwise ReLU,
  followed by a network with `k` hidden layers on the result.
* `ReLUn n k` is taken to be the functions representable with **at most** `k` hidden
  layers (not *exactly* `k`). This is the reading that makes Theorem 2 true as a genuine
  equality: representability classes are monotone in the number of hidden layers (a
  network with `j ≤ k` hidden layers can always be padded, e.g. by inserting an extra
  affine layer that is the identity in effect, to one with exactly `k` hidden layers
  representing the same function), so "exactly k" and "at most k" differ only by this
  padding step, and the paper's `ReLU_{n,k}` is understood as the standard "at most k"
  notion of network complexity classes.
* `CPWL n` is defined as: `f` is continuous, and there is a *finite* family of closed
  polyhedral pieces covering `ℝ^n` (each cut out by finitely many affine inequalities)
  together with an affine function per piece, such that `f` agrees with the affine
  function on each piece. This is a genuine finite polyhedral subdivision condition, not
  a "representable by a ReLU network" or "max of affine functions" definition.
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded using the real logarithm `Real.logb 3`
  applied to `(n : ℝ) - 1` and `Nat.ceil`, matching the paper's real-valued ceiling of a
  real logarithm exactly (for `n ≥ 3`, `(n : ℝ) - 1 ≥ 2 > 0` so the logarithm is
  well-behaved).
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias vector. -/
structure AffineTransform (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  bias : Fin b → ℝ

/-- The function `ℝ^a → ℝ^b` computed by an affine transformation. -/
def AffineTransform.eval {a b : ℕ} (T : AffineTransform a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.bias

/-- A scalar-valued affine function `ℝ^n → ℝ`, `x ↦ ⟨a, x⟩ + b`. Used for describing the
affine pieces of a CPWL function. -/
structure AffineFn (n : ℕ) where
  a : Fin n → ℝ
  b : ℝ

/-- The function `ℝ^n → ℝ` computed by a scalar affine function. -/
def AffineFn.eval {n : ℕ} (f : AffineFn n) (x : Fin n → ℝ) : ℝ :=
  (∑ i, f.a i * x i) + f.b

/-- A subset of `ℝ^n` is a (closed) polyhedron if it is a finite intersection of closed
half-spaces `{x | ⟨a_i, x⟩ ≤ b_i}`. -/
def IsPolyhedron (n : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (A : Fin m → (Fin n → ℝ)) (b : Fin m → ℝ),
    S = {x | ∀ i, (∑ j, A i j * x j) ≤ b i}

/-- `f : ℝ^n → ℝ` is continuous piecewise linear: it is continuous, and there is a finite
family of closed polyhedral pieces covering `ℝ^n`, together with an affine function per
piece, such that `f` agrees with the corresponding affine function on each piece. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (S : Fin m → Set (Fin n → ℝ)) (g : Fin m → AffineFn n),
      (∀ i, IsPolyhedron n (S i)) ∧
      (Set.univ = ⋃ i, S i) ∧
      (∀ i, ∀ x ∈ S i, f x = (g i).eval x)}

/-- `ReLURepExact k n f` means `f : ℝ^n → ℝ` is computed by a ReLU network with *exactly*
`k` hidden layers, i.e. by the alternating composition
`T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}` of `k + 1` affine transformations with
componentwise ReLU applications in between, ending in an affine map to `ℝ^1` (whose single
output component is the value of `f`). Defined by recursion on `k`. -/
def ReLURepExact : ℕ → (n : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | 0, n, f =>
      ∃ T : AffineTransform n 1, ∀ x, f x = T.eval x 0
  | (k + 1), n, f =>
      ∃ (m : ℕ) (T : AffineTransform n m) (g : (Fin m → ℝ) → ℝ),
        ReLURepExact k m g ∧ ∀ x, f x = g (fun i => relu (T.eval x i))

/-- `ReLUn n k`, the set of functions `ℝ^n → ℝ` representable by a ReLU network with *at
most* `k` hidden layers (see the module docstring for why "at most" rather than
"exactly" is the right reading for Theorem 2). -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ j ≤ k, ReLURepExact j n f}

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from Theorem 2, with the ceiling of the real
logarithm base 3 taken via `Nat.ceil` and `Real.logb`. -/
def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent098


namespace Agent099

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

Modelling choices (see summary at the call site / final report):

* Vectors `ℝ^n` are encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is given concretely by a matrix of
  coefficients `A : Fin b → Fin a → ℝ` and a bias vector, evaluated as
  `x ↦ A x + bias`.
* A ReLU network with `k` hidden layers is represented by the inductive
  family `ReLUNet n k` below, which literally encodes the alternating
  composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper,
  with all intermediate widths existentially quantified.
* `ReLUn n k` is the set of functions representable with **at most** `k`
  hidden layers (i.e. with some `k' ≤ k`). This is the standard reading
  that makes `ReLUn n k` monotone in `k`, matching the informal use of
  "depth budget" in the statement of Theorem 2.
* `CPWL n` is defined as: continuous, and locally (in a neighbourhood of
  every point) equal to one of finitely many globally-fixed affine
  functions. This is a genuine piecewise-affine condition, not a
  "representable by ReLU network" or "max of affine" definition.
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded using the real logarithm
  `Real.logb 3` composed with `Nat.ceil`.
-/

/-- The ReLU function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ :=
  fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely as `x ↦ A x + bias`. -/
structure AffMap (a b : ℕ) where
  A    : Fin b → Fin a → ℝ
  bias : Fin b → ℝ

/-- Evaluation of an affine transformation. -/
def AffMap.eval {a b : ℕ} (T : AffMap a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, T.A i j * x j) + T.bias i

/--
A ReLU network with input dimension `n` and `k` hidden layers, encoded as
`k + 1` affine transformations `T^(1), …, T^(k+1)` with the intermediate
widths existentially quantified:

* `last T` is the base case of a network with `0` hidden layers: a single
  affine transformation `T^(1) : ℝ^n → ℝ` (the output layer, output
  dimension `1`), with no ReLU applied.
* `cons m T rest` prepends an affine transformation `T : ℝ^n → ℝ^m`
  followed by a componentwise ReLU, then continues with the network `rest`
  (which has `k` further hidden layers), giving `k + 1` hidden layers in
  total.
-/
inductive ReLUNet : ℕ → ℕ → Type where
  | last {n : ℕ} (T : AffMap n 1) : ReLUNet n 0
  | cons {n k : ℕ} (m : ℕ) (T : AffMap n m) (rest : ReLUNet m k) : ReLUNet n (k + 1)

/-- The real-valued function computed by a ReLU network. -/
def ReLUNet.eval : {n k : ℕ} → ReLUNet n k → (Fin n → ℝ) → ℝ
  | _, _, .last T, x => T.eval x 0
  | _, _, .cons _ T rest, x => rest.eval (reluVec (T.eval x))

/--
`ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU
network with **at most** `k` hidden layers (some `k' ≤ k`).
-/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, ∃ net : ReLUNet n k', ∀ x, net.eval x = f x }

/-- A function `ℝ^n → ℝ` is affine if it has the form `x ↦ ∑ a_i x_i + b`. -/
def IsAffineFn (n : ℕ) (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x, g x = (∑ i, a i * x i) + b

/--
`CPWL n` is the space of continuous piecewise-linear (affine) functions
`ℝ^n → ℝ`: functions that are continuous, and such that there is a finite
family of affine functions with which `f` locally agrees at every point
(i.e. every point has a neighbourhood on which `f` coincides with one of
the finitely many affine pieces).
-/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
      ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ),
        (∀ i, IsAffineFn n (g i)) ∧
        ∀ x : Fin n → ℝ, ∃ i, ∀ᶠ y in nhds x, f y = g i y }

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from Theorem 2. -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/--
**Theorem 2.** For `n ≥ 3`, the space of continuous piecewise-linear
functions on `ℝ^n` equals the space of functions representable by a ReLU
network with `⌈log_3(n-1)⌉ + 1` hidden layers.
-/
theorem theorem2 : ∀ n : ℕ, 3 ≤ n → CPWL n = ReLUn n (depthBound n) := sorry

end Agent099


namespace Agent100

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

"Better Neural Network Expressivity: Subdividing the Simplex"
(Bakaev, Brunck, Hertrich, Stade, Yehudayoff).

**Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3 (n-1)⌉ + 1}`.

## Modelling choices

* Vectors `ℝ^n` are encoded as `Fin n → ℝ`.
* An affine transformation `ℝ^a → ℝ^b` is encoded concretely as a pair `(A, bias)` with
  `A : Matrix (Fin b) (Fin a) ℝ` and `bias : Fin b → ℝ`, acting as `x ↦ A.mulVec x + bias`.
* A ReLU network with `k` *hidden layers* (depth `k + 1`) computing `f : ℝ^n → ℝ` is defined
  recursively: with `0` hidden layers it is a single affine map `ℝ^n → ℝ^1`; with `k+1`
  hidden layers it is an affine map `ℝ^n → ℝ^m` into some hidden width `m`, followed by
  componentwise ReLU, followed by a network with `k` hidden layers on `ℝ^m`. This exactly
  mirrors the alternating composition
  `T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}` from the paper.
* `ReLUn n k` is the set of functions representable with *exactly* `k` hidden layers (the
  literal reading of `ReLU_{n,k}`). This choice is consistent with the theorem: one can pad
  a `k`-hidden-layer network into a `(k+1)`-hidden-layer network computing the same function
  (e.g. by carrying each coordinate `x_i` through an extra layer as `relu(x_i) - relu(-x_i)`),
  so the classes are monotone in `k` and the "exactly `k`" and "at most `k`" readings agree
  on which functions are representable within `k` layers.
* `CPWL n` is defined genuinely: `f` is continuous and there is a *finite* family of affine
  functions `g : Fin m → (ℝ^n → ℝ)` such that around every point `x`, `f` locally agrees with
  one of the `g i` (i.e. `f =ᶠ[𝓝 x] g i`). This is a real piecewise-affine/local-polyhedral
  condition, not a disguised "representable by a ReLU network" or "max of affine functions"
  statement.
* The depth bound `⌈log_3 (n - 1)⌉ + 1` is encoded using the real logarithm `Real.logb 3`
  together with `Nat.ceil`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^n`. -/
def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a matrix and a bias vector. -/
structure AffineTransform (a b : ℕ) where
  A : Matrix (Fin b) (Fin a) ℝ
  bias : Fin b → ℝ

/-- The function `ℝ^a → ℝ^b` computed by an affine transformation: `x ↦ A x + bias`. -/
def AffineTransform.toFun {a b : ℕ} (T : AffineTransform a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  T.A.mulVec x + T.bias

/--
`IsReLURepresentable n k f` means `f : ℝ^n → ℝ` is computed by a ReLU network with `k` hidden
layers, i.e. by the alternating composition
`T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ⋯ ∘ ReLU ∘ T^{(1)}`
of `k + 1` affine transformations `T^{(1)}, …, T^{(k+1)}` with `ReLU` applied componentwise
after each of the first `k` of them.

Defined by recursion on `k`: with `0` hidden layers, `f` is itself an affine map into `ℝ^1`;
with `k + 1` hidden layers, `f` factors as `g ∘ ReLU ∘ T` where `T : ℝ^n → ℝ^m` is affine
(the first layer) and `g : ℝ^m → ℝ` is representable with `k` hidden layers.
-/
def IsReLURepresentable : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : AffineTransform n 1, ∀ x, f x = T.toFun x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : AffineTransform n m) (g : (Fin m → ℝ) → ℝ),
        IsReLURepresentable m k g ∧ ∀ x, f x = g (reluVec (T.toFun x))

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with
exactly `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) := {f | IsReLURepresentable n k f}

/-- An affine (as opposed to merely linear) real-valued function `ℝ^n → ℝ`. -/
def IsAffineFun (n : ℕ) (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ T : AffineTransform n 1, ∀ x, g x = T.toFun x 0

/--
`CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: those `f` that are
continuous and admit a *finite* family of affine functions `g 0, …, g (m-1)` such that around
every point `x` of `ℝ^n`, `f` coincides with some `g i` on a neighbourhood of `x`. This is a
genuine local-polyhedral piecewise-affine condition, independent of any ReLU-network
representation and not simply a "max of finitely many affine functions" normal form.
-/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | Continuous f ∧
    ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ),
      (∀ i, IsAffineFun n (g i)) ∧ ∀ x, ∃ i, f =ᶠ[nhds x] g i}

/-- The depth bound `⌈log_3 (n - 1)⌉ + 1` from Theorem 2, for `n ≥ 3` (in general `n ≥ 2`
suffices for the logarithm to be well-behaved). -/
noncomputable def depthBound (n : ℕ) : ℕ :=
  Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3 (n - 1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : n ≥ 3) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent100

set_option maxHeartbeats 0 in

run_cmd Lean.Elab.Command.liftTermElabM (dfCheck ["001", "002", "003", "004", "005", "006", "007", "008", "009", "010", "011", "012", "013", "014", "015", "016", "017", "018", "019", "021", "022", "023", "024", "025", "026", "028", "029", "030", "031", "032", "033", "034", "035", "036", "037", "038", "039", "040", "041", "042", "043", "044", "045", "046", "047", "048", "049", "050", "051", "052", "053", "054", "055", "056", "057", "058", "059", "060", "061", "062", "063", "064", "065", "066", "067", "068", "069", "070", "071", "072", "073", "074", "075", "076", "077", "078", "079", "080", "081", "082", "083", "085", "086", "087", "088", "089", "090", "091", "092", "093", "094", "095", "096", "097", "098", "099", "100"])

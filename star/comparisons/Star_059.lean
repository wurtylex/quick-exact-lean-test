/-!
# Star comparison: `Agent059` vs `Ref`

Agent 059 is in the "polyhedral subdivision" family: its `CPWL` is the honest
piecewise-linearity condition (continuous + finite polyhedral cover on each piece
of which `f` agrees with an affine functional), exactly as in `Ref`.  The only
difference is *how a polyhedron is packaged*:

* `Ref.IsPolyhedron n S` : `S` is a finite **intersection of halfspaces**
  `S = ⋂ i, H i` with each `H i` a halfspace.
* `Agent059.IsPolyhedron S` : `S` is cut out by a finite **system of affine
  inequalities**, `S = {x | ∀ i, ⟪a i, x⟫ ≤ b i}`.

These are the same notion; the bridge is `Set.mem_iInter` plus `choose` to turn
`∀ i, IsHalfspace (H i)` into coefficient functions.  So `cpwl` is *true* and is
proved below.

`ReLUn` also agrees: both files use "**at most** `k`" hidden layers, and the two
`ComputedBy`/`ReLURepresentable` recursions differ only in the concrete encoding
of an affine map (`Matrix`+`mulVec` vs. an explicit weight function and sum),
which is definitional.  So `relun` needs no padding lemma and is proved outright.

`depthBound` is literally the same term (`⌈·⌉₊` *is* `Nat.ceil`), so `depth` is
`rfl` and no `Real.natCeil_logb_natCast` bridge is needed.

Consequently `statement` follows from the three equalities and no `sorry`
remains in this file.
-/

namespace Star_059

/-- The two packagings of "polyhedron" agree: a finite intersection of
halfspaces is the same thing as the solution set of a finite system of affine
inequalities. -/
private lemma poly_iff (n : ℕ) (S : Set (Fin n → ℝ)) :
    Agent059.IsPolyhedron S ↔ Ref.IsPolyhedron n S := by
  constructor
  · rintro ⟨m, a, b, rfl⟩
    refine ⟨m, fun i => {x | (∑ j, a i j * x j) ≤ b i}, fun i => ⟨a i, b i, rfl⟩, ?_⟩
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
  · rintro ⟨m, H, hH, rfl⟩
    have hH' : ∀ i, ∃ (a : Fin n → ℝ) (b : ℝ), H i = {x | (∑ j, a j * x j) ≤ b} := hH
    choose a b hab using hH'
    refine ⟨m, a, b, ?_⟩
    ext x
    simp only [Set.mem_iInter, hab, Set.mem_setOf_eq]

/-- Agent 059's `CPWL` is the reference `CPWL`. -/
theorem cpwl (n : ℕ) : Agent059.CPWL n = Ref.CPWL n := by
  ext f
  simp only [Agent059.CPWL, Ref.CPWL, Ref.IsCPWL, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hc, m, S, g, hP, hg, hU, hfg⟩
    exact ⟨hc, m, S, g, fun i => (poly_iff n (S i)).1 (hP i), hg, hU, hfg⟩
  · rintro ⟨hc, m, S, g, hP, hg, hU, hfg⟩
    exact ⟨hc, m, S, g, fun i => (poly_iff n (S i)).2 (hP i), hg, hU, hfg⟩

/-- The two recursive notions of "computed by a ReLU network with exactly `k`
hidden layers" coincide.  The induction is on `k`, generalising the input
dimension `n` and the function `f`, since the recursive call changes both.

Each step is definitional: `Ref.Aff.eval T x i = T.M.mulVec x i + T.c i` and
`Agent059.AffineMap.eval T x i = (∑ j, T.A i j * x j) + T.bias i` are the same
term once `Matrix.mulVec`/`dotProduct` and `Pi.add` are unfolded, and the two
`relu`/`reluVec` are both `fun i => max 0 (v i)`. -/
private lemma computedBy_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent059.ReLURepresentable n k f ↔ Ref.ComputedBy n k f := by
  intro k
  induction k with
  | zero =>
    intro n f
    simp only [Agent059.ReLURepresentable, Ref.ComputedBy, Agent059.IsAffineFun]
    constructor
    · rintro ⟨w, c, hf⟩
      exact ⟨⟨Matrix.of fun _ => w, fun _ => c⟩, hf⟩
    · rintro ⟨T, hT⟩
      exact ⟨T.M 0, T.c 0, hT⟩
  | succ k ih =>
    intro n f
    simp only [Agent059.ReLURepresentable, Ref.ComputedBy]
    constructor
    · rintro ⟨m, T, g, hg, rfl⟩
      exact ⟨m, ⟨Matrix.of T.A, T.bias⟩, g, (ih m g).1 hg, fun _ => rfl⟩
    · rintro ⟨m, T, g, hg, hf⟩
      exact ⟨m, ⟨fun i j => T.M i j, T.c⟩, g, (ih m g).2 hg, funext hf⟩

/-- Agent 059's `ReLUn` is the reference `ReLUn`.  Both files read the depth as
"at most `k`", so the hard padding identity `x = relu x - relu (-x)` is *not*
needed here. -/
theorem relun (n k : ℕ) : Agent059.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent059.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  exact exists_congr fun j => and_congr_right fun _ => computedBy_iff j n f

/-- The depth bounds are the *same term*: `⌈·⌉₊` is notation for `Nat.ceil`. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent059.depthBound n = Ref.depthBound n := rfl

/-- The two statements of Theorem 2 are equivalent — indeed each side rewrites
into the other along `cpwl`, `relun` and `depth`. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent059.CPWL n = Agent059.ReLUn n (Agent059.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
  constructor
  · intro h n hn
    have hx := h n hn
    rw [cpwl n, relun n (Agent059.depthBound n), depth n hn] at hx
    exact hx
  · intro h n hn
    have hx := h n hn
    rw [← cpwl n, ← relun n (Ref.depthBound n), ← depth n hn] at hx
    exact hx

end Star_059

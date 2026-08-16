/-!
# Star comparison: `Agent021` vs `Ref`

Agent 021 belongs to the *polyhedral subdivision* family: its `CPWL` is the
honest geometric condition (continuous + a finite polyhedral cover of `ℝⁿ` on
each piece of which `f` agrees with an affine functional), exactly as in
`Ref.IsCPWL`.  Two cosmetic differences have to be bridged:

* a polyhedron is written as the solution set `{x | ∀ l, ⟨c l, x⟩ ≤ d l}` of a
  finite system of inequalities, where the reference writes a finite `⋂` of
  halfspaces (`poly_iff` below, via `Set.mem_iInter` and `choose`);
* the affine functional on each piece is given by its coefficients `a i, b i`
  where the reference quantifies over a function `g i` together with a proof
  `Ref.IsAffine (g i)` (again `choose` in one direction, `rfl` in the other).

`ReLUn` is "at most `k`" on **both** sides, so the padding identity
`x = relu x - relu (-x)` is *not* needed; the only content is that
`Agent021.ComputesReLU` is an `inductive` where `Ref.ComputedBy` is a recursive
`def`, and that `Agent021.AffineMap` and `Ref.Aff` are the same record.

`depthBound` is syntactically identical on both sides.

Verdict: all four obligations are provable; nothing is refuted; no `sorry`.
-/

namespace Star_021

/-! ### `CPWL` -/

/-- The two polyhedron predicates agree: a finite intersection of halfspaces is
the solution set of a finite system of affine inequalities, and conversely. -/
private lemma poly_iff (n : ℕ) (S : Set (Fin n → ℝ)) :
    Ref.IsPolyhedron n S ↔ Agent021.IsPolyhedron n S := by
  constructor
  · rintro ⟨m, H, hH, rfl⟩
    simp only [Ref.IsHalfspace] at hH
    choose a b hab using hH
    refine ⟨m, a, b, ?_⟩
    ext x
    constructor
    · intro hx l
      have hxl := Set.mem_iInter.mp hx l
      rw [hab l] at hxl
      exact hxl
    · intro hx
      refine Set.mem_iInter.mpr fun l => ?_
      rw [hab l]
      exact hx l
  · rintro ⟨M, c, d, rfl⟩
    refine ⟨M, fun l => {x | (∑ j, c l j * x j) ≤ d l}, fun l => ⟨c l, d l, rfl⟩, ?_⟩
    ext x
    simp [Set.mem_iInter]

/-- Both files define `CPWL` by a finite polyhedral cover with affine pieces, so
the sets are equal; the only work is repackaging the polyhedra (`poly_iff`) and
the affine pieces (coefficients versus a function plus `Ref.IsAffine`). -/
theorem cpwl (n : ℕ) : Agent021.CPWL n = Ref.CPWL n := by
  ext f
  simp only [Agent021.CPWL, Ref.CPWL, Ref.IsCPWL, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hcont, N, P, a, b, hP, hcov, hfa⟩
    exact ⟨hcont, N, P, fun i x => (∑ j, a i j * x j) + b i,
      fun i => (poly_iff n (P i)).mpr (hP i),
      fun i => ⟨a i, b i, fun _ => rfl⟩, hcov, hfa⟩
  · rintro ⟨hcont, m, P, g, hP, hg, hcov, hfg⟩
    simp only [Ref.IsAffine] at hg
    choose a b hab using hg
    exact ⟨hcont, m, P, a, b, fun i => (poly_iff n (P i)).mp (hP i), hcov,
      fun i x hx => (hfg i x hx).trans (hab i x)⟩

/-! ### `ReLUn` -/

/-- `Ref.ComputedBy` (a recursion on the layer count) implies the agent's
`inductive` version.  The induction is on `k`, generalised over `n` and `f`,
because the successor case changes the ambient dimension; the two `reluVec`s
and the two affine-evaluation functions are definitionally equal, so only the
`Ref.Aff` record has to be repacked into `Agent021.AffineMap`. -/
private lemma computes_of_computedBy :
    ∀ (n k : ℕ) (f : (Fin n → ℝ) → ℝ),
      Ref.ComputedBy n k f → Agent021.ComputesReLU n k f := by
  intro n k
  induction k generalizing n with
  | zero =>
    intro f hf
    have hf' : ∃ T : Ref.Aff n 1, ∀ x, f x = T.eval x 0 := hf
    obtain ⟨T, hT⟩ := hf'
    have hfe : f = fun x => (Agent021.AffineMap.mk T.M T.c).apply x 0 := by
      funext x; exact hT x
    rw [hfe]
    exact Agent021.ComputesReLU.base _
  | succ k ih =>
    intro f hf
    have hf' : ∃ (m : ℕ) (T : Ref.Aff n m) (g : (Fin m → ℝ) → ℝ),
        Ref.ComputedBy m k g ∧ ∀ x, f x = g (Ref.reluVec (T.eval x)) := hf
    obtain ⟨m, T, g, hg, hfx⟩ := hf'
    have hfe : f = fun x =>
        g (Agent021.reluVec ((Agent021.AffineMap.mk T.M T.c).apply x)) := by
      funext x; exact hfx x
    rw [hfe]
    exact Agent021.ComputesReLU.step _ (ih m g hg)

/-- The converse, by induction on the derivation. -/
private lemma computedBy_of_computes {n k : ℕ} {f : (Fin n → ℝ) → ℝ} :
    Agent021.ComputesReLU n k f → Ref.ComputedBy n k f := by
  intro h
  induction h with
  | base T => exact ⟨⟨T.A, T.b⟩, fun _ => rfl⟩
  | step T _ ih => exact ⟨_, ⟨T.A, T.b⟩, _, ih, fun _ => rfl⟩

/-- Both files read `ReLU_{n,k}` as *at most* `k` hidden layers (`∃ j ≤ k, …`),
so no padding argument is needed. -/
theorem relun (n k : ℕ) : Agent021.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent021.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, computedBy_of_computes h⟩
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, computes_of_computedBy n j f h⟩

/-! ### `depthBound` -/

/-- Both files write `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`, character for
character, so `hn` is not needed and no `Nat.clog` bridge is required. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent021.depthBound n = Ref.depthBound n := rfl

/-! ### The statement of Theorem 2 -/

/-- Pointwise transport of the theorem-2 equation across the three component
identifications above.  This does **not** invoke `Agent021.theorem2` or
`Ref.theorem2` (both `sorry`-ed); it only rewrites with `cpwl`, `depth`,
`relun`. -/
private lemma thm2_iff (n : ℕ) (hn : 3 ≤ n) :
    (Agent021.CPWL n = Agent021.ReLUn n (Agent021.depthBound n)) ↔
      (Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
  rw [cpwl n, depth n hn, relun n (Ref.depthBound n)]

theorem statement :
    (∀ n, 3 ≤ n → Agent021.CPWL n = Agent021.ReLUn n (Agent021.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
  constructor
  · intro h n hn
    exact (thm2_iff n hn).mp (h n hn)
  · intro h n hn
    exact (thm2_iff n hn).mpr (h n hn)

end Star_021

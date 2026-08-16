import QuickTest.Formalizations.Thm2_032
import QuickTest.Reference

namespace Star_032

/-!
# Comparison of `Agent032` against `Ref`

`Agent032` is in the "polyhedral subdivision" family: its `CPWL` is the honest
continuous-piecewise-linear condition (continuity plus a finite polyhedral cover
on each piece of which `f` is affine), exactly like `Ref.IsCPWL`.  The three
cosmetic differences are

* the index of the cover is an arbitrary `Finite` type instead of `Fin m`;
* affineness is packaged as `IsAffineOn f (P i)` instead of a separate global
  affine `g i` plus an agreement clause;
* a polyhedron is given by one system `{x | ∀ j, ⟪A j, x⟫ ≤ b j}` instead of an
  intersection of individually-named halfspaces.

All three are reversible, so `cpwl` is genuinely provable.  Likewise both files
read `ReLU_{n,k}` as **at most** `k` hidden layers, and the two affine-map
structures (`Aff` / `AffineMap'`) have definitionally equal evaluation, so
`relun` is provable too — no padding identity is needed here.
-/

/-- `Ref.Aff.eval` and `Agent032.AffineMap'.eval` agree: `Matrix.mulVec` unfolds
to the same `Finset.sum`, and `Pi` addition is pointwise. -/
private lemma eval_eq {a b : ℕ} (M : Matrix (Fin b) (Fin a) ℝ) (c : Fin b → ℝ)
    (x : Fin a → ℝ) :
    Ref.Aff.eval ⟨M, c⟩ x = Agent032.AffineMap'.eval ⟨M, c⟩ x := rfl

/-- The two polyhedron predicates agree: a finite intersection of halfspaces is
the solution set of a finite system of affine inequalities, and conversely. -/
private lemma poly_iff (n : ℕ) (S : Set (Fin n → ℝ)) :
    Ref.IsPolyhedron n S ↔ Agent032.IsPolyhedron S := by
  constructor
  · rintro ⟨m, H, hH, rfl⟩
    simp only [Ref.IsHalfspace] at hH
    choose a b hab using hH
    refine ⟨m, a, b, ?_⟩
    ext x
    constructor
    · intro hx j
      have hxj := Set.mem_iInter.mp hx j
      rw [hab j] at hxj
      exact hxj
    · intro hx
      refine Set.mem_iInter.mpr fun j => ?_
      rw [hab j]
      exact hx j
  · rintro ⟨m, A, b, rfl⟩
    refine ⟨m, fun j => {x | (∑ i, A j i * x i) ≤ b j}, fun j => ⟨A j, b j, rfl⟩, ?_⟩
    ext x
    simp [Set.mem_iInter]

/-- The two "computed by a network with exactly `k` hidden layers" predicates
agree, by induction on `k`; the affine-map structures are interchanged
componentwise and the two `reluVec`s are definitionally equal. -/
private lemma computable_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent032.ReLUComputable n k f ↔ Ref.ComputedBy n k f := by
  intro k
  induction k with
  | zero =>
      intro n f
      constructor
      · rintro ⟨⟨A, c⟩, hT⟩
        exact ⟨⟨A, c⟩, hT⟩
      · rintro ⟨⟨M, c⟩, hT⟩
        exact ⟨⟨M, c⟩, hT⟩
  | succ k ih =>
      intro n f
      constructor
      · rintro ⟨m, ⟨A, c⟩, g, hg, hf⟩
        exact ⟨m, ⟨A, c⟩, g, (ih m g).mp hg, hf⟩
      · rintro ⟨m, ⟨M, c⟩, g, hg, hf⟩
        exact ⟨m, ⟨M, c⟩, g, (ih m g).mpr hg, hf⟩

theorem cpwl (n : ℕ) : Agent032.CPWL n = Ref.CPWL n := by
  ext f
  simp only [Agent032.CPWL, Ref.CPWL, Ref.IsCPWL, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hcont, ι, hι, P, hP, hcov, haff⟩
    haveI : Finite ι := hι
    simp only [Agent032.IsAffineOn] at haff
    choose A c hAc using haff
    -- re-index the finite cover along `ι ≃ Fin (Nat.card ι)`
    let e := Finite.equivFin ι
    refine ⟨hcont, Nat.card ι, fun k => P (e.symm k),
      fun k x => (∑ j, A (e.symm k) j * x j) + c (e.symm k),
      fun k => (poly_iff n _).mpr (hP _),
      fun k => ⟨A (e.symm k), c (e.symm k), fun x => rfl⟩, ?_,
      fun k x hx => hAc (e.symm k) x hx⟩
    refine Set.eq_univ_of_forall fun x => ?_
    have hx : x ∈ ⋃ i, P i := by rw [hcov]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨e i, by simpa using hi⟩
  · rintro ⟨hcont, m, P, g, hP, hg, hcov, hfg⟩
    refine ⟨hcont, Fin m, inferInstance, P, fun i => (poly_iff n _).mp (hP i), hcov, ?_⟩
    intro i
    obtain ⟨a, b, hab⟩ := hg i
    exact ⟨a, b, fun x hx => by rw [hfg i x hx, hab x]⟩

theorem relun (n k : ℕ) : Agent032.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent032.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (computable_iff j n f).mp hf⟩
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (computable_iff j n f).mpr hf⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent032.depthBound n = Ref.depthBound n := rfl

theorem statement :
    (∀ n, 3 ≤ n → Agent032.CPWL n = Agent032.ReLUn n (Agent032.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
  constructor
  · intro h n hn
    rw [← cpwl n, ← depth n hn, ← relun n (Agent032.depthBound n)]
    exact h n hn
  · intro h n hn
    rw [cpwl n, relun n (Agent032.depthBound n), depth n hn]
    exact h n hn

end Star_032

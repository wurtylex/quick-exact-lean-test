import QuickTest.Formalizations.Thm2_074
import QuickTest.Reference

/-!
# Star comparison: `Agent074` vs `Ref`

`Agent074` is in the "polyhedral subdivision" family: its `CPWL` is the honest
finite-polyhedral-cover condition, exactly like the reference.  The three
differences are cosmetic and all four obligations are proved outright:

* index types: `Ref` indexes covers/intersections by `Fin m`, `Agent074` by an
  arbitrary `ι` with `[Fintype ι]` — transported along `Fintype.equivFin`;
* the affine pieces are a family `g : Fin m → _` in `Ref` and an existential
  per piece in `Agent074` — transported by `choose`;
* `c + ∑ a j * x j` vs `(∑ a i * x i) + b`, and `{x | ∀ i, _ ≤ _}` vs
  `⋂ i, {x | _ ≤ _}`.

Crucially `Agent074.ReLUn` is *at most* `k` hidden layers, like the reference,
so no padding identity is needed and `relun` is a plain induction.  No `sorry`.
-/

namespace Star_074

/-- The two affine-functional predicates agree (only `add_comm` separates them). -/
private lemma isAffine_iff {n : ℕ} (g : (Fin n → ℝ) → ℝ) :
    Agent074.IsAffineFun n g ↔ Ref.IsAffine g := by
  constructor
  · rintro ⟨a, c, h⟩
    exact ⟨a, c, fun x => by rw [h x]; ring⟩
  · rintro ⟨a, b, h⟩
    exact ⟨a, b, fun x => by rw [h x]; ring⟩

/-- The two polyhedron predicates agree: a `Fintype`-indexed system of affine
inequalities is the same thing as a finite intersection of halfspaces. -/
private lemma isPolyhedron_iff {n : ℕ} (S : Set (Fin n → ℝ)) :
    Agent074.IsPolyhedron n S ↔ Ref.IsPolyhedron n S := by
  constructor
  · rintro ⟨ι, hι, a, b, rfl⟩
    haveI : Fintype ι := hι
    have e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
    refine ⟨Fintype.card ι,
      fun i => {x | ∑ j, a (e.symm i) j * x j ≤ b (e.symm i)},
      fun i => ⟨a (e.symm i), b (e.symm i), rfl⟩, ?_⟩
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact ⟨fun h i => h (e.symm i), fun h i => by simpa using h (e i)⟩
  · rintro ⟨m, H, hH, rfl⟩
    classical
    choose a b hab using hH
    refine ⟨Fin m, inferInstance, a, b, ?_⟩
    ext x
    simp only [hab, Set.mem_iInter, Set.mem_setOf_eq]

/-- Membership in the two `CPWL` sets is the same condition. -/
private lemma cpwl_mem_iff {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    f ∈ Agent074.CPWL n ↔ f ∈ Ref.CPWL n := by
  constructor
  · rintro ⟨hc, ι, hι, P, hP, hcov, hg⟩
    haveI : Fintype ι := hι
    classical
    choose g hg1 hg2 using hg
    have e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
    refine ⟨hc, Fintype.card ι, fun i => P (e.symm i), fun i => g (e.symm i),
      fun i => (isPolyhedron_iff _).mp (hP _), fun i => (isAffine_iff _).mp (hg1 _), ?_,
      fun i x hx => hg2 (e.symm i) hx⟩
    rw [← hcov]
    ext x
    simp only [Set.mem_iUnion]
    exact ⟨fun ⟨i, hi⟩ => ⟨_, hi⟩, fun ⟨i, hi⟩ => ⟨e i, by simpa using hi⟩⟩
  · rintro ⟨hc, m, P, g, hP, hg, hcov, hfg⟩
    exact ⟨hc, Fin m, inferInstance, P, fun i => (isPolyhedron_iff _).mpr (hP i), hcov,
      fun i => ⟨g i, (isAffine_iff _).mpr (hg i), fun x hx => hfg i x hx⟩⟩

theorem cpwl (n : ℕ) : Agent074.CPWL n = Ref.CPWL n :=
  Set.ext fun f => cpwl_mem_iff f

/-- The reference's `ComputedBy` (an unfolded existential recursion) and
`Agent074`'s inductive `ReLUNet` describe the same functions, layer for layer.
The affine-map structures and both `reluVec`s are definitionally equal, so each
step is `rfl` after the induction hypothesis. -/
private lemma computedBy_iff (k : ℕ) : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Ref.ComputedBy n k f ↔ ∃ net : Agent074.ReLUNet n k, f = net.eval := by
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨T, hT⟩
      exact ⟨Agent074.ReLUNet.output ⟨T.M, T.c⟩, funext hT⟩
    · rintro ⟨net, rfl⟩
      cases net with
      | output T => exact ⟨⟨T.A, T.bias⟩, fun _ => rfl⟩
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, T, g, hg, hf⟩
      obtain ⟨net, rfl⟩ := (ih m g).mp hg
      exact ⟨Agent074.ReLUNet.layer ⟨T.M, T.c⟩ net, funext hf⟩
    · rintro ⟨net, rfl⟩
      cases net with
      | layer T rest =>
        exact ⟨_, ⟨T.A, T.bias⟩, rest.eval, (ih _ _).mpr ⟨rest, rfl⟩, fun _ => rfl⟩

theorem relun (n k : ℕ) : Agent074.ReLUn n k = Ref.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨j, hj, net, rfl⟩
    exact ⟨j, hj, (computedBy_iff j n _).mpr ⟨net, rfl⟩⟩
  · rintro ⟨j, hj, h⟩
    obtain ⟨net, rfl⟩ := (computedBy_iff j n f).mp h
    exact ⟨j, hj, net, rfl⟩

/-- Both files write the depth bound as `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`, so
this is syntactically the same definition. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent074.depthBound n = Ref.depthBound n := rfl

private lemma depthBound_eq (n : ℕ) : Agent074.depthBound n = Ref.depthBound n := rfl

theorem statement :
    (∀ n, 3 ≤ n → Agent074.CPWL n = Agent074.ReLUn n (Agent074.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
  constructor
  · intro h n hn
    simpa [cpwl, relun, depthBound_eq] using h n hn
  · intro h n hn
    simpa [cpwl, relun, depthBound_eq] using h n hn

end Star_074

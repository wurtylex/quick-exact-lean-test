import QuickTest.Formalizations.Thm2_096
import QuickTest.Reference

namespace Star_096

/-!
# Star comparison: `Agent096` vs `Ref`

* `depthBound` is *literally* the same term (`⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`), so
  `depth` is `rfl`.
* `ReLUn` agrees: both files read `ReLUn n k` as **at most** `k` hidden layers.  The
  network predicates differ only in packaging — `Agent096` builds an indexed inductive
  chain `ReLUNet a b k` of affine maps, `Ref` uses the recursive predicate
  `ComputedBy`.  Peeling one layer at a time matches them; the induction is below.
* `CPWL` does **not** agree.  `Agent096.CPWL` demands agreement with one member of a
  finite affine family on a whole *neighbourhood* (`∀ᶠ y in nhds x`) of every point.
  On connected `ℝⁿ` that forces global affineness, so it is strictly stronger than the
  reference's polyhedral-cover condition.  Hence `cpwl` is false and we prove `cpwl_ne`.
* Consequently the `Agent096` reading of Theorem 2 is outright false: `agent_side_false`.
-/

/-! ### The network predicates agree -/

/-- The two componentwise ReLUs are the same function. -/
private lemma reluVec_eq {m : ℕ} (v : Fin m → ℝ) : Ref.reluVec v = Agent096.reluVec v := rfl

/-- `Agent096.NetComputesExact` and `Ref.ComputedBy` denote the same predicate: an
`Agent096` network with `k` hidden layers is exactly a `Ref` alternating composition of
`k + 1` affine maps. -/
private lemma exact_iff (k : ℕ) : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent096.NetComputesExact n k f ↔ Ref.ComputedBy n k f := by
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨N, hN⟩
      cases N with
      | last T => exact ⟨⟨T.A, T.c⟩, fun x => hN x⟩
    · rintro ⟨T, hT⟩
      exact ⟨.last ⟨T.M, T.c⟩, fun x => hT x⟩
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨N, hN⟩
      cases N with
      | step T rest =>
        refine ⟨_, ⟨T.A, T.c⟩, fun y => rest.eval y 0,
          (ih _ (fun y => rest.eval y 0)).1 ⟨rest, fun _ => rfl⟩, fun x => hN x⟩
    · rintro ⟨m, T, g, hg, hf⟩
      obtain ⟨M, hM⟩ := (ih m g).2 hg
      refine ⟨Agent096.ReLUNet.step (⟨T.M, T.c⟩ : Agent096.AffMap n m) M, fun x => ?_⟩
      rw [hf x, hM]
      first
        | rfl
        | simp only [Agent096.ReLUNet.eval, Agent096.AffMap.eval, Ref.Aff.eval,
            Ref.reluVec, Agent096.reluVec, Ref.relu, Agent096.relu]

theorem relun (n k : ℕ) : Agent096.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent096.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (exact_iff j n f).1 hf⟩
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (exact_iff j n f).2 hf⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent096.depthBound n = Ref.depthBound n := rfl

/-! ### `CPWL` disagrees: the neighbourhood reading rejects `relu` -/

/-- Every halfspace is a polyhedron (intersection of a one-element family). -/
private lemma poly_of_half {n : ℕ} {S : Set (Fin n → ℝ)} (h : Ref.IsHalfspace n S) :
    Ref.IsPolyhedron n S :=
  ⟨1, fun _ => S, fun _ => h, by rw [Set.iInter_const]⟩

/-- `x ↦ max 0 (x 0)` is CPWL in the reference sense: the two halflines cover `ℝ`. -/
private lemma witness_mem : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Ref.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2,
    ![{x : Fin 1 → ℝ | ∑ j, (1 : ℝ) * x j ≤ 0}, {x : Fin 1 → ℝ | ∑ j, (-1 : ℝ) * x j ≤ 0}],
    ![fun _ => 0, fun x => x 0], ?_, ?_, ?_, ?_⟩
  · exact Fin.forall_fin_two.2 ⟨poly_of_half ⟨fun _ => 1, 0, rfl⟩,
      poly_of_half ⟨fun _ => -1, 0, rfl⟩⟩
  · exact Fin.forall_fin_two.2 ⟨⟨0, 0, by simp⟩, ⟨fun _ => 1, 0, by simp⟩⟩
  · refine Set.eq_univ_of_forall fun x => ?_
    rcases le_or_gt (x 0) 0 with hx | hx
    · refine Set.mem_iUnion.2 ⟨0, ?_⟩
      simp only [Matrix.cons_val_zero, Set.mem_setOf_eq, Fin.sum_univ_one, one_mul]
      linarith
    · refine Set.mem_iUnion.2 ⟨1, ?_⟩
      simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, Set.mem_setOf_eq,
        Fin.sum_univ_one, neg_mul, one_mul]
      linarith
  · refine Fin.forall_fin_two.2 ⟨fun x hx => ?_, fun x hx => ?_⟩
    · simp only [Matrix.cons_val_zero, Set.mem_setOf_eq, Fin.sum_univ_one, one_mul] at hx ⊢
      exact max_eq_left (by linarith)
    · simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, Set.mem_setOf_eq,
        Fin.sum_univ_one, neg_mul, one_mul] at hx ⊢
      exact max_eq_right (by linarith)

/-- `x ↦ max 0 (x 0)` is *not* in `Agent096.CPWL`: local agreement with a single affine
map at the origin forces `max 0 t = a * t + b` on a whole interval around `0`, which the
kink at `0` forbids. -/
private lemma witness_not_mem (n : ℕ) :
    (fun x : Fin (n + 1) → ℝ => max 0 (x 0)) ∉ Agent096.CPWL (n + 1) := by
  rintro ⟨-, m, g, hg⟩
  obtain ⟨i, hi⟩ := hg (fun _ => (0 : ℝ))
  have htend : Filter.Tendsto (fun t : ℝ => (fun _ => t : Fin (n + 1) → ℝ))
      (nhds 0) (nhds (fun _ => (0 : ℝ))) :=
    (continuous_pi fun _ => continuous_id).tendsto 0
  have key : ∀ᶠ t : ℝ in nhds 0,
      max 0 t = (∑ j, (g i).A 0 j) * t + (g i).c 0 := by
    filter_upwards [htend.eventually hi] with t ht
    simpa [Agent096.AffMap.eval, Matrix.mulVec, dotProduct, Finset.sum_mul] using ht
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 key
  have h0 : max (0 : ℝ) 0 = (∑ j, (g i).A 0 j) * 0 + (g i).c 0 := by
    refine hball ?_
    simpa using hε
  have hp : max (0 : ℝ) (ε / 2) = (∑ j, (g i).A 0 j) * (ε / 2) + (g i).c 0 := by
    refine hball ?_
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
    linarith
  have hm : max (0 : ℝ) (-(ε / 2)) = (∑ j, (g i).A 0 j) * (-(ε / 2)) + (g i).c 0 := by
    refine hball ?_
    rw [Real.dist_eq, sub_zero, abs_of_neg (by linarith)]
    linarith
  rw [max_self] at h0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ ε / 2)] at hp
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0 : ℝ))] at hm
  have hring : (∑ j, (g i).A 0 j) * (ε / 2) + (∑ j, (g i).A 0 j) * (-(ε / 2)) = 0 := by
    ring
  have hzero : (∑ j, (g i).A 0 j) * (0 : ℝ) = 0 := by ring
  linarith

/-- `Agent096.CPWL` is strictly stronger than `Ref.CPWL`; they already differ at `n = 1`,
witnessed by `x ↦ max 0 (x 0)`. -/
theorem cpwl_ne : ∃ n, Agent096.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => witness_not_mem 0 ?_⟩
  rw [h]
  exact witness_mem

/-! ### The `Agent096` reading of Theorem 2 is false outright -/

/-- `x ↦ max 0 (x 0)` on `ℝ³` is computed by a network with exactly one hidden layer. -/
private lemma relu3_computes :
    Agent096.NetComputesExact 3 1 (fun x : Fin 3 → ℝ => max 0 (x 0)) := by
  refine ⟨Agent096.ReLUNet.step
      (⟨Matrix.of fun _ j => if j = 0 then (1 : ℝ) else 0, 0⟩ : Agent096.AffMap 3 1)
      (Agent096.ReLUNet.last (⟨Matrix.of fun _ _ => (1 : ℝ), 0⟩ : Agent096.AffMap 1 1)),
    fun x => ?_⟩
  simp [Agent096.ReLUNet.eval, Agent096.AffMap.eval, Agent096.reluVec, Agent096.relu,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_one]

/-- The `Agent096` reading of Theorem 2 is false: `relu` of a coordinate is a
one-hidden-layer network, but the neighbourhood-agreement `CPWL` rejects it. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent096.CPWL n = Agent096.ReLUn n (Agent096.depthBound n)) := by
  intro h
  refine witness_not_mem 2 ?_
  rw [h 3 (by norm_num)]
  exact ⟨1, Nat.le_add_left 1 _, relu3_computes⟩

/-- The two readings are *not* equivalent: the left side is false (`agent_side_false`)
while the right side is the genuine Theorem 2, which is true.  Honest `sorry`: closing it
needs the truth of `Ref.theorem2`, which is itself `sorry`-ed, and routing through it is
forbidden. -/
theorem statement_ne :
    ¬ ((∀ n, 3 ≤ n → Agent096.CPWL n = Agent096.ReLUn n (Agent096.depthBound n)) ↔
      (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n))) := by
  intro hiff
  exact agent_side_false (hiff.2 (by sorry))

end Star_096

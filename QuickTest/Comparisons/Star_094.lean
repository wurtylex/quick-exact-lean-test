import QuickTest.Formalizations.Thm2_094
import QuickTest.Reference

/-!
# Star comparison 094 vs. the reference

`Agent094.ReLUn` and `Ref.ReLUn` agree (both are "at most `k`" hidden layers,
differing only in how an affine map is packaged), and `depthBound` is literally
the same term.  `Agent094.CPWL`, however, is *neighbourhood agreement*:

    ∀ x, ∃ i, ∃ U ∈ nhds x, Set.EqOn f (g i) U

with a finite family of affine `g i`.  That is strictly stronger than the
reference's polyhedral-cover condition — on connected `ℝⁿ` it forces `f` to be
globally affine — so `cpwl` is refuted and the agent's Theorem 2 is outright
false (`agent_side_false`).
-/

namespace Star_094

/-! ### The kink obstruction for the agent's `CPWL` -/

/-- `x ↦ max 0 (x i₀)` is never in the agent's neighbourhood-agreement `CPWL`:
agreement with an affine map near `0` is contradicted by the kink at `0`. -/
private lemma not_mem_agent_cpwl {n : ℕ} (i0 : Fin n) :
    (fun x : Fin n → ℝ => max 0 (x i0)) ∉ Agent094.CPWL n := by
  rintro ⟨-, m, g, hg, hcov⟩
  obtain ⟨i, U, hU, hEq⟩ := hcov 0
  obtain ⟨a, c, hgi⟩ := hg i
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  have hsum : ∀ t : ℝ, (∑ j, a j * (if j = i0 then t else 0)) = a i0 * t := by
    intro t
    rw [Finset.sum_eq_single i0]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ i0) h
  have key : ∀ t : ℝ, |t| < ε → max 0 t = c + a i0 * t := by
    intro t ht
    have hmem : (fun j => if j = i0 then t else 0 : Fin n → ℝ) ∈
        Metric.ball (0 : Fin n → ℝ) ε := by
      rw [Metric.mem_ball, dist_pi_lt_iff hε]
      intro j
      by_cases hj : j = i0
      · simpa [hj, Real.dist_eq] using ht
      · simpa [hj] using hε
    have hx := hEq (hball hmem)
    rw [hgi] at hx
    simpa [hsum] using hx
  have h0 := key 0 (by simpa using hε)
  have hp := key (ε / 2) (by rw [abs_of_pos (by linarith)]; linarith)
  have hm := key (-(ε / 2)) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
  rw [max_self] at h0
  have hc : c = 0 := by simpa using h0.symm
  rw [max_eq_right (by linarith : (0:ℝ) ≤ ε / 2)] at hp
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0:ℝ)), mul_neg] at hm
  rw [hc] at hp hm
  linarith

/-! ### The same function *is* in the reference `CPWL` -/

private lemma poly_of_half {S : Set (Fin 1 → ℝ)} (h : Ref.IsHalfspace 1 S) :
    Ref.IsPolyhedron 1 S :=
  ⟨1, fun _ => S, fun _ => h, (Set.iInter_const S).symm⟩

/-- `x ↦ max 0 (x 0)` is CPWL in the reference sense: the two halfspaces
`{x 0 ≤ 0}` and `{-x 0 ≤ 0}` cover `ℝ`, with pieces `0` and `x 0`. -/
private lemma mem_ref : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Ref.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2,
    ![{x | x 0 ≤ 0}, {x | -(x 0) ≤ 0}], ![fun _ => 0, fun x => x 0], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · show Ref.IsPolyhedron 1 {x : Fin 1 → ℝ | x 0 ≤ 0}
      exact poly_of_half ⟨fun _ => 1, 0, by ext x; simp⟩
    · show Ref.IsPolyhedron 1 {x : Fin 1 → ℝ | -(x 0) ≤ 0}
      exact poly_of_half ⟨fun _ => -1, 0, by ext x; simp⟩
  · intro i
    fin_cases i
    · exact ⟨0, 0, by intro x; simp⟩
    · exact ⟨fun _ => 1, 0, by intro x; simp⟩
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    rcases le_or_gt (x 0) 0 with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, neg_nonpos.mpr h.le⟩
  · intro i x hx
    fin_cases i
    · show max 0 (x 0) = (0:ℝ)
      exact max_eq_left (hx : x 0 ≤ 0)
    · show max 0 (x 0) = x 0
      exact max_eq_right (by have h : -(x 0) ≤ 0 := hx; linarith)

/-- The two `CPWL` predicates differ: neighbourhood agreement is strictly
stronger than a polyhedral cover. -/
theorem cpwl_ne : ∃ n, Agent094.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => not_mem_agent_cpwl (n := 1) 0 ?_⟩
  rw [h]
  exact mem_ref

/-! ### The agent's Theorem 2 is false on its own terms -/

private def A1 : Matrix (Fin 1) (Fin 3) ℝ := fun _ j => if j = 0 then 1 else 0

/-- At `n = 3` the one-hidden-layer network `x ↦ relu (x 0)` lies in
`ReLUn 3 (depthBound 3)` but not in the agent's `CPWL 3`. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent094.CPWL n = Agent094.ReLUn n (Agent094.depthBound n)) := by
  intro h
  have hmem : (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈
      Agent094.ReLUn 3 (Agent094.depthBound 3) := by
    refine ⟨1, ?_, ?_⟩
    · simp only [Agent094.depthBound]; omega
    · refine ⟨1, A1, 0, fun y => y 0, ?_, ?_⟩
      · show Agent094.IsAffine 1 (fun y : Fin 1 → ℝ => y 0)
        exact ⟨fun _ => 1, 0, by funext y; simp⟩
      · funext x
        have hA : A1.mulVec x 0 = x 0 := by
          show ∑ j, (if j = 0 then (1:ℝ) else 0) * x j = x 0
          simp [Fin.sum_univ_three]
        simp [Agent094.reluVec, Agent094.relu, Agent094.affineApply, hA]
  rw [← h 3 le_rfl] at hmem
  exact not_mem_agent_cpwl (n := 3) 0 hmem

/-! ### `ReLUn` and `depthBound` do agree -/

/-- Both files read "exactly `k` hidden layers" the same way; the only
difference is that the reference bundles the matrix and the bias into `Aff`,
and states the base case pointwise instead of as a function equality. -/
private lemma computed_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent094.ComputedWithHiddenLayers n k f ↔ Ref.ComputedBy n k f := by
  intro k
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨a, c, hf⟩
      refine ⟨⟨fun _ j => a j, fun _ => c⟩, fun x => ?_⟩
      rw [hf]
      show c + ∑ i, a i * x i = (∑ j, a j * x j) + c
      ring
    · rintro ⟨T, hT⟩
      refine ⟨fun j => T.M 0 j, T.c 0, funext fun x => ?_⟩
      rw [hT x]
      show (∑ j, T.M 0 j * x j) + T.c 0 = T.c 0 + ∑ i, T.M 0 i * x i
      ring
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, A, c, g, hg, hf⟩
      exact ⟨m, ⟨A, c⟩, g, (ih m g).1 hg, fun x => congrFun hf x⟩
    · rintro ⟨m, T, g, hg, hf⟩
      exact ⟨m, T.M, T.c, g, (ih m g).2 hg, funext fun x => hf x⟩

theorem relun (n k : ℕ) : Agent094.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent094.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  exact exists_congr fun j => and_congr_right fun _ => computed_iff j n f

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent094.depthBound n = Ref.depthBound n := rfl

/-- The forward implication of `statement` holds vacuously: its hypothesis is
refuted by `agent_side_false`. -/
theorem statement_mp :
    (∀ n, 3 ≤ n → Agent094.CPWL n = Agent094.ReLUn n (Agent094.depthBound n)) →
      (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) :=
  fun h => absurd h agent_side_false

/-- The agent side is false and the reference side is the (true) paper theorem,
so this iff is in fact false; but refuting it means *proving* `Ref.theorem2`,
which is `sorry`-ed there and is the hard content of the paper.  Honest gap. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent094.CPWL n = Agent094.ReLUn n (Agent094.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_094

import QuickTest.Formalizations.Thm2_025
import QuickTest.Reference

namespace Star_025

/-!
`Agent025` defines `CPWL` by **local agreement on a neighbourhood** with a finite
family of affine functions.  That condition forces global affineness on the
connected space `ℝⁿ`, so it is strictly stronger than the reference's polyhedral
`CPWL`.  We therefore refute `cpwl`, and prove the stronger `agent_side_false`.
-/

/-- The depth bounds are literally the same expression. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent025.depthBound n = Ref.depthBound n := rfl

/-! ### The witness `x ↦ max 0 (x 0)` -/

/-- The witness function on `ℝ^(n+1)`. -/
private noncomputable def F (n : ℕ) : (Fin (n + 1) → ℝ) → ℝ := fun x => max 0 (x 0)

/-- The affine map `ℝ^(n+1) → ℝ^1` reading off coordinate `0`. -/
private def proj0 (n : ℕ) : Agent025.AffineMap (n + 1) 1 :=
  ⟨fun _ j => if j = 0 then 1 else 0, fun _ => 0⟩

private lemma proj0_apply (n : ℕ) (x : Fin (n + 1) → ℝ) :
    (proj0 n).apply x 0 = x 0 := by
  simp [proj0, Agent025.AffineMap.apply, ite_mul, Finset.sum_ite_eq']

/-! ### `F n` is computed by a ReLU network with any positive number of layers -/

/-- `relu (relu t) = relu t` lets us pad a one-hidden-layer network to any depth. -/
private lemma net_F : ∀ (k n : ℕ), Agent025.NetworkComputable (n + 1) (k + 1) (F n) := by
  intro k
  induction k with
  | zero =>
      intro n
      refine ⟨1, proj0 n, fun y => y 0, ⟨⟨fun _ _ => 1, fun _ => 0⟩, ?_⟩, ?_⟩
      · intro y
        simp [Agent025.AffineMap.apply, Fin.sum_univ_one]
      · intro x
        show max 0 (x 0) = Agent025.reluVec ((proj0 n).apply x) 0
        simp [Agent025.reluVec, Agent025.relu, proj0_apply]
  | succ k ih =>
      intro n
      refine ⟨1, proj0 n, F 0, ih 0, ?_⟩
      intro x
      show max 0 (x 0) = max 0 (Agent025.reluVec ((proj0 n).apply x) 0)
      have h : Agent025.reluVec ((proj0 n).apply x) 0 = max 0 (x 0) := by
        simp [Agent025.reluVec, Agent025.relu, proj0_apply]
      rw [h, max_eq_right (le_max_left (0 : ℝ) (x 0))]

/-! ### `F n` is *not* in `Agent025.CPWL` -/

/-- The curve `t ↦ t · e₀` through the origin. -/
private def e (n : ℕ) (t : ℝ) : Fin (n + 1) → ℝ := fun j => if j = 0 then t else 0

private lemma e_cont (n : ℕ) : Continuous (e n) := by
  refine continuous_pi fun j => ?_
  by_cases h : j = 0
  · simp only [e, if_pos h]
    exact continuous_id
  · simp only [e, if_neg h]
    exact continuous_const

private lemma e_zero (n : ℕ) : e n 0 = 0 := by
  funext j
  simp [e]

/-- Neighbourhood-agreement with a single affine map fails at the kink of `max 0 (·)`. -/
private lemma F_not_cpwl (n : ℕ) : F n ∉ Agent025.CPWL (n + 1) := by
  rintro ⟨-, m, g, hg, hcover⟩
  obtain ⟨i, hi⟩ := hcover 0
  obtain ⟨a, c, ha⟩ := hg i
  have htend : Filter.Tendsto (e n) (nhds 0) (nhds 0) := by
    have h := (e_cont n).tendsto 0
    rwa [e_zero] at h
  have hev := htend.eventually hi
  have hev2 : ∀ᶠ t : ℝ in nhds 0, max 0 t = a 0 * t + c := by
    filter_upwards [hev] with t ht
    rw [ha] at ht
    simpa [F, e, mul_ite, Finset.sum_ite_eq'] using ht
  rw [Metric.eventually_nhds_iff] at hev2
  obtain ⟨ε, hε, H⟩ := hev2
  have hc : c = 0 := by
    have h := H (show dist (0 : ℝ) 0 < ε by simpa using hε)
    rw [max_self, mul_zero, zero_add] at h
    exact h.symm
  have hpos : (0 : ℝ) < ε / 2 := by linarith
  have h1 := H (show dist (ε / 2) (0 : ℝ) < ε by
    rw [Real.dist_eq, sub_zero, abs_of_pos hpos]; linarith)
  have h2 := H (show dist (-(ε / 2)) (0 : ℝ) < ε by
    rw [Real.dist_eq, sub_zero, abs_of_neg (by linarith : -(ε / 2) < 0)]; linarith)
  rw [hc, add_zero, max_eq_right hpos.le] at h1
  rw [hc, add_zero, max_eq_left (by linarith : -(ε / 2) ≤ 0), mul_neg] at h2
  linarith

/-! ### `F 0` *is* in the reference `CPWL 1` -/

private lemma half_poly (S : Set (Fin 1 → ℝ)) (h : Ref.IsHalfspace 1 S) :
    Ref.IsPolyhedron 1 S :=
  ⟨1, fun _ => S, fun _ => h, (Set.iInter_const _).symm⟩

private lemma F_mem_ref : F 0 ∈ Ref.CPWL 1 := by
  refine ⟨?_, 2,
    ![{x : Fin 1 → ℝ | (∑ i, (1 : ℝ) * x i) ≤ 0}, {x : Fin 1 → ℝ | (∑ i, (-1 : ℝ) * x i) ≤ 0}],
    ![fun _ => (0 : ℝ), fun x => x 0], ?_, ?_, ?_, ?_⟩
  · show Continuous fun x : Fin 1 → ℝ => max 0 (x 0)
    exact continuous_const.max (continuous_apply 0)
  · intro i
    fin_cases i
    · show Ref.IsPolyhedron 1 {x : Fin 1 → ℝ | (∑ i, (1 : ℝ) * x i) ≤ 0}
      exact half_poly _ ⟨fun _ => 1, 0, rfl⟩
    · show Ref.IsPolyhedron 1 {x : Fin 1 → ℝ | (∑ i, (-1 : ℝ) * x i) ≤ 0}
      exact half_poly _ ⟨fun _ => -1, 0, rfl⟩
  · intro i
    fin_cases i
    · exact ⟨fun _ => 0, 0, fun x => by simp⟩
    · exact ⟨fun _ => 1, 0, fun x => by simp⟩
  · rw [Set.eq_univ_iff_forall]
    intro x
    rcases le_total (x 0) 0 with h | h
    · refine Set.mem_iUnion.2 ⟨0, ?_⟩
      show (∑ i, (1 : ℝ) * x i) ≤ 0
      simpa using h
    · refine Set.mem_iUnion.2 ⟨1, ?_⟩
      show (∑ i, (-1 : ℝ) * x i) ≤ 0
      simpa using h
  · intro i
    fin_cases i
    · intro x hx
      have h1 : (∑ i, (1 : ℝ) * x i) ≤ 0 := hx
      have hx' : x 0 ≤ 0 := by simpa using h1
      show max 0 (x 0) = 0
      exact max_eq_left hx'
    · intro x hx
      have h1 : (∑ i, (-1 : ℝ) * x i) ≤ 0 := hx
      have hx' : (0 : ℝ) ≤ x 0 := by simpa using h1
      show max 0 (x 0) = x 0
      exact max_eq_right hx'

/-! ### The obligations -/

/-- `Agent025.CPWL` is strictly stronger than `Ref.CPWL`: `max 0 (x 0)` separates them. -/
theorem cpwl_ne : ∃ n, Agent025.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => F_not_cpwl 0 ?_⟩
  rw [h]
  exact F_mem_ref

/-- The agent's own Theorem 2 is false: `max 0 (x 0)` is a `2`-hidden-layer ReLU
network on `ℝ³` that fails the agent's neighbourhood-agreement `CPWL`. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent025.CPWL n = Agent025.ReLUn n (Agent025.depthBound n)) := by
  intro h
  have h3 := h 3 (by norm_num)
  have hmem : F 2 ∈ Agent025.ReLUn 3 (Agent025.depthBound 3) := by
    unfold Agent025.depthBound
    exact net_F _ 2
  rw [← h3] at hmem
  exact F_not_cpwl 2 hmem

-- `Agent025.ReLUn` is "exactly k" layers, `Ref.ReLUn` is "at most k"; they agree only
-- via the padding identity `x = relu x - relu (-x)`, which is a genuine theorem.
theorem relun (n k : ℕ) : Agent025.ReLUn n k = Ref.ReLUn n k := sorry

-- `agent_side_false` makes the LHS `False`, so `statement` is equivalent to the negation
-- of the reference Theorem 2 — refuting it would require proving Theorem 2 itself.
theorem statement :
    (∀ n, 3 ≤ n → Agent025.CPWL n = Agent025.ReLUn n (Agent025.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_025

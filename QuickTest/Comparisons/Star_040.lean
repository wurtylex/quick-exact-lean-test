import QuickTest.Formalizations.Thm2_040
import QuickTest.Reference

namespace Star_040

/-! ### Depth bound

`Agent040.depthBound` and `Ref.depthBound` are literally the same expression
`⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`, so the comparison is definitional. -/

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent040.depthBound n = Ref.depthBound n := rfl

/-! ### `CPWL` : the agent's definition is the neighbourhood-agreement one

`Agent040.CPWL n` asks for a *finite* family `S` of affine maps such that every
point has a neighbourhood on which `f` agrees with a member of `S`.  On connected
`ℝⁿ` this forces `f` to be globally affine, so it is strictly stronger than the
reference's polyhedral-cover definition. -/

/-- The ramp `x ↦ max 0 (xᵢ)` is not in the agent's `CPWL`: local agreement with an
affine map at the origin is impossible because of the kink. -/
private lemma ramp_not_mem_agent {n : ℕ} (i : Fin n) :
    (fun x : Fin n → ℝ => max 0 (x i)) ∉ Agent040.CPWL n := by
  rintro ⟨-, S, hS⟩
  obtain ⟨T, -, hT⟩ := hS (fun _ => 0)
  have hcont : Continuous (fun t : ℝ => (fun _ => t : Fin n → ℝ)) :=
    continuous_pi fun _ => continuous_id
  have htend : Filter.Tendsto (fun t : ℝ => (fun _ => t : Fin n → ℝ))
      (nhds 0) (nhds (fun _ => 0)) := by simpa using hcont.tendsto (0 : ℝ)
  have hT' : ∀ᶠ t : ℝ in nhds (0 : ℝ),
      max 0 t = (∑ j, T.A 0 j) * t + T.c 0 := by
    filter_upwards [htend.eventually hT] with t ht
    simpa [Agent040.Affine.eval, Finset.sum_mul] using ht
  rw [Metric.eventually_nhds_iff] at hT'
  obtain ⟨ε, hε, hball⟩ := hT'
  have h0 := hball (y := (0 : ℝ)) (by simpa using hε)
  have hp := hball (y := ε / 2)
    (by rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
  have hm := hball (y := -(ε / 2))
    (by rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by linarith)]; linarith)
  rw [max_self] at h0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ ε / 2)] at hp
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0 : ℝ))] at hm
  linarith

private def H0 : Set (Fin 1 → ℝ) := {x | (∑ i, (1 : ℝ) * x i) ≤ 0}
private def H1 : Set (Fin 1 → ℝ) := {x | (∑ i, (-1 : ℝ) * x i) ≤ 0}

private lemma H0_mem {x : Fin 1 → ℝ} : x ∈ H0 ↔ x 0 ≤ 0 := by simp [H0]
private lemma H1_mem {x : Fin 1 → ℝ} : x ∈ H1 ↔ 0 ≤ x 0 := by simp [H1]

/-- The same ramp *is* in the reference `CPWL`: the two halflines are polyhedra and
`f` is affine on each. -/
private lemma ramp_mem_ref : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Ref.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2, ![H0, H1],
    ![fun _ => 0, fun x => x 0], ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨1, fun _ => ![H0, H1] i, fun _ => ?_, ?_⟩
    · fin_cases i
      · exact ⟨fun _ => 1, 0, rfl⟩
      · exact ⟨fun _ => -1, 0, rfl⟩
    · exact Set.Subset.antisymm (Set.subset_iInter fun _ => subset_rfl)
        (Set.iInter_subset _ 0)
  · intro i
    fin_cases i
    · exact ⟨fun _ => 0, 0, fun x => by simp⟩
    · exact ⟨fun _ => 1, 0, fun x => by simp⟩
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    rcases le_total (x 0) 0 with h | h
    · exact ⟨0, H0_mem.2 h⟩
    · exact ⟨1, H1_mem.2 h⟩
  · intro i x hx
    fin_cases i
    · exact max_eq_left (H0_mem.1 hx)
    · exact max_eq_right (H1_mem.1 hx)

/-- The agent's `CPWL` is **not** the reference `CPWL`. -/
theorem cpwl_ne : ∃ n, Agent040.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => ramp_not_mem_agent (0 : Fin 1) ?_⟩
  rw [h]
  exact ramp_mem_ref

/-! ### The bonus obligation : the agent's Theorem 2 is outright false -/

private lemma max_zero_idem (a : ℝ) : max 0 (max 0 a) = max 0 a := by
  rw [← max_assoc, max_self]

private lemma ceil_logb_two : ⌈Real.logb 3 (2 : ℝ)⌉₊ = 1 := by
  have hpos : 0 < Real.logb 3 (2 : ℝ) := Real.logb_pos (by norm_num) (by norm_num)
  have hle : Real.logb 3 (2 : ℝ) ≤ 1 := by
    rw [show Real.logb 3 (2 : ℝ) = Real.log 2 / Real.log 3 from rfl,
      div_le_one (Real.log_pos (by norm_num))]
    gcongr <;> norm_num
  exact le_antisymm (Nat.ceil_le.mpr (by exact_mod_cast hle)) (Nat.ceil_pos.mpr hpos)

private lemma depthBound_three : Agent040.depthBound 3 = 2 := by
  have h : Agent040.depthBound 3 = ⌈Real.logb 3 (2 : ℝ)⌉₊ + 1 := by
    unfold Agent040.depthBound; norm_num
  rw [h, ceil_logb_two]

/-- `x ↦ max 0 (x 0)` on `ℝ³` is computed by a ReLU network with exactly two hidden
layers: pick out `x 0`, then let the second layer re-apply `relu` (idempotent). -/
private lemma ramp_net2 :
    Agent040.NetworkComputes 2 3 (fun x : Fin 3 → ℝ => max 0 (x 0)) := by
  refine ⟨1, ⟨fun _ j => if j = 0 then (1 : ℝ) else 0, fun _ => 0⟩,
    fun y : Fin 1 → ℝ => max 0 (y 0), ?_, ?_⟩
  · refine ⟨1, ⟨fun _ _ => (1 : ℝ), fun _ => 0⟩, fun z : Fin 1 → ℝ => z 0, ?_, ?_⟩
    · exact ⟨⟨fun _ _ => (1 : ℝ), fun _ => 0⟩, fun z => by simp [Agent040.Affine.eval]⟩
    · intro y
      simp [Agent040.Affine.eval, Agent040.reluVec, Agent040.relu]
  · intro x
    simp [Agent040.Affine.eval, Agent040.reluVec, Agent040.relu, max_zero_idem]

/-- The agent's own Theorem 2 statement is false, independently of the reference:
at `n = 3` the function `x ↦ max 0 (x 0)` lies in `ReLUn 3 2` but not in `CPWL 3`. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent040.CPWL n = Agent040.ReLUn n (Agent040.depthBound n)) := by
  intro h
  have h3 := h 3 le_rfl
  rw [depthBound_three] at h3
  refine ramp_not_mem_agent (0 : Fin 3) ?_
  rw [h3]
  exact ramp_net2

/-! ### The remaining obligations -/

-- `Agent040.ReLUn n k` is "**exactly** `k` hidden layers", `Ref.ReLUn n k` is
-- "**at most** `k`".  These denote the same set, but only via the padding identity
-- `x = relu x - relu (-x)`, which is a real theorem and is not proved here.
theorem relun (n k : ℕ) : Agent040.ReLUn n k = Ref.ReLUn n k := sorry

-- The agent side of the biconditional is false (`agent_side_false`), so `statement`
-- is equivalent to the *negation* of the reference Theorem 2.  Deciding that needs
-- `Ref.theorem2`, which is itself `sorry`-ed; routing through it would prove nothing.
theorem statement :
    (∀ n, 3 ≤ n → Agent040.CPWL n = Agent040.ReLUn n (Agent040.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_040

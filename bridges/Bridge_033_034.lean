namespace Bridge_033_034

/-- The kink function `x ↦ max 0 (x 0)` on `Fin 1 → ℝ`, used to distinguish the two
agents' `CPWL` definitions: it is CPWL under Agent034's polyhedral-cover reading but
*not* under Agent033's "single open neighborhood" reading, since at `x = 0` no one
affine formula can hold on a full open neighborhood. -/
def kinkFun : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

theorem kink_mem034 : kinkFun ∈ Agent034.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2,
    fun i => if i = 0 then {x : Fin 1 → ℝ | x 0 ≤ 0} else {x | 0 ≤ x 0},
    fun i => if i = 0 then (fun _ : Fin 1 → ℝ => (0 : ℝ)) else (fun x => x 0),
    ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    rcases le_total (x 0) 0 with h | h
    · exact ⟨0, by simp only [if_pos rfl, Set.mem_setOf_eq]; exact h⟩
    · exact ⟨1, by
        simp only [if_neg (by decide : (1 : Fin 2) ≠ 0), Set.mem_setOf_eq]; exact h⟩
  · intro i
    by_cases hi : i = 0
    · subst hi
      refine ⟨1, fun _ _ => (1 : ℝ), fun _ => (0 : ℝ), ?_⟩
      ext x
      simp [if_pos rfl, Fin.forall_fin_one, Fin.sum_univ_one]
    · refine ⟨1, fun _ _ => (-1 : ℝ), fun _ => (0 : ℝ), ?_⟩
      ext x
      simp only [if_neg hi, Set.mem_setOf_eq, Fin.forall_fin_one, Fin.sum_univ_one]
      constructor <;> intro h <;> linarith
  · intro i
    by_cases hi : i = 0
    · subst hi
      refine ⟨0, 0, ?_⟩
      intro x; simp [if_pos rfl, Fin.sum_univ_one]
    · refine ⟨fun _ => 1, 0, ?_⟩
      intro x; simp [if_neg hi, Fin.sum_univ_one]
  · intro i x hx
    by_cases hi : i = 0
    · subst hi
      simp only [if_pos rfl] at hx ⊢
      simp [kinkFun, max_eq_left hx]
    · simp only [if_neg hi] at hx ⊢
      simp [kinkFun, max_eq_right hx]

theorem kink_not_mem033 : kinkFun ∉ Agent033.CPWL 1 := by
  rintro ⟨-, m, a, b, hloc⟩
  obtain ⟨i, U, hU, h0U, hUeq⟩ := hloc (fun _ => (0 : ℝ))
  have hcont : Continuous (fun t : ℝ => (fun _ : Fin 1 => t)) :=
    continuous_pi (fun _ => continuous_id)
  have hUopen : IsOpen ((fun t : ℝ => (fun _ : Fin 1 => t)) ⁻¹' U) := hU.preimage hcont
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUopen 0 h0U
  have e2 : (0 : ℝ) < ε / 2 := by linarith
  have hy0 : (fun _ : Fin 1 => (0 : ℝ)) ∈ U := h0U
  have hy1 : (fun _ : Fin 1 => (ε / 2 : ℝ)) ∈ U := hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos e2]; linarith)
  have hy2 : (fun _ : Fin 1 => (-ε / 2 : ℝ)) ∈ U := hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (by linarith : (-ε / 2 : ℝ) < 0)]
    linarith)
  have e0 := hUeq _ hy0
  have e1 := hUeq _ hy1
  have e2' := hUeq _ hy2
  have v0 : kinkFun (fun _ : Fin 1 => (0 : ℝ)) = 0 := by unfold kinkFun; simp
  have v1 : kinkFun (fun _ : Fin 1 => (ε / 2 : ℝ)) = ε / 2 := by
    unfold kinkFun; exact max_eq_right (le_of_lt e2)
  have v2 : kinkFun (fun _ : Fin 1 => (-ε / 2 : ℝ)) = 0 := by
    unfold kinkFun; exact max_eq_left (by linarith : (-ε / 2 : ℝ) ≤ 0)
  simp only [Fin.sum_univ_one, v0, v1, v2, mul_zero, zero_add] at e0 e1 e2'
  have hb : b i = 0 := by linarith
  rw [hb] at e1 e2'
  have hε2 : (ε / 2 : ℝ) ≠ 0 := ne_of_gt e2
  have hne : (-ε / 2 : ℝ) ≠ 0 := ne_of_lt (by linarith)
  have h1 : a i 0 = 1 := by
    have e1' : a i 0 * (ε / 2) = 1 * (ε / 2) := by linarith
    exact mul_right_cancel₀ hε2 e1'
  have h2 : a i 0 = 0 := by
    have e2'' : a i 0 * (-ε / 2) = 0 * (-ε / 2) := by linarith
    exact mul_right_cancel₀ hne e2''
  linarith

/-- Refutation: Agent033's `CPWL` (agreement with an affine piece on *some open
neighborhood* of each point) forces global affineness on the connected space `ℝⁿ`
by the argument above, whereas Agent034's `CPWL` (a genuine polyhedral partition,
closed pieces meeting at boundaries) admits real kinks such as `max 0 (x 0)`. -/
theorem cpwl_ne : ∃ n, Agent033.CPWL n ≠ Agent034.CPWL n := by
  refine ⟨1, fun h => kink_not_mem033 ?_⟩
  rw [h]; exact kink_mem034

/-- Both agents define `depthBound n` by the identical term
`⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`, so the two functions are definitionally equal. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent033.depthBound n = Agent034.depthBound n := by
  rfl

-- `relun`: both agents read `ReLUn n k` as "at most `k` hidden layers", but
-- Agent033 encodes a network as a recursive `Prop` (`ComputesReLU`, nested
-- existentials) while Agent034 encodes it as an inductive family `ReLUNet` with an
-- `eval` function. Showing the two sets of representable functions coincide needs an
-- explicit two-way translation between these encodings, by induction on the number
-- of layers; this is a real but substantial construction that is not attempted here.
theorem relun (n k : ℕ) : Agent033.ReLUn n k = Agent034.ReLUn n k := sorry

-- `statement`: deciding this iff would require knowing whether each agent's own
-- `theorem2` is actually true. Agent033's `CPWL` was just shown (via `cpwl_ne`'s
-- argument) to essentially collapse to globally affine functions, which strongly
-- suggests Agent033's `theorem2` is *false* for `n ≥ 3` (`ReLUn` contains the
-- non-affine `kinkFun`-like functions), while Agent034's is the genuine hard
-- direction of Theorem 2 from the paper. Resolving either side is out of scope here.
theorem statement :
    (∀ n, 3 ≤ n → Agent033.CPWL n = Agent033.ReLUn n (Agent033.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent034.CPWL n = Agent034.ReLUn n (Agent034.depthBound n)) := sorry

end Bridge_033_034

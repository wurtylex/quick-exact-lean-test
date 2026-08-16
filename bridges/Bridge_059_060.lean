namespace Bridge_059_060

/-- The one-dimensional "crease" function `x ↦ max 0 (x 0)`, used to
distinguish Agent059's polyhedral `CPWL` from Agent060's local-agreement
`CPWL` at `n = 1`. -/
def creaseFun : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

theorem depth (n : ℕ) (hn : 3 ≤ n) :
    Agent059.depthBound n = Agent060.depthBound n := by
  unfold Agent059.depthBound Agent060.depthBound
  rfl

theorem creaseFun_mem059 : creaseFun ∈ Agent059.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2,
    ![{x : Fin 1 → ℝ | x 0 ≤ 0}, {x : Fin 1 → ℝ | 0 ≤ x 0}],
    ![(fun _ : Fin 1 → ℝ => (0 : ℝ)), fun x => x 0], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact ⟨1, ![fun _ : Fin 1 => (1 : ℝ)], ![(0 : ℝ)], by
        ext x; simp [Fin.sum_univ_one, Fin.forall_fin_one]⟩
    · exact ⟨1, ![fun _ : Fin 1 => (-1 : ℝ)], ![(0 : ℝ)], by
        ext x; simp [Fin.sum_univ_one, Fin.forall_fin_one]⟩
  · intro i
    fin_cases i
    · exact ⟨fun _ => (0 : ℝ), 0, by intro x; simp⟩
    · exact ⟨fun _ => (1 : ℝ), 0, by intro x; simp [Fin.sum_univ_one]⟩
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    rcases le_total (x 0) 0 with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  · intro i
    fin_cases i
    · intro x hx
      simp at hx
      simp [creaseFun, max_eq_left hx]
    · intro x hx
      simp at hx
      simp [creaseFun, max_eq_right hx]

/-- Agent060's `CPWL` requires literal local agreement with a *single* affine
function on a whole open neighbourhood of every point, so `creaseFun`, which
genuinely creases at `x 0 = 0`, cannot belong: no affine `g` can equal it on
both a positive and a negative point near `0`. -/
theorem creaseFun_not_mem060 : creaseFun ∉ Agent060.CPWL 1 := by
  rintro ⟨-, S, hAff, hCover⟩
  obtain ⟨g, hgS, U, hU, h0U, hEqOn⟩ := hCover (fun _ => (0 : ℝ))
  obtain ⟨a, b, hgab⟩ := hAff g hgS
  have hcont : Continuous (fun t : ℝ => (fun _ : Fin 1 => t)) :=
    continuous_pi (fun _ => continuous_id)
  have hnhds : (fun t : ℝ => (fun _ : Fin 1 => t)) ⁻¹' U ∈ nhds (0 : ℝ) :=
    hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds h0U)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  set t : ℝ := ε / 2 with ht
  have htpos : 0 < t := by positivity
  have hmemt : t ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos htpos]; linarith
  have hmemnegt : -t ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero,
      abs_of_neg (show (-t : ℝ) < 0 by linarith)]
    linarith
  have hUt : (fun _ : Fin 1 => t) ∈ U := hball hmemt
  have hUnegt : (fun _ : Fin 1 => -t) ∈ U := hball hmemnegt
  have e0 : creaseFun (fun _ : Fin 1 => (0 : ℝ)) = g (fun _ : Fin 1 => (0 : ℝ)) := hEqOn h0U
  have et : creaseFun (fun _ : Fin 1 => t) = g (fun _ : Fin 1 => t) := hEqOn hUt
  have ent : creaseFun (fun _ : Fin 1 => -t) = g (fun _ : Fin 1 => -t) := hEqOn hUnegt
  rw [hgab] at e0 et ent
  simp only [creaseFun, Fin.sum_univ_one, mul_zero, zero_add, max_self] at e0 et ent
  have hb : b = 0 := e0.symm
  rw [hb, add_zero] at et ent
  rw [max_eq_right htpos.le] at et
  rw [max_eq_left (show (-t : ℝ) ≤ 0 by linarith)] at ent
  rw [mul_neg] at ent
  linarith [et, ent]

theorem cpwl_ne : ∃ n, Agent059.CPWL n ≠ Agent060.CPWL n := by
  refine ⟨1, fun hEq => creaseFun_not_mem060 ?_⟩
  rw [← hEq]
  exact creaseFun_mem059

/-- `relun`: proving `Agent059.ReLUn n k = Agent060.ReLUn n k` needs an
induction on `k` showing `Agent059.ReLURepresentable n k f ↔
Agent060.represents n k f`, translating between the two affine-map encodings
(a raw weight function vs. `Matrix.mulVec`) at every layer. Both classes use
the same "at most `k`" reading so the equivalence is plausible, but the
induction was not completed within the time budget for this bridge. -/
theorem relun (n k : ℕ) : Agent059.ReLUn n k = Agent060.ReLUn n k := by
  sorry

/-- `statement`: `cpwl_ne` shows Agent060's `CPWL` forces, by a connectedness
argument (any genuine crease defeats agreement with a single affine function
on a whole neighbourhood), essentially only affine functions into `CPWL n`,
so its right-hand side is presumably false in general. But resolving this
`iff` still requires knowing the truth value of the left-hand side, i.e. the
genuine unproved Theorem 2 for Agent059's faithful polyhedral `CPWL` — exactly
the open mathematical content neither agent proved (both `theorem2`s are
`sorry`). Not resolved here. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent059.CPWL n = Agent059.ReLUn n (Agent059.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent060.CPWL n = Agent060.ReLUn n (Agent060.depthBound n)) := by
  sorry

end Bridge_059_060

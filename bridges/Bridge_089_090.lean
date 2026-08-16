namespace Bridge_089_090

/-- Both agents encode `depthBound` with the literal identical formula
`⌈Real.logb 3 ((n:ℝ)-1)⌉₊ + 1`, so the two definitions are definitionally equal. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent089.depthBound n = Agent090.depthBound n := rfl

/-- Witness for `cpwl_ne`: `f1 x = max 0 (x 0)` (essentially `ReLU` on the first
coordinate) is CPWL in Agent090's polyhedral-subdivision sense but is *not* CPWL in
Agent089's "locally equal to one globally-fixed affine piece" sense, since near `x = 0`
no single affine `ℓ` can agree with `f1` on a whole neighbourhood (it must match both
`t ↦ t` for `t > 0` small and `t ↦ 0` for `t < 0` small). -/
private noncomputable def f1 : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

private theorem f1_mem_090 : f1 ∈ Agent090.CPWL 1 := by
  have hcont : Continuous f1 := continuous_const.max (continuous_apply 0)
  refine ⟨hcont, 2,
    ![[(⟨fun _ => (-1 : ℝ), 0⟩ : Agent090.Halfspace 1)],
      [(⟨fun _ => (1 : ℝ), 0⟩ : Agent090.Halfspace 1)]],
    ![(fun x : Fin 1 → ℝ => x 0), (fun _ => (0 : ℝ))],
    ?_, ?_, ?_⟩
  · intro j
    fin_cases j
    · exact ⟨fun _ => 1, 0, fun x => by simp [Matrix.cons_val_zero, Fin.sum_univ_one]⟩
    · exact ⟨fun _ => 0, 0, fun x => by simp [Matrix.cons_val_one, Fin.sum_univ_one]⟩
  · intro x
    rcases le_or_lt 0 (x 0) with h | h
    · refine ⟨0, ?_⟩
      simp only [Agent090.Polyhedron.mem, Agent090.Halfspace.mem, List.mem_singleton,
        forall_eq, Matrix.cons_val_zero, Fin.sum_univ_one]
      linarith
    · refine ⟨1, ?_⟩
      simp only [Agent090.Polyhedron.mem, Agent090.Halfspace.mem, List.mem_singleton,
        forall_eq, Matrix.cons_val_one, Fin.sum_univ_one]
      linarith
  · intro j x hx
    fin_cases j
    · simp only [Agent090.Polyhedron.mem, Agent090.Halfspace.mem, List.mem_singleton,
        forall_eq, Matrix.cons_val_zero, Fin.sum_univ_one] at hx
      simp only [f1, Matrix.cons_val_zero]
      exact max_eq_right (by linarith)
    · simp only [Agent090.Polyhedron.mem, Agent090.Halfspace.mem, List.mem_singleton,
        forall_eq, Matrix.cons_val_one, Fin.sum_univ_one] at hx
      simp only [f1, Matrix.cons_val_one]
      exact max_eq_left (by linarith)

private theorem f1_not_mem_089 : f1 ∉ Agent089.CPWL 1 := by
  rintro ⟨-, S, hS, hloc⟩
  obtain ⟨ℓ, hℓS, U, hUnhds, hUmem⟩ := hloc 0
  obtain ⟨a, b, hℓeq⟩ := hS ℓ hℓS
  have hb : b = 0 := by
    have h0 := hUmem 0 (mem_of_mem_nhds hUnhds)
    simp only [f1, Pi.zero_apply, max_self, hℓeq, Fin.sum_univ_one, mul_zero, zero_add] at h0
    linarith
  set φ : ℝ → (Fin 1 → ℝ) := fun t _ => t with hφdef
  have hφcont : Continuous φ := continuous_pi (fun _ => continuous_id)
  have hφ0 : φ 0 = 0 := by ext i; simp [hφdef]
  obtain ⟨V, hVU, hVopen, hV0⟩ := mem_nhds_iff.mp hUnhds
  have hpre : φ ⁻¹' V ∈ nhds (0 : ℝ) :=
    (hφcont.isOpen_preimage hVopen).mem_nhds (by rw [Set.mem_preimage, hφ0]; exact hV0)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  set t : ℝ := ε / 2 with htdef
  have ht_pos : 0 < t := by positivity
  have ht_ball : t ∈ Metric.ball (0 : ℝ) ε := by
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht_pos]; linarith
  have htm_ball : -t ∈ Metric.ball (0 : ℝ) ε := by
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_neg (by linarith : -t < (0:ℝ))]
    linarith
  have hUt : φ t ∈ U := hVU (hball ht_ball)
  have hUmt : φ (-t) ∈ U := hVU (hball htm_ball)
  have e1 := hUmem (φ t) hUt
  have e2 := hUmem (φ (-t)) hUmt
  simp only [f1, hφdef, hℓeq, Fin.sum_univ_one, hb, zero_add] at e1 e2
  rw [max_eq_right ht_pos.le] at e1
  rw [max_eq_left (show -t ≤ (0:ℝ) by linarith), mul_neg] at e2
  linarith [e1, e2]

theorem cpwl_ne : ∃ n, Agent089.CPWL n ≠ Agent090.CPWL n := by
  refine ⟨1, fun h => f1_not_mem_089 ?_⟩
  rw [h]
  exact f1_mem_090

/-- Both `ReLUn` definitions use the "at most `k` hidden layers" reading, via two
structurally isomorphic recursive network types (`Agent089.NNComputesExact` vs.
`Agent090.Network`/`Network.eval`). Establishing that isomorphism needs an induction on
the hidden-layer count `k` (simultaneously generalizing the input dimension `n`, since the
recursive step changes it), which is more than a "quick win" under this budget, so it is
left unproved here rather than risk an unchecked, possibly-wrong proof. -/
theorem relun (n k : ℕ) : Agent089.ReLUn n k = Agent090.ReLUn n k := by
  sorry

/-- Depends on both `cpwl` (which we refuted, so `Agent089.CPWL` is not the intended
CPWL family) and `relun` (left `sorry`); not attempted, and in any case cannot be proved
via either agent's `theorem2`. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent089.CPWL n = Agent089.ReLUn n (Agent089.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent090.CPWL n = Agent090.ReLUn n (Agent090.depthBound n)) := by
  sorry

end Bridge_089_090

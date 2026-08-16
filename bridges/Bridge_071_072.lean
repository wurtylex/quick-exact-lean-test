namespace Bridge_071_072

/-- Both agents define `depthBound n` by the identical formula
`⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1`, so the defs are definitionally equal. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) :
    Agent071.depthBound n = Agent072.depthBound n := rfl

/-- Agent071's `ReLUn` is built from `ComputesWithHiddenLayers` (an indexed family of
widths `w : Fin (k+2) → ℕ` with an explicit "last layer is affine, others ReLU" split),
while Agent072's is built from `IsReLUNet` (structural recursion peeling the input
layer). These are two different-looking "exactly k hidden layers" encodings; showing
them equivalent needs an induction reindexing the two recursive schemes against each
other, which is beyond the one-extra-obligation budget for this bridge. -/
theorem relun (n k : ℕ) : Agent071.ReLUn n k = Agent072.ReLUn n k := by
  sorry

/-- `statement` compares "Theorem 2 holds for Agent071" with "Theorem 2 holds for
Agent072". Since `cpwl` is refuted below (the two `CPWL` predicates are genuinely
different sets, see `cpwl_ne`), this iff is not obviously provable or refutable
without essentially deciding whether the informal Theorem 2 is true for each
formalization's own (differing) notion of `CPWL`, which is out of scope here. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent071.CPWL n = Agent071.ReLUn n (Agent071.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent072.CPWL n = Agent072.ReLUn n (Agent072.depthBound n)) := by
  sorry

/-- The witness function `x ↦ max 0 (x 0)` on `Fin 1 → ℝ`, i.e. the ReLU applied to
the single coordinate. It separates Agent071's "local agreement" `CPWL` from
Agent072's "polyhedral subdivision" `CPWL`. -/
noncomputable def hingeFun : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

/-- `hingeFun` is not locally affine at `0`: any neighbourhood of `0` contains points
of both signs in the first coordinate, and no single affine function can agree with
`hingeFun` on such a neighbourhood (a two-point argument at two different scales
pins down the affine coefficients inconsistently). -/
theorem hnot071 : hingeFun ∉ Agent071.CPWL 1 := by
  rintro ⟨-, m, g, hg_affine, hloc⟩
  obtain ⟨j, U, hU, heq⟩ := hloc (fun _ => (0 : ℝ))
  obtain ⟨a, b, hab⟩ := hg_affine j
  have hcq : Continuous (fun t : ℝ => (fun _ : Fin 1 => t)) :=
    continuous_pi fun _ => continuous_id
  have hpre : (fun t : ℝ => (fun _ : Fin 1 => t)) ⁻¹' U ∈ nhds (0 : ℝ) :=
    hcq.continuousAt.preimage_mem_nhds hU
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hpre
  have hball : ∀ t : ℝ, |t| < ε → (fun _ : Fin 1 => t) ∈ U := fun t ht =>
    hsub (show t ∈ Metric.ball (0 : ℝ) ε by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero]; exact ht)
  have h1 := heq (hball (ε / 4) (abs_lt.mpr ⟨by linarith, by linarith⟩))
  have h2 := heq (hball (-(ε / 4)) (abs_lt.mpr ⟨by linarith, by linarith⟩))
  have h3 := heq (hball (ε / 2) (abs_lt.mpr ⟨by linarith, by linarith⟩))
  simp only [hingeFun, hab, Fin.sum_univ_one] at h1 h2 h3
  rw [show max (0 : ℝ) (ε / 4) = ε / 4 from max_eq_right (by linarith)] at h1
  rw [show max (0 : ℝ) (-(ε / 4)) = 0 from max_eq_left (by linarith)] at h2
  rw [show max (0 : ℝ) (ε / 2) = ε / 2 from max_eq_right (by linarith)] at h3
  nlinarith [h1, h2, h3, hε]

/-- `hingeFun` is genuinely polyhedral-piecewise-affine: `{x0 ≤ 0}` and `{x0 ≥ 0}`
cover `ℝ` and `hingeFun` is affine (`0`, resp. `x0`) on each. -/
theorem hin072 : hingeFun ∈ Agent072.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2,
    ![{x : Fin 1 → ℝ | x 0 ≤ 0}, {x : Fin 1 → ℝ | 0 ≤ x 0}],
    ![fun _ : Fin 1 → ℝ => (0 : ℝ), fun x : Fin 1 → ℝ => x 0], ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact ⟨1, fun _ _ => 1, fun _ => 0, by
        ext x; simp [Fin.sum_univ_one, Fin.forall_fin_one]⟩
    · exact ⟨1, fun _ _ => -1, fun _ => 0, by
        ext x
        simp only [Set.mem_setOf_eq, Fin.forall_fin_one, Fin.sum_univ_one]
        constructor <;> intro h <;> linarith⟩
  · intro i; fin_cases i
    · exact ⟨0, 0, by funext x; simp⟩
    · exact ⟨fun _ => 1, 0, by funext x; simp [Fin.sum_univ_one]⟩
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    rcases le_total (x 0) 0 with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  · intro i; fin_cases i
    · intro x hx
      simp only [Set.mem_setOf_eq] at hx
      simp [hingeFun, max_eq_left hx]
    · intro x hx
      simp only [Set.mem_setOf_eq] at hx
      simp [hingeFun, max_eq_right hx]

/-- The two `CPWL` predicates disagree: `hingeFun` is polyhedral-CPWL (Agent072) but
fails Agent071's local-agreement condition at the origin, since no single affine
function can match a genuine "hinge" on any full neighbourhood of the kink. -/
theorem cpwl_ne : ∃ n, Agent071.CPWL n ≠ Agent072.CPWL n := by
  refine ⟨1, fun he => hnot071 ?_⟩
  rw [he]
  exact hin072

end Bridge_071_072

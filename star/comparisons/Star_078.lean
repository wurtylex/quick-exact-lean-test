namespace Star_078

/-!
# Comparison of `Agent078` against `Ref`

* `depthBound` is *literally* the same expression, so `depth` is `rfl`.
* `Agent078.CPWL` is the **local-agreement (nhds)** variant: a finite family of
  affine functions such that every point has a *neighbourhood* on which `f`
  agrees with one member.  On connected `ℝⁿ` this forces `f` to be globally
  affine, so it is strictly stronger than genuine CPWL.  Hence `cpwl` is false
  (`cpwl_ne`), and the agent's Theorem 2 is outright false (`agent_side_false`).
* `Agent078.ReLUn` uses a completely different (sequence-indexed) network
  encoding; equality with `Ref.ReLUn` is left as an honest `sorry`.
-/

/-- The depth bounds are syntactically identical. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent078.depthBound n = Ref.depthBound n := rfl

/-- Networks are encoded completely differently (`ℕ`-indexed sequences with a
`width` bookkeeping field vs. dependent `Fin`-typed affine maps); proving the two
sets equal needs a full translation between the encodings. -/
theorem relun (n k : ℕ) : Agent078.ReLUn n k = Ref.ReLUn n k := sorry

/-! ### The kink argument: `x ↦ max 0 (x i₀)` is not locally affine at `0`. -/

/-- A ReLU of a coordinate is never in the neighbourhood-agreement `CPWL`. -/
private lemma not_mem_agent_cpwl (n : ℕ) (i0 : Fin n) :
    (fun x : Fin n → ℝ => max 0 (x i0)) ∉ Agent078.CPWL n := by
  intro hmem
  obtain ⟨-, m, g, hg, hall⟩ := hmem
  obtain ⟨i, hi⟩ := hall 0
  obtain ⟨a, c, hac⟩ := hg i
  obtain ⟨e, he0, he1⟩ : ∃ e : Fin n → ℝ, e i0 = 1 ∧ ∀ j, j ≠ i0 → e j = 0 :=
    ⟨fun j => if j = i0 then 1 else 0, if_pos rfl, fun j hj => if_neg hj⟩
  have hcont : Continuous (fun t : ℝ => t • e) := continuous_id.smul continuous_const
  have htend : Filter.Tendsto (fun t : ℝ => t • e) (nhds (0 : ℝ)) (nhds (0 : Fin n → ℝ)) :=
    hcont.tendsto' 0 _ (by simp)
  have key : ∀ᶠ t : ℝ in nhds (0 : ℝ), max 0 t = a i0 * t + c := by
    filter_upwards [htend.eventually hi] with t ht
    have ht' : max 0 ((t • e) i0) = g i (t • e) := ht
    rw [Pi.smul_apply, smul_eq_mul, he0, mul_one] at ht'
    rw [ht', hac]
    congr 1
    rw [Finset.sum_eq_single i0
      (fun b _ hb => by rw [Pi.smul_apply, smul_eq_mul, he1 b hb]; ring)
      (fun h => absurd (Finset.mem_univ i0) h),
      Pi.smul_apply, smul_eq_mul, he0, mul_one]
  rw [Metric.eventually_nhds_iff] at key
  obtain ⟨ε, hε, hkey⟩ := key
  simp only [Real.dist_eq, sub_zero] at hkey
  have h0 := hkey (show |(0 : ℝ)| < ε by simpa using hε)
  have hp := hkey (show |ε / 2| < ε by rw [abs_of_pos (by linarith)]; linarith)
  have hm := hkey (show |(-(ε / 2) : ℝ)| < ε by rw [abs_of_neg (by linarith)]; linarith)
  rw [max_self] at h0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ ε / 2)] at hp
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0 : ℝ))] at hm
  linarith

/-! ### The same function *is* genuinely CPWL, for the reference definition. -/

/-- `x ↦ max 0 (x 0)` on `ℝ¹`, covered by the two halflines. -/
private lemma mem_ref_cpwl : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Ref.CPWL 1 := by
  have hpoly : ∀ (a : Fin 1 → ℝ) (b : ℝ),
      Ref.IsPolyhedron 1 {x : Fin 1 → ℝ | (∑ i, a i * x i) ≤ b} :=
    fun a b => ⟨1, fun _ => {x : Fin 1 → ℝ | (∑ i, a i * x i) ≤ b}, fun _ => ⟨a, b, rfl⟩, (Set.iInter_const _).symm⟩
  refine ⟨continuous_const.max (continuous_apply 0), 2,
    fun i => {x : Fin 1 → ℝ | (∑ j, (if i = 0 then (1 : ℝ) else -1) * x j) ≤ 0},
    fun i x => if i = 0 then 0 else x 0, fun i => hpoly _ 0, fun i => ?_, ?_, ?_⟩
  · exact ⟨fun _ => if i = 0 then 0 else 1, 0, fun x => by by_cases h : i = 0 <;> simp [h]⟩
  · ext x
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true, Fin.sum_univ_one]
    rcases le_total (x 0) 0 with h | h
    · refine ⟨0, ?_⟩
      rw [if_pos rfl]; linarith
    · refine ⟨1, ?_⟩
      rw [if_neg (by decide : ¬((1 : Fin 2) = 0))]; linarith
  · intro i x hx
    simp only [Set.mem_setOf_eq, Fin.sum_univ_one] at hx
    by_cases h : i = 0
    · have hx0 : x 0 ≤ 0 := by rw [if_pos h, one_mul] at hx; exact hx
      simp [h, max_eq_left hx0]
    · have hx0 : (0 : ℝ) ≤ x 0 := by rw [if_neg h] at hx; linarith
      simp [h, max_eq_right hx0]

/-- The two `CPWL` predicates are **not** the same: the agent's version is the
strictly stronger local-agreement condition. -/
theorem cpwl_ne : ∃ n, Agent078.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => not_mem_agent_cpwl 1 0 ?_⟩
  rw [h]
  exact mem_ref_cpwl

/-! ### The agent's Theorem 2 is false outright. -/

/-- A one-hidden-layer network on `ℝ³` computing `x ↦ max 0 (x 0)`. -/
private noncomputable def netRelu0 : Agent078.ReLUNetwork 3 1 where
  width := fun i => if i = 0 then 3 else 1
  width_zero := rfl
  width_last := rfl
  A := fun _ j l => if j = 0 ∧ l = 0 then (1 : ℝ) else 0
  b := fun _ _ => 0

private lemma netRelu0_computes :
    netRelu0.Computes (fun x : Fin 3 → ℝ => max 0 (x 0)) := by
  intro x
  simp [Agent078.ReLUNetwork.netForward, Agent078.ReLUNetwork.layerMap, netRelu0,
    Agent078.reluVec, Agent078.relu, Agent078.toSeq, Finset.sum_range_succ]

/-- `x ↦ max 0 (x 0)` is representable by a one-hidden-layer ReLU network. -/
private lemma mem_agent_relun :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent078.ReLUn 3 (Agent078.depthBound 3) :=
  ⟨1, by simp [Agent078.depthBound], netRelu0, netRelu0_computes⟩

/-- **The agent's Theorem 2 is false.**  At `n = 3`, `x ↦ max 0 (x 0)` is computed
by a one-hidden-layer ReLU network but is rejected by the neighbourhood-agreement
`CPWL` (it has a kink at the origin). -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent078.CPWL n = Agent078.ReLUn n (Agent078.depthBound n)) := by
  intro h
  have h3 := h 3 le_rfl
  refine not_mem_agent_cpwl 3 0 ?_
  rw [h3]
  exact mem_agent_relun

/-- The reference direction of the `↔` is exactly `Ref.theorem2`, which is
`sorry`-ed in the reference file; the agent direction is refuted above by
`agent_side_false`, so this reduces to the (unproved) reference theorem. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent078.CPWL n = Agent078.ReLUn n (Agent078.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_078

namespace Star_087

/-!
# Star comparison: `Agent087` vs `Ref`

* `depthBound` is *literally* the same term `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`, so
  `depth` is `rfl`.
* `CPWL` does **not** agree.  Despite the doc-string calling it "a genuine finite
  polyhedral/local piecewise-affine condition", the definition is the
  *neighbourhood-agreement* one: `∀ x, ∃ i, ∀ᶠ y in nhds x, f y = a i y` with `a` a
  finite family of affine functionals.  There is no polyhedral cover anywhere in the
  definition, and on connected `ℝⁿ` local agreement forces `f` to be globally affine.
  So `cpwl` is false and we prove `cpwl_ne`, plus the bonus `agent_side_false`.
* `ReLUn` is the "**exactly** `k` hidden layers" reading against the reference's
  "at most `k`"; honest `sorry`.
-/

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent087.depthBound n = Ref.depthBound n := rfl

/-! ### The ramp is rejected by the agent's `CPWL` -/

/-- `x ↦ max 0 (x i)` is not in `Agent087.CPWL n`: agreement with a single affine map
on a neighbourhood of the origin forces `max 0 t = a * t + b` for all small `t`, which
the kink at `0` makes impossible. -/
private lemma ramp_not_mem_agent {n : ℕ} (i : Fin n) :
    (fun x : Fin n → ℝ => max 0 (x i)) ∉ Agent087.CPWL n := by
  rintro ⟨-, r, a, ha, hloc⟩
  obtain ⟨j, hj⟩ := hloc (fun _ => 0)
  obtain ⟨c, b, hcb⟩ := ha j
  have hcont : Continuous (fun t : ℝ => (fun _ => t : Fin n → ℝ)) :=
    continuous_pi fun _ => continuous_id
  have htend : Filter.Tendsto (fun t : ℝ => (fun _ => t : Fin n → ℝ))
      (nhds 0) (nhds (fun _ => 0)) := by simpa using hcont.tendsto (0 : ℝ)
  have key : ∀ᶠ t : ℝ in nhds (0 : ℝ), max 0 t = (∑ k, c k) * t + b := by
    filter_upwards [htend.eventually hj] with t ht
    simpa [hcb, Finset.sum_mul] using ht
  rw [Metric.eventually_nhds_iff] at key
  obtain ⟨ε, hε, hball⟩ := key
  have h0 := hball (y := (0 : ℝ)) (by simpa using hε)
  have hp := hball (y := ε / 2)
    (by rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
  have hm := hball (y := -(ε / 2))
    (by rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by linarith)]; linarith)
  rw [max_self] at h0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ ε / 2)] at hp
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0 : ℝ))] at hm
  linarith

/-! ### The same ramp is accepted by the reference `CPWL` -/

/-- A halfspace is a polyhedron: intersect the one-element family. -/
private lemma poly_of_half {n : ℕ} {S : Set (Fin n → ℝ)} (h : Ref.IsHalfspace n S) :
    Ref.IsPolyhedron n S :=
  ⟨1, fun _ => S, fun _ => h, by rw [Set.iInter_const]⟩

/-- `x ↦ max 0 (x 0)` is CPWL in the reference sense: the two halflines are polyhedra,
they cover `ℝ`, and the ramp is affine on each. -/
private lemma ramp_mem_ref : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Ref.CPWL 1 := by
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

/-- The agent's `CPWL` is strictly stronger than the reference's, so the two differ. -/
theorem cpwl_ne : ∃ n, Agent087.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => ramp_not_mem_agent (0 : Fin 1) ?_⟩
  rw [h]
  exact ramp_mem_ref

/-! ### Bonus: the agent's own Theorem 2 is outright false -/

private lemma max_zero_idem (x : ℝ) : max 0 (max 0 x) = max 0 x := by
  rw [← max_assoc, max_self]

private lemma ceil_logb_two : ⌈Real.logb 3 (2 : ℝ)⌉₊ = 1 := by
  have hpos : 0 < Real.logb 3 (2 : ℝ) := Real.logb_pos (by norm_num) (by norm_num)
  have hle : Real.logb 3 (2 : ℝ) ≤ 1 := by
    rw [show Real.logb 3 (2 : ℝ) = Real.log 2 / Real.log 3 from rfl,
      div_le_one (Real.log_pos (by norm_num))]
    gcongr <;> norm_num
  exact le_antisymm (Nat.ceil_le.mpr (by exact_mod_cast hle)) (Nat.ceil_pos.mpr hpos)

private lemma depthBound_three : Agent087.depthBound 3 = 2 := by
  have h : Agent087.depthBound 3 = ⌈Real.logb 3 (2 : ℝ)⌉₊ + 1 := by
    unfold Agent087.depthBound; norm_num
  rw [h, ceil_logb_two]

/-- The coordinate projection is an affine functional in the agent's sense. -/
private lemma isAffine_proj : Agent087.IsAffine 3 (fun z : Fin 3 → ℝ => z 0) := by
  refine ⟨fun j => if j = 0 then (1 : ℝ) else 0, 0, ?_⟩
  funext z
  simp [Fin.sum_univ_three]

/-- `x ↦ max 0 (x 0)` on `ℝ³` is computed by a network with **exactly two** hidden
layers: the first applies `relu` after the identity, the second re-applies it
(`relu` is idempotent) before reading off coordinate `0`. -/
private lemma ramp_represents : Agent087.Represents 3 2 (fun x : Fin 3 → ℝ => max 0 (x 0)) := by
  refine ⟨3, 1, 0, fun y : Fin 3 → ℝ => max 0 (y 0), ?_, ?_⟩
  · refine ⟨3, 1, 0, fun z : Fin 3 → ℝ => z 0, isAffine_proj, ?_⟩
    funext y
    simp [Agent087.affineMap, Agent087.reluVec, Agent087.relu]
  · funext x
    simp [Agent087.affineMap, Agent087.reluVec, Agent087.relu, max_zero_idem]

/-- The `Agent087` reading of Theorem 2 is false on its own terms, with no reference
theorem involved: at `n = 3` the ramp lies in `ReLUn 3 (depthBound 3)` but its
neighbourhood-agreement `CPWL` rejects it. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent087.CPWL n = Agent087.ReLUn n (Agent087.depthBound n)) := by
  intro h
  have h3 := h 3 le_rfl
  rw [depthBound_three] at h3
  refine ramp_not_mem_agent (0 : Fin 3) ?_
  rw [h3]
  exact ramp_represents

/-! ### The remaining obligations -/

-- `Agent087.ReLUn n k` is "**exactly** `k` hidden layers", `Ref.ReLUn n k` is
-- "**at most** `k`".  These denote the same set, but only through the padding identity
-- `x = relu x - relu (-x)`, which is a real theorem and is not proved here.
theorem relun (n k : ℕ) : Agent087.ReLUn n k = Ref.ReLUn n k := sorry

-- The agent side of the biconditional is false (`agent_side_false`), so `statement`
-- holds iff the reference side is *also* false, i.e. iff the real Theorem 2 fails.
-- Settling that needs `Ref.theorem2`, which is itself `sorry`-ed; routing through it
-- would prove nothing, so this stays an honest `sorry`.
theorem statement :
    (∀ n, 3 ≤ n → Agent087.CPWL n = Agent087.ReLUn n (Agent087.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_087

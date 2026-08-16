namespace Star_017

/-!
# Star comparison: `Agent017` vs `Ref`

* `ReLUn` agrees: both files read `ReLU_{n,k}` as **at most** `k` hidden layers, and the two
  recursive network predicates (`Ref.ComputedBy` / `Agent017.ComputesWithLayers`) are the
  same definition up to the field names of the affine-map structure.  Proved by induction.
* `depthBound` agrees, once `((n-1 : ℕ) : ℝ)` is identified with `((n : ℝ) - 1)`, which needs
  `1 ≤ n` — supplied by `hn`.
* `CPWL` does **not** agree.  `Agent017.CPWL` asks for agreement with a member of a finite
  affine family on a *neighbourhood* of every point; on connected `ℝⁿ` that forces global
  affineness, so it is strictly stronger than the reference's polyhedral-cover condition.
  Hence `cpwl_ne`, and in fact the whole `Agent017` reading of Theorem 2 is false
  (`agent_side_false`): `x ↦ max 0 (x 0)` is a one-hidden-layer network missing from its `CPWL`.
-/

/-- The two network predicates denote the same thing; they differ only in the field names
of the affine-transformation structure (`Ref.Aff.M` vs `Agent017.Aff.A`). -/
private lemma computedBy_iff (k : ℕ) : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Ref.ComputedBy n k f ↔ Agent017.ComputesWithLayers n k f := by
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨T, hT⟩; exact ⟨⟨T.M, T.c⟩, hT⟩
    · rintro ⟨T, hT⟩; exact ⟨⟨T.A, T.c⟩, hT⟩
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, T, g, hg, hf⟩
      exact ⟨m, ⟨T.M, T.c⟩, g, (ih m g).1 hg, hf⟩
    · rintro ⟨m, T, g, hg, hf⟩
      exact ⟨m, ⟨T.A, T.c⟩, g, (ih m g).2 hg, hf⟩

theorem relun (n k : ℕ) : Agent017.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent017.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, hf⟩; exact ⟨j, hj, (computedBy_iff j n f).2 hf⟩
  · rintro ⟨j, hj, hf⟩; exact ⟨j, hj, (computedBy_iff j n f).1 hf⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent017.depthBound n = Ref.depthBound n := by
  have h1 : (1 : ℕ) ≤ n := le_trans (by norm_num) hn
  unfold Agent017.depthBound Ref.depthBound
  rw [Nat.cast_sub h1, Nat.cast_one]

/-- Every halfspace is a polyhedron (the intersection of the one-element family). -/
private lemma poly_of_half {n : ℕ} {S : Set (Fin n → ℝ)} (h : Ref.IsHalfspace n S) :
    Ref.IsPolyhedron n S :=
  ⟨1, fun _ => S, fun _ => h, by rw [Set.iInter_const]⟩

/-- `x ↦ max 0 (x 0)` is CPWL in the reference sense: the two halflines cover `ℝ`. -/
private lemma mem_ref : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Ref.CPWL 1 := by
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

/-- `x ↦ max 0 (x 0)` is **not** in `Agent017.CPWL`: neighbourhood agreement with a single
affine map at the origin forces `max 0 t = a * t + b` for all small `t`, which is absurd. -/
private lemma not_mem_agent (n : ℕ) :
    (fun x : Fin (n + 1) → ℝ => max 0 (x 0)) ∉ Agent017.CPWL (n + 1) := by
  rintro ⟨-, N, g, hloc⟩
  obtain ⟨U, i, hU, hUy⟩ := hloc 0
  have hev : ∀ᶠ y in nhds (0 : Fin (n + 1) → ℝ), max 0 (y 0) = (g i).eval y 0 := by
    filter_upwards [hU] with y hy using hUy y hy
  have hs : Filter.Tendsto (fun t : ℝ => (fun _ => t : Fin (n + 1) → ℝ)) (nhds 0)
      (nhds (0 : Fin (n + 1) → ℝ)) :=
    (continuous_pi fun _ => continuous_id).tendsto' 0 0 (by funext j; rfl)
  have key : ∀ᶠ t : ℝ in nhds (0 : ℝ),
      max 0 t = (∑ j, (g i).A 0 j) * t + (g i).c 0 := by
    filter_upwards [hs.eventually hev] with t ht
    simpa [Agent017.Aff.eval, Matrix.mulVec, dotProduct, Finset.sum_mul, Pi.add_apply] using ht
  rw [Metric.eventually_nhds_iff] at key
  obtain ⟨ε, hε, hkey⟩ := key
  have e0 := hkey (show dist (0 : ℝ) 0 < ε by simpa using hε)
  have ep := hkey (show dist (ε / 2) (0 : ℝ) < ε by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
  have en := hkey (show dist (-(ε / 2)) (0 : ℝ) < ε by
    rw [Real.dist_eq, sub_zero, abs_of_neg (by linarith)]; linarith)
  rw [max_self] at e0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ ε / 2)] at ep
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0 : ℝ))] at en
  linarith

/-- **Refutation of `cpwl`.** The neighbourhood-agreement `CPWL` of `Agent017` is strictly
stronger than the reference's polyhedral-cover `CPWL`; `x ↦ max 0 (x 0)` separates them. -/
theorem cpwl_ne : ∃ n, Agent017.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  exact not_mem_agent 0 ((Set.ext_iff.mp h (fun x : Fin 1 → ℝ => max 0 (x 0))).mpr mem_ref)

/-- `x ↦ max 0 (x 0)` on `ℝ³` is a one-hidden-layer ReLU network, hence lies in
`Agent017.ReLUn 3 (depthBound 3)` since `depthBound 3 ≥ 1`. -/
private lemma relu3_mem :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent017.ReLUn 3 (Agent017.depthBound 3) := by
  have h0 : Agent017.ComputesWithLayers 1 0 (fun y : Fin 1 → ℝ => y 0) :=
    ⟨⟨1, 0⟩, by intro x; simp [Agent017.Aff.eval, Matrix.one_mulVec]⟩
  have h1 : Agent017.ComputesWithLayers 3 1 (fun x : Fin 3 → ℝ => max 0 (x 0)) := by
    refine ⟨1, ⟨Matrix.of fun _ j => if j = 0 then (1 : ℝ) else 0, 0⟩,
      (fun y : Fin 1 → ℝ => y 0), h0, fun x => ?_⟩
    simp [Agent017.Aff.eval, Agent017.reluV, Agent017.relu, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]
  exact ⟨1, Nat.le_add_left 1 _, h1⟩

/-- **Bonus.** The `Agent017` reading of Theorem 2 is outright false: its `CPWL` is a set of
globally affine functions, so it misses the one-hidden-layer network `x ↦ max 0 (x 0)`. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent017.CPWL n = Agent017.ReLUn n (Agent017.depthBound n)) := by
  intro h
  have hmem : (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent017.CPWL 3 := by
    rw [h 3 (by norm_num)]; exact relu3_mem
  exact not_mem_agent 2 hmem

/-- The two readings of Theorem 2 are **not** equivalent: the left side is false
(`agent_side_false`) while the right side is the genuine Theorem 2, which is true.
Honest `sorry`: closing it requires *proving* `Ref.theorem2`, the entire content of the
paper, and routing through the `sorry`-ed `Ref.theorem2` is forbidden. -/
theorem statement_ne :
    ¬ ((∀ n, 3 ≤ n → Agent017.CPWL n = Agent017.ReLUn n (Agent017.depthBound n)) ↔
      (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n))) := by
  intro hiff
  exact agent_side_false (hiff.2 (by sorry))

end Star_017

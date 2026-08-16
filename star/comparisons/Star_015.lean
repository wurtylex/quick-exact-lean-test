namespace Star_015

/-!
# Star comparison: `Agent015` vs `Ref`

* `depthBound` is *literally* the same term (`⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1`), so `depth`
  is `rfl`.
* The two network predicates agree (`computedBy_iff`), but `Agent015.ReLUn n k` asks for
  **exactly** `k` hidden layers while `Ref.ReLUn n k` asks for **at most** `k`.  One
  inclusion is immediate (`relun_subset`); the other needs the padding identity
  `x = relu x - relu (-x)`, so `relun` is an honest `sorry`.
* `CPWL` does **not** agree: despite the "polyhedral subdivision" wording in the doc
  comment, `Agent015.IsCPWL` only requires agreement with one affine map on an
  `ε`-ball around each point, which on connected `ℝⁿ` forces global affineness.
  So `cpwl` is false; we prove `cpwl_ne`, and moreover `agent_side_false`.
-/

/-- The two network predicates denote the same thing; only the affine-map bundle differs. -/
private lemma computedBy_iff : ∀ (k n : ℕ) (f : Agent015.Vec n → ℝ),
    Agent015.Represents n k f ↔ Ref.ComputedBy n k f := by
  intro k
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨T, hT⟩; exact ⟨⟨T.A, T.c⟩, hT⟩
    · rintro ⟨T, hT⟩; exact ⟨⟨T.M, T.c⟩, hT⟩
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, T, g, hg, hf⟩
      exact ⟨m, ⟨T.A, T.c⟩, g, (ih m g).1 hg, hf⟩
    · rintro ⟨m, T, g, hg, hf⟩
      exact ⟨m, ⟨T.M, T.c⟩, g, (ih m g).2 hg, hf⟩

/-- "Exactly `k` layers" is contained in "at most `k` layers". -/
theorem relun_subset (n k : ℕ) : Agent015.ReLUn n k ⊆ Ref.ReLUn n k := by
  intro f hf
  exact ⟨k, le_rfl, (computedBy_iff k n f).1 hf⟩

/-- The two sets are in fact equal, but the reverse inclusion needs the padding identity
`x = relu x - relu (-x)` to lift a `j`-layer network to exactly `k` layers.  Honest
`sorry`: that is a real theorem, not a definitional unfolding. -/
theorem relun (n k : ℕ) : Agent015.ReLUn n k = Ref.ReLUn n k := by
  sorry

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent015.depthBound n = Ref.depthBound n := rfl

/-- Every halfspace is a polyhedron (intersection of the one-element family). -/
private lemma poly_of_half {n : ℕ} {S : Set (Fin n → ℝ)} (h : Ref.IsHalfspace n S) :
    Ref.IsPolyhedron n S :=
  ⟨1, fun _ => S, fun _ => h, by rw [Set.iInter_const]⟩

/-- `x ↦ max 0 (x 0)` is CPWL in the reference sense: the two halflines cover `ℝ`. -/
private lemma max_mem_ref : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Ref.CPWL 1 := by
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

/-- `x ↦ max 0 (x 0)` is *not* in `Agent015.CPWL`: neighbourhood agreement with a single
affine map at the origin forces `max 0 t = a * t + b` for all small `t`, which is absurd. -/
private lemma max_not_mem (n : ℕ) :
    (fun x : Agent015.Vec (n + 1) => max 0 (x 0)) ∉ Agent015.CPWL (n + 1) := by
  rintro ⟨-, m, g, h⟩
  obtain ⟨i, ε, hε, hi⟩ := h 0
  have key : ∀ t : ℝ, |t| < ε → max 0 t = (∑ j, (g i).A 0 j) * t + (g i).c 0 := by
    intro t ht
    have hd : dist (fun _ => t : Agent015.Vec (n + 1)) 0 < ε := by
      rw [dist_pi_lt_iff hε]
      intro j
      simpa [Real.dist_eq] using ht
    simpa [Agent015.AffineMap.toFun, Matrix.mulVec, dotProduct, Finset.sum_mul]
      using hi (fun _ => t) hd
  have h0 := key 0 (by simpa using hε)
  have h1 := key (ε / 2) (by rw [abs_of_pos] <;> linarith)
  have h2 := key (-(ε / 2)) (by rw [abs_of_neg] <;> linarith)
  rw [max_self] at h0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ ε / 2)] at h1
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0 : ℝ))] at h2
  nlinarith [h0, h1, h2]

/-- `Agent015.CPWL` is strictly stronger than `Ref.CPWL`, so the two differ. -/
theorem cpwl_ne : ∃ n, Agent015.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  have hmem : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent015.CPWL 1 := by
    rw [h]; exact max_mem_ref
  exact max_not_mem 0 hmem

/-- `relu` is idempotent, which lets us pad a network to any extra depth. -/
private lemma relu_idem (t : ℝ) : max (0 : ℝ) (max 0 t) = max 0 t := by
  rw [← max_assoc, max_self]

/-- On `ℝ¹`, `relu` is computed by a network with *exactly* `k + 1` hidden layers. -/
private lemma rep_one (k : ℕ) :
    Agent015.Represents 1 (k + 1) (fun y : Agent015.Vec 1 => max 0 (y 0)) := by
  induction k with
  | zero =>
    refine ⟨1, ⟨1, 0⟩, fun y : Agent015.Vec 1 => y 0, ⟨⟨1, 0⟩, fun x => ?_⟩, fun x => ?_⟩
    · simp [Agent015.AffineMap.toFun, Matrix.one_mulVec]
    · simp [Agent015.AffineMap.toFun, Agent015.reluVec, Agent015.relu, Matrix.one_mulVec]
  | succ k ih =>
    refine ⟨1, ⟨1, 0⟩, fun y : Agent015.Vec 1 => max 0 (y 0), ih, fun x => ?_⟩
    simp [Agent015.AffineMap.toFun, Agent015.reluVec, Agent015.relu, Matrix.one_mulVec,
      relu_idem]

/-- On `ℝ³`, `x ↦ max 0 (x 0)` is computed by exactly `k + 2` hidden layers. -/
private lemma rep_three (k : ℕ) :
    Agent015.Represents 3 (k + 2) (fun x : Agent015.Vec 3 => max 0 (x 0)) := by
  refine ⟨1, ⟨Matrix.of fun _ j => if j = 0 then (1 : ℝ) else 0, 0⟩,
    fun y : Agent015.Vec 1 => max 0 (y 0), rep_one k, fun x => ?_⟩
  simp [Agent015.AffineMap.toFun, Agent015.reluVec, Agent015.relu, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three, relu_idem]

/-- `⌈log₃ 2⌉ ≥ 1`, so the depth budget at `n = 3` is at least two hidden layers. -/
private lemma depthBound_three : ∃ m : ℕ, Agent015.depthBound 3 = m + 2 := by
  have hcast : (((3 : ℕ) : ℝ) - 1) = 2 := by norm_num
  have hpos : 0 < Real.logb 3 (((3 : ℕ) : ℝ) - 1) := by
    rw [hcast]; exact Real.logb_pos (by norm_num) (by norm_num)
  have h1 : 0 < ⌈Real.logb 3 (((3 : ℕ) : ℝ) - 1)⌉₊ := Nat.ceil_pos.mpr hpos
  exact ⟨⌈Real.logb 3 (((3 : ℕ) : ℝ) - 1)⌉₊ - 1, by simp only [Agent015.depthBound]; omega⟩

/-- The `Agent015` reading of Theorem 2 is outright false: `relu` of a coordinate is a
one-hidden-layer network (padded to the required depth), but its neighbourhood-agreement
`CPWL` rejects it. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent015.CPWL n = Agent015.ReLUn n (Agent015.depthBound n)) := by
  intro h
  obtain ⟨m, hm⟩ := depthBound_three
  have hmem : (fun x : Agent015.Vec 3 => max 0 (x 0)) ∈ Agent015.CPWL 3 := by
    rw [h 3 (by norm_num)]
    show Agent015.Represents 3 (Agent015.depthBound 3) _
    rw [hm]
    exact rep_three m
  exact max_not_mem 2 hmem

/-- The two readings are *not* equivalent: the left side is false (`agent_side_false`)
while the right side is the real Theorem 2.  Honest `sorry`: discharging it needs the
true `Ref.theorem2`, which is itself `sorry`-ed, and routing through it is forbidden. -/
theorem statement_ne :
    ¬ ((∀ n, 3 ≤ n → Agent015.CPWL n = Agent015.ReLUn n (Agent015.depthBound n)) ↔
      (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n))) := by
  intro hiff
  exact agent_side_false (hiff.2 (by sorry))

end Star_015

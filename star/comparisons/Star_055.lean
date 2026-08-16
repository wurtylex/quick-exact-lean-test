namespace Star_055

/-!
# Star comparison: `Agent055` vs `Ref`

* `depthBound` agrees, but not definitionally: `Agent055` casts `(n - 1 : ℕ)`, the
  reference subtracts in `ℝ`.  The bridge is `Nat.cast_sub`, available from `hn`.
* `ReLUn` agrees: both files take **at most** `k` hidden layers and the recursive
  network predicates differ only in the base case (`IsAffineFun` vs. a width-`1`
  affine map read at coordinate `0`) and in the packaging of affine maps.
  A genuine (if easy) induction, proved below.
* `CPWL` does **not** agree: `Agent055.CPWL` demands agreement with a member of a
  fixed finite affine family on a *neighbourhood* of every point, which on connected
  `ℝⁿ` forces global affineness.  So `cpwl` is false; we prove `cpwl_ne`, and in fact
  the whole `Agent055` reading of Theorem 2 is false (`agent_side_false`).
-/

/-- The two packagings of an affine map evaluate to the same function. -/
private lemma aff_eval_eq {a b : ℕ} (M : Matrix (Fin b) (Fin a) ℝ) (c : Fin b → ℝ) :
    (Agent055.AffMap.mk M c).eval = (Ref.Aff.mk M c).eval := by
  funext x i
  simp [Agent055.AffMap.eval, Ref.Aff.eval, Matrix.mulVec, dotProduct]

/-- The two componentwise ReLUs are the same function. -/
private lemma reluVec_eq {m : ℕ} : (Agent055.reluVec (m := m)) = Ref.reluVec := by
  funext v i
  simp [Agent055.reluVec, Ref.reluVec, Agent055.relu, Ref.relu]

/-- The two network predicates denote the same thing, by induction on the depth. -/
private lemma computed_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent055.ComputedByReLUNet n k f ↔ Ref.ComputedBy n k f := by
  intro k
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨a, b, hf⟩
      refine ⟨⟨Matrix.of fun _ j => a j, fun _ => b⟩, fun x => ?_⟩
      rw [hf x]
      simp [Ref.Aff.eval, Matrix.mulVec, dotProduct]
    · rintro ⟨T, hT⟩
      refine ⟨fun j => T.M 0 j, T.c 0, fun x => ?_⟩
      simpa [Ref.Aff.eval, Matrix.mulVec, dotProduct] using hT x
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, ⟨A, c⟩, g, hg, hf⟩
      refine ⟨m, ⟨A, c⟩, g, (ih m g).1 hg, fun x => ?_⟩
      rw [hf x, reluVec_eq, aff_eval_eq]
    · rintro ⟨m, ⟨M, c⟩, g, hg, hf⟩
      refine ⟨m, ⟨M, c⟩, g, (ih m g).2 hg, fun x => ?_⟩
      rw [hf x, ← aff_eval_eq M c, ← reluVec_eq]

theorem relun (n k : ℕ) : Agent055.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent055.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (computed_iff j n f).1 hf⟩
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (computed_iff j n f).2 hf⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent055.depthBound n = Ref.depthBound n := by
  have h1 : 1 ≤ n := le_trans (by norm_num) hn
  simp [Agent055.depthBound, Ref.depthBound, Nat.cast_sub h1]

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

/-- `x ↦ max 0 (x 0)` is *not* in `Agent055.CPWL`: neighbourhood agreement with a single
affine map at the origin forces `max 0 t = a * t + b` for all small `t`, which is absurd. -/
private lemma max_not_mem (n : ℕ) :
    (fun x : Fin (n + 1) → ℝ => max 0 (x 0)) ∉ Agent055.CPWL (n + 1) := by
  rintro ⟨-, m, g, hg, h⟩
  obtain ⟨i, U, hU, hEq⟩ := h 0
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨a, b, ha⟩ := hg i
  have key : ∀ t : ℝ, |t| < r → max 0 t = (∑ j, a j) * t + b := by
    intro t ht
    have hmem : (fun _ => t : Fin (n + 1) → ℝ) ∈ Metric.ball (0 : Fin (n + 1) → ℝ) r := by
      rw [Metric.mem_ball, dist_pi_lt_iff hr]
      intro j
      simpa [Real.dist_eq] using ht
    have hval := hEq (hball hmem)
    simpa [ha, Finset.sum_mul] using hval
  have h0 := key 0 (by simpa using hr)
  have h1 := key (r / 2) (by rw [abs_of_pos] <;> linarith)
  have h2 := key (-(r / 2)) (by rw [abs_of_neg] <;> linarith)
  rw [max_self] at h0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ r / 2)] at h1
  rw [max_eq_left (by linarith : -(r / 2) ≤ (0 : ℝ))] at h2
  nlinarith [h0, h1, h2]

/-- `Agent055.CPWL` is strictly stronger than `Ref.CPWL`, so the two differ. -/
theorem cpwl_ne : ∃ n, Agent055.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  have hmem : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent055.CPWL 1 := by
    rw [h]; exact max_mem_ref
  exact max_not_mem 0 hmem

/-- `max 0 (x 0)` on `ℝ³` is computed by one hidden layer, hence lies in `Agent055.ReLUn`. -/
private lemma relu3_mem :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent055.ReLUn 3 (Agent055.depthBound 3) := by
  refine ⟨1, Nat.le_add_left 1 _, 1, ⟨Matrix.of fun _ j => if j = 0 then (1 : ℝ) else 0, 0⟩,
    (fun y => y 0), ⟨fun _ => 1, 0, fun y => by simp⟩, fun x => ?_⟩
  simp [Agent055.AffMap.eval, Agent055.reluVec, Agent055.relu, Fin.sum_univ_three]

/-- The `Agent055` reading of Theorem 2 is outright false: its `CPWL` misses `relu`. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent055.CPWL n = Agent055.ReLUn n (Agent055.depthBound n)) := by
  intro h
  have hmem : (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent055.CPWL 3 := by
    rw [h 3 (by norm_num)]; exact relu3_mem
  exact max_not_mem 2 hmem

/-- The two readings of Theorem 2 are *not* equivalent: the left side is false
(`agent_side_false`), while the right side is the real Theorem 2, which is true.
Honest `sorry`: discharging it needs the true direction of `Ref.theorem2`, which is itself
`sorry`-ed in both files, and routing through it is forbidden. -/
theorem statement_ne :
    ¬ ((∀ n, 3 ≤ n → Agent055.CPWL n = Agent055.ReLUn n (Agent055.depthBound n)) ↔
      (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n))) := by
  intro hiff
  exact agent_side_false (hiff.2 (by sorry))

end Star_055

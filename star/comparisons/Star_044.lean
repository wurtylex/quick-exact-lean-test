namespace Star_044

/-!
# Star comparison: `Agent044` vs `Ref`

* `depthBound` is *literally* the same term (`⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1`), so `depth` is `rfl`.
* `ReLUn` agrees: both files take **at most** `k` hidden layers.  The only difference is that
  `Agent044.NetComputes` insists every hidden layer have positive width, while `Ref.ComputedBy`
  permits a width-`0` layer.  A width-`0` layer can only produce a *constant* function, and
  constants are already affine, so the two sets coincide; this is proved below.
* `CPWL` does **not** agree: `Agent044.CPWL` asks for agreement with an affine map on a
  *neighbourhood* of every point, which on connected `ℝⁿ` forces global affineness.
  So `cpwl` is false and we prove `cpwl_ne` — and, more strongly, `agent_side_false`.
-/

/-- `Agent044`'s network predicate is at least as strong as `Ref`'s: drop the width hypothesis. -/
private lemma agent_to_ref (k : ℕ) : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent044.NetComputes n k f → Ref.ComputedBy n k f := by
  induction k with
  | zero =>
    rintro n f ⟨T, hT⟩
    exact ⟨⟨T.A, T.c⟩, hT⟩
  | succ k ih =>
    rintro n f ⟨m, -, T, g, hg, hf⟩
    exact ⟨m, ⟨T.A, T.c⟩, g, ih m g hg, hf⟩

/-- Conversely, a `Ref` network is an `Agent044` network of depth `≤ k`: a width-`0` hidden
layer forces the function to be constant, and a constant needs no hidden layer at all. -/
private lemma ref_to_agent (k : ℕ) : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Ref.ComputedBy n k f → ∃ k' ≤ k, Agent044.NetComputes n k' f := by
  induction k with
  | zero =>
    rintro n f ⟨T, hT⟩
    exact ⟨0, le_rfl, ⟨T.M, T.c⟩, hT⟩
  | succ k ih =>
    rintro n f ⟨m, T, g, hg, hf⟩
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      refine ⟨0, Nat.zero_le _, ⟨0, fun _ => g 0⟩, fun x => ?_⟩
      rw [hf x, Subsingleton.elim (Ref.reluVec (T.eval x)) (0 : Fin 0 → ℝ)]
      simp [Agent044.AffineMap.eval]
    · obtain ⟨k', hk', hg'⟩ := ih m g hg
      exact ⟨k' + 1, Nat.succ_le_succ hk', m, hm, ⟨T.M, T.c⟩, g, hg', hf⟩

theorem relun (n k : ℕ) : Agent044.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent044.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, agent_to_ref j n f hf⟩
  · rintro ⟨j, hj, hf⟩
    obtain ⟨j', hj', hf'⟩ := ref_to_agent j n f hf
    exact ⟨j', hj'.trans hj, hf'⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent044.depthBound n = Ref.depthBound n := rfl

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

/-- `x ↦ max 0 (x 0)` is *not* in `Agent044.CPWL`: neighbourhood agreement with a single
affine map at the origin forces `max 0 t = a * t + b` for all small `t`, which is absurd. -/
private lemma max_not_mem (n : ℕ) :
    (fun x : Fin (n + 1) → ℝ => max 0 (x 0)) ∉ Agent044.CPWL (n + 1) := by
  rintro ⟨-, N, A, b, h⟩
  obtain ⟨i, hi⟩ := h 0
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hi
  have key : ∀ t : ℝ, |t| < r → max 0 t = (∑ j, A i j) * t + b i := by
    intro t ht
    have hd : dist (fun _ => t : Fin (n + 1) → ℝ) 0 < r := by
      rw [dist_pi_lt_iff hr]
      intro j
      simpa [Real.dist_eq] using ht
    simpa [Finset.sum_mul] using hball hd
  have h0 := key 0 (by simpa using hr)
  have h1 := key (r / 2) (by rw [abs_of_pos] <;> linarith)
  have h2 := key (-(r / 2)) (by rw [abs_of_neg] <;> linarith)
  rw [max_self] at h0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ r / 2)] at h1
  rw [max_eq_left (by linarith : -(r / 2) ≤ (0 : ℝ))] at h2
  nlinarith [h0, h1, h2]

/-- `Agent044.CPWL` is strictly stronger than `Ref.CPWL`, so the two differ. -/
theorem cpwl_ne : ∃ n, Agent044.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  have hmem : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent044.CPWL 1 := by
    rw [h]; exact max_mem_ref
  exact max_not_mem 0 hmem

/-- `max 0 (x 0)` on `ℝ³` is computed by one hidden layer of width `1`, hence lies in
`Agent044.ReLUn 3 (depthBound 3)`. -/
private lemma relu3_mem :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent044.ReLUn 3 (Agent044.depthBound 3) := by
  refine ⟨1, Nat.le_add_left 1 _, 1, one_pos,
    ⟨Matrix.of fun _ j => if j = 0 then (1 : ℝ) else 0, 0⟩, fun y => y 0,
    ⟨(⟨1, 0⟩ : Agent044.AffineMap 1 1), ?_⟩, ?_⟩
  · intro x
    simp [Agent044.AffineMap.eval, Matrix.one_mulVec]
  · intro x
    simp [Agent044.AffineMap.eval, Agent044.reluVec, Agent044.relu, Matrix.mulVec,
      dotProduct, Matrix.of_apply, Fin.sum_univ_three]

/-- The `Agent044` reading of Theorem 2 is outright false: its neighbourhood-based `CPWL`
misses `relu`, which its own `ReLUn` contains. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent044.CPWL n = Agent044.ReLUn n (Agent044.depthBound n)) := by
  intro h
  have hmem : (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent044.CPWL 3 := by
    rw [h 3 (by norm_num)]; exact relu3_mem
  exact max_not_mem 2 hmem

/-- The two readings of Theorem 2 are *not* equivalent: the left side is false
(`agent_side_false`), while the right side is the real Theorem 2, which is true.
Honest `sorry`: discharging it needs the true direction of `Ref.theorem2`, which is itself
`sorry`-ed in both files, and routing through it is forbidden. -/
theorem statement_ne :
    ¬ ((∀ n, 3 ≤ n → Agent044.CPWL n = Agent044.ReLUn n (Agent044.depthBound n)) ↔
      (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n))) := by
  intro hiff
  exact agent_side_false (hiff.2 (by sorry))

end Star_044

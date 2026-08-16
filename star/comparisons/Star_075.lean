namespace Star_075

/-!
# Star comparison: `Agent075` vs `Ref`

* `depthBound` is *literally* the same term (`⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1`), so `depth`
  is `rfl`.
* `ReLUn` differs in reading: `Agent075` asks for **exactly** `k` hidden layers (baked into
  the type `ReLUNet n k`), `Ref` for **at most** `k`.  The two sets coincide, but only via
  the padding identity `x = relu x - relu (-x)`; that is a real theorem and is left as an
  honest `sorry`.
* `CPWL` does **not** agree: `Agent075.CPWL` asks for agreement with an affine map on a
  *neighbourhood* of every point, which on connected `ℝⁿ` forces global affineness.
  So `cpwl` is false and we prove `cpwl_ne` — and in fact the whole `Agent075` reading of
  Theorem 2 is false (`agent_side_false`).
-/

/-- On nonnegative inputs `relu` is the identity, so for **every** `k` there is a width-one
`ReLUNet 1 k` computing `y ↦ y 0` on the nonnegative orthant. -/
private lemma id_net (k : ℕ) :
    ∃ net : Agent075.ReLUNet 1 k, ∀ y : Fin 1 → ℝ, 0 ≤ y 0 → net.eval y = y 0 := by
  induction k with
  | zero =>
    refine ⟨.last ⟨fun _ _ => 1, fun _ => 0⟩, fun y _ => ?_⟩
    simp [Agent075.ReLUNet.eval, Agent075.AffineTransform.eval, Fin.sum_univ_one]
  | succ k ih =>
    obtain ⟨net, hnet⟩ := ih
    refine ⟨.cons ⟨fun _ _ => 1, fun _ => 0⟩ net, fun y hy => ?_⟩
    have h1 : Agent075.reluVec
        ((⟨fun _ _ => 1, fun _ => 0⟩ : Agent075.AffineTransform 1 1).eval y) = fun _ => y 0 := by
      funext j
      simp only [Agent075.reluVec, Agent075.relu, Agent075.AffineTransform.eval,
        Fin.sum_univ_one, one_mul, add_zero]
      exact max_eq_right hy
    simp only [Agent075.ReLUNet.eval]
    rw [h1]
    exact hnet _ (by simpa using hy)

/-- `x ↦ max 0 (x 0)` on `ℝ³` is computed by a network with *exactly* `k + 1` hidden layers,
for every `k`: one layer to take the relu, then identity layers. -/
private lemma relu_mem_exact (k : ℕ) :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent075.ReLUn 3 (k + 1) := by
  obtain ⟨net, hnet⟩ := id_net k
  refine ⟨.cons ⟨fun _ i => if i = 0 then 1 else 0, fun _ => 0⟩ net, fun x => ?_⟩
  have h1 : Agent075.reluVec
      ((⟨fun _ i => if i = 0 then (1 : ℝ) else 0, fun _ => 0⟩ :
        Agent075.AffineTransform 3 1).eval x) = fun _ => max 0 (x 0) := by
    funext j
    simp [Agent075.reluVec, Agent075.relu, Agent075.AffineTransform.eval, Fin.sum_univ_three,
      Fin.ext_iff]
  simp only [Agent075.ReLUNet.eval]
  rw [h1]
  exact (hnet (fun _ => max 0 (x 0)) (by simpa using le_max_left 0 (x 0))).symm

/-- `x ↦ max 0 (x 0)` is *not* in `Agent075.CPWL`: neighbourhood agreement with a single
affine map at the origin forces `max 0 t = a * t + b` for all small `t`, which is absurd. -/
private lemma max_not_mem (n : ℕ) :
    (fun x : Fin (n + 1) → ℝ => max 0 (x 0)) ∉ Agent075.CPWL (n + 1) := by
  rintro ⟨-, m, g, hg, h⟩
  obtain ⟨i, U, hU, hEq⟩ := h 0
  obtain ⟨w, b, hwb⟩ := hg i
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hU
  have key : ∀ t : ℝ, |t| < r → max 0 t = (∑ j, w j) * t + b := by
    intro t ht
    have hmem : (fun _ => t : Fin (n + 1) → ℝ) ∈ U := by
      refine hball ?_
      rw [Metric.mem_ball, dist_pi_lt_iff hr]
      intro j
      simpa [Real.dist_eq] using ht
    have hx := hEq hmem
    rw [hwb] at hx
    simpa [Finset.sum_mul] using hx
  have h0 := key 0 (by simpa using hr)
  have h1 := key (r / 2) (by rw [abs_of_pos] <;> linarith)
  have h2 := key (-(r / 2)) (by rw [abs_of_neg] <;> linarith)
  rw [max_self] at h0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ r / 2)] at h1
  rw [max_eq_left (by linarith : -(r / 2) ≤ (0 : ℝ))] at h2
  nlinarith [h0, h1, h2]

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

/-- `Agent075.CPWL` is strictly stronger than `Ref.CPWL`, so the two differ. -/
theorem cpwl_ne : ∃ n, Agent075.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  have hmem : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent075.CPWL 1 := by
    rw [h]; exact max_mem_ref
  exact max_not_mem 0 hmem

/-- Honest `sorry`: `Agent075.ReLUn` is *exactly* `k` hidden layers and `Ref.ReLUn` is *at
most* `k`.  The inclusion `⊆` is routine, but `⊇` needs the padding theorem
`x = relu x - relu (-x)`, which is genuine mathematical content. -/
theorem relun (n k : ℕ) : Agent075.ReLUn n k = Ref.ReLUn n k := sorry

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent075.depthBound n = Ref.depthBound n := rfl

/-- The `Agent075` reading of Theorem 2 is outright false: its neighbourhood-based `CPWL`
misses `relu`, which its own `ReLUn n (depthBound n)` contains. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent075.CPWL n = Agent075.ReLUn n (Agent075.depthBound n)) := by
  intro h
  have hmem : (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent075.CPWL 3 := by
    rw [h 3 (by norm_num)]
    exact relu_mem_exact ⌈Real.logb 3 ((3 : ℝ) - 1)⌉₊
  exact max_not_mem 2 hmem

/-- The two readings of Theorem 2 are *not* equivalent: the left side is false
(`agent_side_false`), while the right side is the real Theorem 2, which is true.
Honest `sorry`: discharging it needs the true direction of `Ref.theorem2`, which is itself
`sorry`-ed in both files, and routing through it is forbidden. -/
theorem statement_ne :
    ¬ ((∀ n, 3 ≤ n → Agent075.CPWL n = Agent075.ReLUn n (Agent075.depthBound n)) ↔
      (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n))) := by
  intro hiff
  exact agent_side_false (hiff.2 (by sorry))

end Star_075

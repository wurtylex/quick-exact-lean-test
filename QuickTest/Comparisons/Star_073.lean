import QuickTest.Formalizations.Thm2_073
import QuickTest.Reference

namespace Star_073

/-!
# Star comparison: `Agent073` vs `Ref`

* `depthBound` is *literally* the same term (`⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1`), so `depth`
  is `rfl`.
* `ReLUn` differs in convention: `Agent073` asks for **exactly** `k` hidden layers, `Ref`
  for **at most** `k`.  These denote the same set, but only via the padding identity
  `x = relu x - relu (-x)`; that is a real theorem, so `relun` is an honest `sorry`.
* `CPWL` does **not** agree: `Agent073.CPWL` asks for agreement with a *single* affine map
  on a whole *neighbourhood* of every point, which on connected `ℝⁿ` forces global
  affineness.  So `cpwl` is false and we prove `cpwl_ne`; moreover the `Agent073` reading
  of Theorem 2 is outright false (`agent_side_false`).
-/

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent073.depthBound n = Ref.depthBound n := rfl

/-- Honest `sorry`: `Agent073.ReLUn` is *exactly* `k` hidden layers while `Ref.ReLUn` is
*at most* `k`.  The two sets coincide, but only through the padding identity
`x = relu x - relu (-x)`, which is a genuine theorem and not in budget here. -/
theorem relun (n k : ℕ) : Agent073.ReLUn n k = Ref.ReLUn n k := sorry

/-! ## `relu` is not in `Agent073.CPWL` -/

/-- `x ↦ max 0 (x 0)` is *not* in `Agent073.CPWL`: neighbourhood agreement with a single
affine map at the origin forces `max 0 t = a * t + b` for all small `t`, which is absurd. -/
private lemma max_not_mem (n : ℕ) :
    (fun x : Fin (n + 1) → ℝ => max 0 (x 0)) ∉ Agent073.CPWL (n + 1) := by
  rintro ⟨-, S, h⟩
  obtain ⟨T, -, U, hU, hUy⟩ := h 0
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hU
  have key : ∀ t : ℝ, |t| < r → max 0 t = (∑ j, T.A 0 j) * t + T.c 0 := by
    intro t ht
    have hd : (fun _ => t : Fin (n + 1) → ℝ) ∈ Metric.ball (0 : Fin (n + 1) → ℝ) r := by
      rw [Metric.mem_ball, dist_pi_lt_iff hr]
      intro j
      simpa [Real.dist_eq] using ht
    have := hUy _ (hball hd)
    simpa [Agent073.AffineMap.eval, Matrix.mulVec, dotProduct, Finset.sum_mul] using this
  have h0 := key 0 (by simpa using hr)
  have h1 := key (r / 2) (by rw [abs_of_pos] <;> linarith)
  have h2 := key (-(r / 2)) (by rw [abs_of_neg] <;> linarith)
  rw [max_self] at h0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ r / 2)] at h1
  rw [max_eq_left (by linarith : -(r / 2) ≤ (0 : ℝ))] at h2
  nlinarith [h0, h1, h2]

/-! ## `relu` *is* in `Ref.CPWL 1` -/

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

/-- `Agent073.CPWL` is strictly stronger than `Ref.CPWL`, so the two differ. -/
theorem cpwl_ne : ∃ n, Agent073.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  have hmem : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent073.CPWL 1 := by
    rw [h]; exact max_mem_ref
  exact max_not_mem 0 hmem

/-! ## `relu` *is* in `Agent073.ReLUn 3 (depthBound 3)` -/

/-- `x ↦ max 0 (x 0)` on `ℝ³` is computed by a network with *exactly* `k + 1` hidden
layers, for **every** `k`: extra layers are padded by `relu ∘ relu = relu` composed with
the identity affine map.  This avoids having to evaluate `⌈logb 3 2⌉₊`. -/
private lemma relu_rep : ∀ k : ℕ,
    Agent073.IsReLURep 3 1 (k + 1) (fun (x : Fin 3 → ℝ) (_ : Fin 1) => max 0 (x 0)) := by
  intro k
  induction k with
  | zero =>
    refine ⟨1, ⟨Matrix.of fun _ j => if j = 0 then (1 : ℝ) else 0, 0⟩,
      (⟨1, 0⟩ : Agent073.AffineMap 1 1).eval, ⟨⟨1, 0⟩, rfl⟩, ?_⟩
    funext x i
    simp [Agent073.AffineMap.eval, Agent073.reluVec, Agent073.relu, Function.comp_apply,
      Matrix.mulVec, dotProduct, Matrix.one_apply, Fin.sum_univ_one, Fin.sum_univ_three]
  | succ k ih =>
    refine ⟨3, ⟨1, 0⟩, (fun (y : Fin 3 → ℝ) (_ : Fin 1) => max 0 (y 0)), ih, ?_⟩
    funext x i
    have hx : (1 : Matrix (Fin 3) (Fin 3) ℝ).mulVec x + (0 : Fin 3 → ℝ) = x := by
      simp [Matrix.one_mulVec]
    simp [Agent073.AffineMap.eval, Agent073.reluVec, Agent073.relu, Function.comp_apply, hx,
      max_eq_right (le_max_left (0 : ℝ) (x 0))]

private lemma relu3_mem :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent073.ReLUn 3 (Agent073.depthBound 3) :=
  relu_rep ⌈Real.logb 3 ((3 : ℝ) - 1)⌉₊

/-- The `Agent073` reading of Theorem 2 is outright false: its neighbourhood-agreement
`CPWL` misses `relu`, which its own `ReLUn` contains. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent073.CPWL n = Agent073.ReLUn n (Agent073.depthBound n)) := by
  intro h
  have hmem : (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent073.CPWL 3 := by
    rw [h 3 (by norm_num)]; exact relu3_mem
  exact max_not_mem 2 hmem

/-- The two readings of Theorem 2 are *not* equivalent: the left side is false
(`agent_side_false`), while the right side is the real Theorem 2, which is true.
Honest `sorry`: discharging it needs the true direction of `Ref.theorem2`, which is itself
`sorry`-ed in both files, and routing through it is forbidden. -/
theorem statement_ne :
    ¬ ((∀ n, 3 ≤ n → Agent073.CPWL n = Agent073.ReLUn n (Agent073.depthBound n)) ↔
      (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n))) := by
  intro hiff
  exact agent_side_false (hiff.2 (by sorry))

end Star_073

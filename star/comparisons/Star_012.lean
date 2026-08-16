namespace Star_012

/-!
# Star comparison: `Agent012` vs `Ref`

* `depthBound` is *literally* the same term (`⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1`), so `depth`
  is `rfl`.
* `ReLUn` agrees: both files take **at most** `k` hidden layers, and the two recursive
  network predicates differ only in that `Ref` packages the first affine map as a
  structure `Aff` while `Agent012` carries the matrix and the bias separately, and that
  at depth `0` `Ref` writes the affine map as a `1 × n` matrix instead of a linear
  functional.  Both are genuine (if easy) inductions, proved below.
* `CPWL` does **not** agree: `Agent012.CPWL` asks for agreement with a member of a finite
  affine family on a whole *neighbourhood* of every point, which on connected `ℝⁿ` forces
  global affineness.  So `cpwl` is false and we prove `cpwl_ne`; moreover the `Agent012`
  reading of Theorem 2 is outright false (`agent_side_false`).
-/

/-- The two componentwise ReLUs are the same function. -/
private lemma reluVec_eq {m : ℕ} (v : Fin m → ℝ) : Agent012.reluVec v = Ref.reluVec v := rfl

/-- The two network predicates denote the same thing. -/
private lemma exact_iff (k : ℕ) : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent012.IsReLUNetExact n k f ↔ Ref.ComputedBy n k f := by
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨a, b, h⟩
      refine ⟨⟨Matrix.of fun _ j => a j, fun _ => b⟩, fun x => ?_⟩
      simp [Ref.Aff.eval, Matrix.mulVec, dotProduct, h x]
    · rintro ⟨T, h⟩
      refine ⟨fun j => T.M 0 j, T.c 0, fun x => ?_⟩
      simpa [Ref.Aff.eval, Matrix.mulVec, dotProduct] using h x
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, A, bias, g, hg, hf⟩
      exact ⟨m, ⟨A, bias⟩, g, (ih m g).1 hg, fun x => hf x⟩
    · rintro ⟨m, T, g, hg, hf⟩
      exact ⟨m, T.M, T.c, g, (ih m g).2 hg, fun x => hf x⟩

theorem relun (n k : ℕ) : Agent012.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent012.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (exact_iff j n f).1 hf⟩
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (exact_iff j n f).2 hf⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent012.depthBound n = Ref.depthBound n := rfl

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

/-- `x ↦ max 0 (x 0)` is *not* in `Agent012.CPWL`: agreement with a single affine map on a
neighbourhood of the origin forces `max 0 t = a * t + b` for all small `t`, which is absurd
(take `t = 0`, `t = r/2` and `t = -r/2`). -/
private lemma max_not_mem (n : ℕ) :
    (fun x : Fin (n + 1) → ℝ => max 0 (x 0)) ∉ Agent012.CPWL (n + 1) := by
  rintro ⟨-, m, g, hg, h⟩
  obtain ⟨i, hi⟩ := h 0
  obtain ⟨a, b, hab⟩ := hg i
  have hi' : ∀ᶠ y : Fin (n + 1) → ℝ in nhds 0, max 0 (y 0) = g i y := hi
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hi'
  have key : ∀ t : ℝ, |t| < r → max 0 t = (∑ j, a j) * t + b := by
    intro t ht
    have hd : dist (fun _ => t : Fin (n + 1) → ℝ) 0 < r := by
      rw [dist_pi_lt_iff hr]
      intro j
      simpa [Real.dist_eq] using ht
    have hy := hball hd
    rw [hab] at hy
    simpa [Finset.sum_mul] using hy
  have h0 := key 0 (by simpa using hr)
  have h1 := key (r / 2) (by rw [abs_of_pos] <;> linarith)
  have h2 := key (-(r / 2)) (by rw [abs_of_neg] <;> linarith)
  rw [max_self] at h0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ r / 2)] at h1
  rw [max_eq_left (by linarith : -(r / 2) ≤ (0 : ℝ))] at h2
  nlinarith [h0, h1, h2]

/-- `Agent012.CPWL` is strictly stronger than `Ref.CPWL`, so the two differ. -/
theorem cpwl_ne : ∃ n, Agent012.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  have hmem : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent012.CPWL 1 := by
    rw [h]; exact max_mem_ref
  exact max_not_mem 0 hmem

/-- Reading off the single coordinate of `ℝ¹` is affine. -/
private lemma coord_affine : Agent012.IsAffine (fun y : Fin 1 → ℝ => y 0) :=
  ⟨fun _ => 1, 0, fun y => by simp⟩

/-- `max 0 (x 0)` on `ℝ³` is computed by one hidden layer, hence lies in `Agent012.ReLUn`. -/
private lemma relu3_mem :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent012.ReLUn 3 (Agent012.depthBound 3) := by
  refine ⟨1, Nat.le_add_left 1 _, 1,
    Matrix.of fun _ j => if j = 0 then (1 : ℝ) else 0, 0, (fun y => y 0), coord_affine,
    fun x => ?_⟩
  simp [Agent012.reluVec, Agent012.relu, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- The `Agent012` reading of Theorem 2 is outright false: its neighbourhood-based `CPWL`
misses `relu` of a coordinate, which its own `ReLUn` contains at depth `1`. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent012.CPWL n = Agent012.ReLUn n (Agent012.depthBound n)) := by
  intro h
  have hmem : (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent012.CPWL 3 := by
    rw [h 3 (by norm_num)]; exact relu3_mem
  exact max_not_mem 2 hmem

/-- The two readings of Theorem 2 are *not* equivalent: the left side is false
(`agent_side_false`), while the right side is the real Theorem 2, which is true.
Honest `sorry`: discharging it needs the true content of `Ref.theorem2`, which is itself
`sorry`-ed in the reference file, and routing through it is forbidden. -/
theorem statement_ne :
    ¬ ((∀ n, 3 ≤ n → Agent012.CPWL n = Agent012.ReLUn n (Agent012.depthBound n)) ↔
      (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n))) := by
  intro hiff
  exact agent_side_false (hiff.2 (by sorry))

end Star_012

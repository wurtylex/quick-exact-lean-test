namespace Star_097

/-!
# Star comparison: `Agent097` vs `Ref`

* `depthBound` is *literally* the same term (`⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1`), so `depth`
  is `rfl`.
* `ReLUn` agrees: `Agent097` also takes **at most** `k` hidden layers, and its
  `ComputesWithHiddenLayers` is the same recursion as `Ref.ComputedBy`, only with the
  affine map given as a function plus a predicate rather than as a matrix/vector pair.
  So `relun` is *proved* here, no padding identity needed.
* `CPWL` does **not** agree: `Agent097.CPWL` asks for agreement with a single affine
  functional on a whole *neighbourhood* of every point, which on connected `ℝⁿ` forces
  global affineness.  So `cpwl` is false (`cpwl_ne`), and the `Agent097` reading of
  Theorem 2 is outright false (`agent_side_false`).
-/

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent097.depthBound n = Ref.depthBound n := rfl

/-! ## `ReLUn` really does agree -/

private lemma reluVec_eq {m : ℕ} (v : Fin m → ℝ) :
    Agent097.reluVec v = Ref.reluVec v := by
  funext i; simp [Agent097.reluVec, Ref.reluVec, Agent097.relu, Ref.relu]

/-- The two network recursions define the same predicate: `Agent097` carries the affine
map as a function together with `IsAffineTransformation`, `Ref` as an `Aff` structure. -/
private lemma computes_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent097.ComputesWithHiddenLayers n k f ↔ Ref.ComputedBy n k f := by
  intro k
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨T, ⟨A, c, hT⟩, hf⟩
      exact ⟨⟨A, c⟩, fun x => by rw [hf x, hT x]; rfl⟩
    · rintro ⟨T, hf⟩
      exact ⟨T.eval, ⟨T.M, T.c, fun x => rfl⟩, hf⟩
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, T, g, ⟨A, c, hT⟩, hg, hf⟩
      refine ⟨m, ⟨A, c⟩, g, (ih m g).1 hg, fun x => ?_⟩
      have hE : ((⟨A, c⟩ : Ref.Aff n m).eval x) = T x := (hT x).symm
      rw [hf x, reluVec_eq, hE]
    · rintro ⟨m, T, g, hg, hf⟩
      exact ⟨m, T.eval, g, ⟨T.M, T.c, fun x => rfl⟩, (ih m g).2 hg,
        fun x => by rw [hf x, reluVec_eq]⟩

theorem relun (n k : ℕ) : Agent097.ReLUn n k = Ref.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨j, hj, h⟩; exact ⟨j, hj, (computes_iff j n f).1 h⟩
  · rintro ⟨j, hj, h⟩; exact ⟨j, hj, (computes_iff j n f).2 h⟩

/-! ## `relu` is not in `Agent097.CPWL` -/

/-- `x ↦ max 0 (x 0)` is *not* in `Agent097.CPWL`: neighbourhood agreement with a single
affine functional at the origin forces `max 0 t = a * t + b` for all small `t`, absurd. -/
private lemma max_not_mem (n : ℕ) :
    (fun x : Fin (n + 1) → ℝ => max 0 (x 0)) ∉ Agent097.CPWL (n + 1) := by
  rintro ⟨-, m, A, b, h⟩
  obtain ⟨i, hi⟩ := h 0
  rw [Metric.eventually_nhds_iff] at hi
  obtain ⟨r, hr, hball⟩ := hi
  have key : ∀ t : ℝ, |t| < r → max 0 t = (∑ j, A i j) * t + b i := by
    intro t ht
    have hd : dist (fun _ => t : Fin (n + 1) → ℝ) 0 < r := by
      rw [dist_pi_lt_iff hr]
      intro j
      simpa [Real.dist_eq] using ht
    simpa [← Finset.sum_mul] using hball hd
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

/-- `Agent097.CPWL` is strictly stronger than `Ref.CPWL`, so the two differ. -/
theorem cpwl_ne : ∃ n, Agent097.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  have hmem : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent097.CPWL 1 := by
    rw [h]; exact max_mem_ref
  exact max_not_mem 0 hmem

/-! ## `relu` *is* in `Agent097.ReLUn 3 (depthBound 3)` -/

/-- One hidden layer of width one computes `x ↦ max 0 (x 0)` on `ℝ³`. -/
private lemma computes_relu3 :
    Agent097.ComputesWithHiddenLayers 3 1 (fun x : Fin 3 → ℝ => max 0 (x 0)) := by
  have hg : Agent097.ComputesWithHiddenLayers 1 0 (fun y : Fin 1 → ℝ => y 0) :=
    ⟨fun y => y, ⟨1, 0, fun x => by simp [Matrix.one_mulVec]⟩, fun x => rfl⟩
  exact ⟨1, fun x => fun _ => x 0, fun y => y 0,
    ⟨Matrix.of fun _ j => if j = 0 then (1 : ℝ) else 0, 0, fun x => by
      funext i; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]⟩,
    hg, fun x => by simp [Agent097.reluVec, Agent097.relu]⟩

private lemma relu3_mem :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent097.ReLUn 3 (Agent097.depthBound 3) :=
  ⟨1, by simp [Agent097.depthBound], computes_relu3⟩

/-- The `Agent097` reading of Theorem 2 is outright false: its neighbourhood-agreement
`CPWL` misses `relu`, which its own `ReLUn` contains. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent097.CPWL n = Agent097.ReLUn n (Agent097.depthBound n)) := by
  intro h
  have hmem : (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent097.CPWL 3 := by
    rw [h 3 (by norm_num)]; exact relu3_mem
  exact max_not_mem 2 hmem

/-- The two readings are *not* equivalent: the left side is false (`agent_side_false`)
while the right side is the real Theorem 2, which is true.  Honest `sorry`: discharging it
needs the true direction of `Ref.theorem2`, itself `sorry`-ed, and routing through it is
forbidden. -/
theorem statement_ne :
    ¬ ((∀ n, 3 ≤ n → Agent097.CPWL n = Agent097.ReLUn n (Agent097.depthBound n)) ↔
      (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n))) := by
  intro hiff
  exact agent_side_false (hiff.2 (by sorry))

end Star_097

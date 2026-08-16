import QuickTest.Formalizations.Thm2_003
import QuickTest.Reference

namespace Star_003

/-!
# Star comparison: `Agent003` vs `Ref`

* `depthBound` is *literally* the same term (`⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1`), so `depth`
  is `rfl`.
* `ReLUn` agrees: both files take **at most** `k` hidden layers, and the two recursive
  network predicates differ only in bookkeeping — `Ref` packages an affine map as a
  structure `Aff` and states the network equation pointwise, `Agent003` uses a bare pair
  `Matrix × vector` and states it as an equality of functions.  A short induction below.
* `CPWL` does **not** agree: `Agent003.CPWL` asks that `f` agree with one member of a
  finite affine family on a *neighbourhood* of every point, which on connected `ℝⁿ` forces
  global affineness.  So `cpwl` is false and we prove `cpwl_ne`; moreover the `Agent003`
  reading of Theorem 2 is outright false (`agent_side_false`).
-/

/-- The two network predicates denote the same thing. -/
private lemma computedBy_iff (k : ℕ) : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Ref.ComputedBy n k f ↔ f ∈ Agent003.ReLUnExact n k := by
  induction k with
  | zero =>
    intro n f
    simp only [Ref.ComputedBy, Agent003.ReLUnExact, Set.mem_setOf_eq]
    constructor
    · rintro ⟨T, hT⟩
      exact ⟨(T.M, T.c), funext fun x => hT x⟩
    · rintro ⟨T, hT⟩
      exact ⟨⟨T.1, T.2⟩, fun x => congrFun hT x⟩
  | succ k ih =>
    intro n f
    simp only [Ref.ComputedBy, Agent003.ReLUnExact, Set.mem_setOf_eq]
    constructor
    · rintro ⟨m, T, g, hg, hf⟩
      exact ⟨m, (T.M, T.c), g, (ih m g).1 hg, funext fun x => hf x⟩
    · rintro ⟨m, T, g, hg, hf⟩
      exact ⟨m, ⟨T.1, T.2⟩, g, (ih m g).2 hg, fun x => congrFun hf x⟩

theorem relun (n k : ℕ) : Agent003.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent003.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (computedBy_iff j n f).2 hf⟩
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (computedBy_iff j n f).1 hf⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent003.depthBound n = Ref.depthBound n := rfl

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

/-- `x ↦ max 0 (x 0)` is *not* in `Agent003.CPWL`: neighbourhood agreement with a single
affine map at the origin forces `max 0 t = a * t + c` for all small `t`, which is absurd. -/
private lemma max_not_mem (n : ℕ) :
    (fun x : Fin (n + 1) → ℝ => max 0 (x 0)) ∉ Agent003.CPWL (n + 1) := by
  rintro ⟨-, m, g, hg, hloc⟩
  obtain ⟨i, hi⟩ := hloc 0
  obtain ⟨a, c, hac⟩ := hg i
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hi
  have key : ∀ t : ℝ, |t| < r → max 0 t = (∑ j, a j) * t + c := by
    intro t ht
    have hd : dist (fun _ => t : Fin (n + 1) → ℝ) 0 < r := by
      rw [dist_pi_lt_iff hr]
      intro j
      simpa [Real.dist_eq] using ht
    have hx := hball hd
    rw [hac] at hx
    simpa [Finset.sum_mul] using hx
  have h0 := key 0 (by simpa using hr)
  have h1 := key (r / 2) (by rw [abs_of_pos] <;> linarith)
  have h2 := key (-(r / 2)) (by rw [abs_of_neg] <;> linarith)
  rw [max_self] at h0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ r / 2)] at h1
  rw [max_eq_left (by linarith : -(r / 2) ≤ (0 : ℝ))] at h2
  nlinarith [h0, h1, h2]

/-- `Agent003.CPWL` is strictly stronger than `Ref.CPWL`, so the two differ. -/
theorem cpwl_ne : ∃ n, Agent003.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  have hmem : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent003.CPWL 1 := by
    rw [h]; exact max_mem_ref
  exact max_not_mem 0 hmem

/-- `max 0 (x 0)` on `ℝ³` is computed by one hidden layer, hence lies in `Agent003.ReLUn`. -/
private lemma relu3_mem :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent003.ReLUn 3 (Agent003.depthBound 3) := by
  refine ⟨1, Nat.le_add_left 1 _, ?_⟩
  simp only [Agent003.ReLUnExact, Set.mem_setOf_eq]
  refine ⟨1, (Matrix.of fun _ j => if j = 0 then (1 : ℝ) else 0, 0), fun v => v 0, ?_, ?_⟩
  · refine ⟨((1 : Matrix (Fin 1) (Fin 1) ℝ), 0), ?_⟩
    funext v
    simp [Agent003.AffineMap.eval, Matrix.one_mulVec]
  · funext x
    simp [Agent003.AffineMap.eval, Agent003.reluVec, Agent003.relu, Matrix.mulVec,
      dotProduct, Fin.sum_univ_one, Fin.sum_univ_three]

/-- The `Agent003` reading of Theorem 2 is outright false: its neighbourhood-agreement
`CPWL` misses `relu`, which is a one-hidden-layer network. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent003.CPWL n = Agent003.ReLUn n (Agent003.depthBound n)) := by
  intro h
  have hmem : (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent003.CPWL 3 := by
    rw [h 3 (by norm_num)]; exact relu3_mem
  exact max_not_mem 2 hmem

/-- The two readings of Theorem 2 are *not* equivalent: the left side is false
(`agent_side_false`), while the right side is the real Theorem 2, which is true.
Honest `sorry`: discharging it needs the true direction of `Ref.theorem2`, which is itself
`sorry`-ed, and routing through it is forbidden. -/
theorem statement_ne :
    ¬ ((∀ n, 3 ≤ n → Agent003.CPWL n = Agent003.ReLUn n (Agent003.depthBound n)) ↔
      (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n))) := by
  intro hiff
  exact agent_side_false (hiff.2 (by sorry))

end Star_003

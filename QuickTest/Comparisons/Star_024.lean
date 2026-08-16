import QuickTest.Formalizations.Thm2_024
import QuickTest.Reference

namespace Star_024

/-!
# Star comparison: `Agent024` vs `Ref`

* `depthBound` is *literally* the same term (`⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`), so
  `depth` is `rfl`.
* `ReLUn` agrees: both take **at most** `k` hidden layers, and `Agent024.NetComputes` is the
  inductive presentation of the alternating composition `Ref.ComputedBy` defines recursively.
* `CPWL` does **not** agree: `Agent024.CPWL` asks for agreement with one of finitely many
  affine maps on a whole *neighbourhood* of every point, which on connected `ℝⁿ` forces global
  affineness.  So `cpwl` is false; we prove `cpwl_ne` and also `agent_side_false`.
-/

/-- Transport a network computation along an equality of functions. -/
private lemma net_congr {n k : ℕ} {f g : (Fin n → ℝ) → ℝ} (h : f = g)
    (hg : Agent024.NetComputes n k g) : Agent024.NetComputes n k f := by
  rw [h]; exact hg

/-- The inductive predicate implies the recursive one. -/
private lemma net_to_computed {n k : ℕ} {f : (Fin n → ℝ) → ℝ}
    (h : Agent024.NetComputes n k f) : Ref.ComputedBy n k f := by
  induction h with
  | base T => exact ⟨⟨T.A, T.c⟩, fun x => rfl⟩
  | step T _ ih => exact ⟨_, ⟨T.A, T.c⟩, _, ih, fun x => rfl⟩

/-- The two network predicates denote the same thing. -/
private lemma computedBy_iff (k : ℕ) : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Ref.ComputedBy n k f ↔ Agent024.NetComputes n k f := by
  induction k with
  | zero =>
    intro n f
    refine ⟨?_, net_to_computed⟩
    rintro ⟨T, hT⟩
    have hf : f = fun x => (⟨T.M, T.c⟩ : Agent024.Affine n 1).toFun x 0 := funext hT
    rw [hf]
    exact Agent024.NetComputes.base ⟨T.M, T.c⟩
  | succ k ih =>
    intro n f
    refine ⟨?_, net_to_computed⟩
    rintro ⟨m, T, g, hg, hfx⟩
    have hf : f = fun x => g (Agent024.reluVec ((⟨T.M, T.c⟩ : Agent024.Affine n m).toFun x)) :=
      funext hfx
    rw [hf]
    exact Agent024.NetComputes.step ⟨T.M, T.c⟩ ((ih m g).1 hg)

theorem relun (n k : ℕ) : Agent024.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent024.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (computedBy_iff j n f).2 hf⟩
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (computedBy_iff j n f).1 hf⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent024.depthBound n = Ref.depthBound n := rfl

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

/-- `x ↦ max 0 (x 0)` is *not* in `Agent024.CPWL`: agreement with a single affine piece on a
neighbourhood of the origin forces `max 0 t = a * t + b` for all small `t`, which is absurd
(`t = 0` gives `b = 0`, `t > 0` gives `a = 1`, `t < 0` then gives `0 = t`). -/
private lemma max_not_mem (n : ℕ) :
    (fun x : Fin (n + 1) → ℝ => max 0 (x 0)) ∉ Agent024.CPWL (n + 1) := by
  rintro ⟨-, N, pieces, h⟩
  obtain ⟨i, hi⟩ := h 0
  rw [Metric.eventually_nhds_iff] at hi
  obtain ⟨r, hr, hy⟩ := hi
  have key : ∀ t : ℝ, |t| < r →
      max 0 t = (∑ j, (pieces i).A 0 j) * t + (pieces i).c 0 := by
    intro t ht
    have hd : dist (fun _ => t : Fin (n + 1) → ℝ) 0 < r := by
      rw [dist_pi_lt_iff hr]
      intro j
      simpa [Real.dist_eq] using ht
    simpa [Agent024.Affine.toFun, Matrix.mulVec, dotProduct, Finset.sum_mul] using hy hd
  have h0 := key 0 (by simpa using hr)
  have h1 := key (r / 2) (by rw [abs_of_pos] <;> linarith)
  have h2 := key (-(r / 2)) (by rw [abs_of_neg] <;> linarith)
  rw [max_self] at h0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ r / 2)] at h1
  rw [max_eq_left (by linarith : -(r / 2) ≤ (0 : ℝ))] at h2
  nlinarith [h0, h1, h2]

/-- `Agent024.CPWL` is strictly stronger than `Ref.CPWL`, so the two differ. -/
theorem cpwl_ne : ∃ n, Agent024.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  have hmem : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent024.CPWL 1 := by
    rw [h]; exact max_mem_ref
  exact max_not_mem 0 hmem

/-- `max 0 (x 0)` on `ℝ³` is computed by one hidden layer, hence lies in `Agent024.ReLUn`. -/
private lemma relu3_mem :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent024.ReLUn 3 (Agent024.depthBound 3) := by
  refine ⟨1, Nat.le_add_left 1 _, ?_⟩
  refine net_congr ?_ (Agent024.NetComputes.step
    (⟨Matrix.of fun _ j => if j = 0 then (1 : ℝ) else 0, 0⟩ : Agent024.Affine 3 1)
    (Agent024.NetComputes.base (⟨1, 0⟩ : Agent024.Affine 1 1)))
  funext x
  simp [Agent024.Affine.toFun, Agent024.reluVec, Agent024.relu, Matrix.mulVec, dotProduct,
    Matrix.one_apply, Fin.sum_univ_one, Fin.sum_univ_three]

/-- The `Agent024` reading of Theorem 2 is outright false: its neighbourhood-agreement
`CPWL` misses `relu`, which its own `ReLUn` contains. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent024.CPWL n = Agent024.ReLUn n (Agent024.depthBound n)) := by
  intro h
  have hmem : (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent024.CPWL 3 := by
    rw [h 3 (by norm_num)]; exact relu3_mem
  exact max_not_mem 2 hmem

/-- The two readings of Theorem 2 are *not* equivalent: the left side is false
(`agent_side_false`), while the right side is the real Theorem 2, which is true.
Honest `sorry`: discharging it needs the true direction of `Ref.theorem2`, which is itself
`sorry`-ed in both files, and routing through it is forbidden. -/
theorem statement_ne :
    ¬ ((∀ n, 3 ≤ n → Agent024.CPWL n = Agent024.ReLUn n (Agent024.depthBound n)) ↔
      (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n))) := by
  intro hiff
  exact agent_side_false (hiff.2 (by sorry))

end Star_024

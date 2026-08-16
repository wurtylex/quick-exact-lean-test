import QuickTest.Formalizations.Thm2_028
import QuickTest.Reference

namespace Star_028

/-!
# Star comparison: `Agent028` vs `Ref`

* `depthBound`: same value, not definitionally (`(n - 1 : ℕ)` cast vs `(n : ℝ) - 1`).
* `ReLUn`: agrees (both are *at most* `k` hidden layers); the predicates differ only in
  bookkeeping (scalar vs `Fin 1`-vector output, `Matrix.mulVec` vs explicit sum).
* `CPWL`: does **not** agree — `Agent028.CPWL` asks for agreement with an affine function
  on a whole *neighbourhood* of every point, which forces global affineness on `ℝⁿ`.
  So `cpwl` is false: we prove `cpwl_ne` and `agent_side_false`.
-/

/-- The two affine evaluations agree (scalar output). -/
private lemma eval_zero_eq {a : ℕ} (T : Ref.Aff a 1) (S : Agent028.Affine a 1)
    (hA : ∀ i j, T.M i j = S.A i j) (hc : T.c = S.c) (x : Fin a → ℝ) (i : Fin 1) :
    T.eval x 0 = S.apply x i := by
  have hi : i = 0 := Subsingleton.elim i 0; subst hi
  simp [Ref.Aff.eval, Agent028.Affine.apply, Matrix.mulVec, dotProduct, hA, hc]

/-- The two hidden-layer vectors agree. -/
private lemma reluVec_eq {a b : ℕ} (T : Ref.Aff a b) (S : Agent028.Affine a b)
    (hA : ∀ i j, T.M i j = S.A i j) (hc : T.c = S.c) (x : Fin a → ℝ) :
    Ref.reluVec (T.eval x) = Agent028.reluVec (S.apply x) := by
  funext i; simp [Ref.reluVec, Ref.relu, Agent028.reluVec, Agent028.relu, Ref.Aff.eval,
    Agent028.Affine.apply, Matrix.mulVec, dotProduct, hA, hc]

/-- A `Fin 1`-valued network is unchanged by re-reading its single output coordinate. -/
private lemma netfun_apply_zero {p k : ℕ} {g : (Fin p → ℝ) → (Fin 1 → ℝ)}
    (hg : Agent028.IsReLUNetFun k p 1 g) :
    Agent028.IsReLUNetFun k p 1 (fun y _ => g y 0) := by
  have h : (fun y (_ : Fin 1) => g y 0) = g := by
    funext y i; show g y 0 = g y i; rw [Subsingleton.elim (0 : Fin 1) i]
  rw [h]; exact hg

/-- The two network predicates denote the same thing. -/
private lemma computedBy_iff (k : ℕ) : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Ref.ComputedBy n k f ↔ Agent028.IsReLUNetFun k n 1 (fun x _ => f x) := by
  induction k with
  | zero =>
    intro n f; constructor
    · rintro ⟨T, hT⟩
      refine ⟨⟨fun i j => T.M i j, T.c⟩, ?_⟩; funext x i
      exact (hT x).trans (eval_zero_eq T _ (fun _ _ => rfl) rfl x i)
    · rintro ⟨T, hT⟩
      refine ⟨⟨Matrix.of T.A, T.c⟩, fun x => ?_⟩
      exact (congrFun (congrFun hT x) 0).trans
        (eval_zero_eq ⟨Matrix.of T.A, T.c⟩ T (fun _ _ => rfl) rfl x 0).symm
  | succ k ih =>
    intro n f; constructor
    · rintro ⟨m, T, g, hg, hf⟩
      refine ⟨m, ⟨fun i j => T.M i j, T.c⟩, fun y _ => g y, (ih m g).1 hg, ?_⟩
      funext x i; simp only [Function.comp_apply]
      rw [← reluVec_eq T ⟨fun i j => T.M i j, T.c⟩ (fun _ _ => rfl) rfl x]; exact hf x
    · rintro ⟨p, T, g, hg, hf⟩
      refine ⟨p, ⟨Matrix.of T.A, T.c⟩, fun y => g y 0,
        (ih p _).2 (netfun_apply_zero hg), fun x => ?_⟩
      rw [reluVec_eq ⟨Matrix.of T.A, T.c⟩ T (fun _ _ => rfl) rfl x]
      exact congrFun (congrFun hf x) 0

theorem relun (n k : ℕ) : Agent028.ReLUn n k = Ref.ReLUn n k := by
  ext f; simp only [Agent028.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]; constructor
  · rintro ⟨j, hj, hf⟩; exact ⟨j, hj, (computedBy_iff j n f).2 hf⟩
  · rintro ⟨j, hj, hf⟩; exact ⟨j, hj, (computedBy_iff j n f).1 hf⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent028.depthBound n = Ref.depthBound n := by
  have h : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  simp only [Agent028.depthBound, Ref.depthBound, h]

/-- Every halfspace is a polyhedron (intersection of the one-element family). -/
private lemma poly_of_half {n : ℕ} {S : Set (Fin n → ℝ)} (h : Ref.IsHalfspace n S) :
    Ref.IsPolyhedron n S :=
  ⟨1, fun _ => S, fun _ => h, by rw [Set.iInter_const]⟩

/-- `x ↦ max 0 (x 0)` is CPWL in the reference sense: the two halflines cover `ℝ`. -/
private lemma max_mem_ref : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Ref.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2,
    ![{x : Fin 1 → ℝ | ∑ j, (1 : ℝ) * x j ≤ 0}, {x : Fin 1 → ℝ | ∑ j, (-1 : ℝ) * x j ≤ 0}],
    ![fun _ => 0, fun x => x 0], ?_, ?_, ?_, ?_⟩
  · exact Fin.forall_fin_two.2
      ⟨poly_of_half ⟨fun _ => 1, 0, rfl⟩, poly_of_half ⟨fun _ => -1, 0, rfl⟩⟩
  · exact Fin.forall_fin_two.2 ⟨⟨0, 0, by simp⟩, ⟨fun _ => 1, 0, by simp⟩⟩
  · refine Set.eq_univ_of_forall fun x => ?_
    rcases le_or_gt (x 0) 0 with hx | hx
    · refine Set.mem_iUnion.2 ⟨0, ?_⟩
      simp only [Matrix.cons_val_zero, Set.mem_setOf_eq, Fin.sum_univ_one, one_mul]; linarith
    · refine Set.mem_iUnion.2 ⟨1, ?_⟩
      simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero,
        Set.mem_setOf_eq, Fin.sum_univ_one, neg_mul, one_mul]; linarith
  · refine Fin.forall_fin_two.2 ⟨fun x hx => ?_, fun x hx => ?_⟩
    · simp only [Matrix.cons_val_zero, Set.mem_setOf_eq, Fin.sum_univ_one, one_mul] at hx ⊢
      exact max_eq_left (by linarith)
    · simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero,
        Set.mem_setOf_eq, Fin.sum_univ_one, neg_mul, one_mul] at hx ⊢
      exact max_eq_right (by linarith)

/-- `x ↦ max 0 (x 0)` is *not* in `Agent028.CPWL`: neighbourhood agreement at the origin
forces `max 0 t = a * t + b` for all small `t`, which the kink at `0` forbids. -/
private lemma max_not_mem (n : ℕ) :
    (fun x : Fin (n + 1) → ℝ => max 0 (x 0)) ∉ Agent028.CPWL (n + 1) := by
  rintro ⟨-, ι, -, T, h⟩; obtain ⟨i, hi⟩ := h 0
  rw [Metric.eventually_nhds_iff] at hi; obtain ⟨r, hr, hball⟩ := hi
  have key : ∀ t : ℝ, |t| < r → max 0 t = (∑ j, (T i).w j) * t + (T i).b := by
    intro t ht
    have hd : dist (fun _ => t : Fin (n + 1) → ℝ) 0 < r := by
      rw [dist_pi_lt_iff hr]; intro j; simpa [Real.dist_eq] using ht
    simpa [Agent028.AffineFunc.eval, Finset.sum_mul] using hball hd
  have h0 := key 0 (by simpa using hr)
  have h1 := key (r / 2) (by rw [abs_of_pos] <;> linarith)
  have h2 := key (-(r / 2)) (by rw [abs_of_neg] <;> linarith)
  rw [max_self] at h0; rw [max_eq_right (by linarith : (0 : ℝ) ≤ r / 2)] at h1
  rw [max_eq_left (by linarith : -(r / 2) ≤ (0 : ℝ))] at h2
  nlinarith [h0, h1, h2]

/-- `Agent028.CPWL` is strictly stronger than `Ref.CPWL`, so the two differ. -/
theorem cpwl_ne : ∃ n, Agent028.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  have hmem : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent028.CPWL 1 := by rw [h]; exact max_mem_ref
  exact max_not_mem 0 hmem

/-- `max 0 (x 0)` on `ℝ³` is computed by one hidden layer, hence lies in `Agent028.ReLUn`. -/
private lemma relu3_mem :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent028.ReLUn 3 (Agent028.depthBound 3) := by
  have h1 : Agent028.IsReLUNetFun 1 3 1 (fun (x : Fin 3 → ℝ) (_ : Fin 1) => max 0 (x 0)) := by
    refine ⟨1, ⟨fun _ j => if j = 0 then (1 : ℝ) else 0, fun _ => 0⟩,
      (⟨fun _ _ => (1 : ℝ), fun _ => 0⟩ : Agent028.Affine 1 1).apply,
      ⟨⟨fun _ _ => (1 : ℝ), fun _ => 0⟩, rfl⟩, ?_⟩
    funext x i
    simp [Agent028.Affine.apply, Agent028.reluVec, Agent028.relu, Fin.sum_univ_one,
      Fin.sum_univ_three]
  exact ⟨1, Nat.le_add_left 1 _, h1⟩

/-- The `Agent028` reading of Theorem 2 is outright false: its neighbourhood-based `CPWL`
misses `relu`, which its own `ReLUn` contains. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent028.CPWL n = Agent028.ReLUn n (Agent028.depthBound n)) := by
  intro h
  have hmem : (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent028.CPWL 3 := by
    rw [h 3 (by norm_num)]; exact relu3_mem
  exact max_not_mem 2 hmem

/-- Not equivalent: the left side is false (`agent_side_false`), the right side is the real
Theorem 2.  Honest `sorry`: the right side needs `Ref.theorem2`, itself `sorry`-ed. -/
theorem statement_ne :
    ¬ ((∀ n, 3 ≤ n → Agent028.CPWL n = Agent028.ReLUn n (Agent028.depthBound n)) ↔
      (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n))) := fun hiff =>
  agent_side_false (hiff.2 (by sorry))

end Star_028

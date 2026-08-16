import QuickTest.Formalizations.Thm2_043
import QuickTest.Reference

namespace Star_043

/-!
# Star comparison: `Agent043` vs `Ref`

* `depthBound` is *literally* the same term (`⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1`), so `depth` is `rfl`.
* `ReLUn` agrees: both files take **at most** `k` hidden layers, and the two recursive
  network predicates differ only in that `Agent043` carries the scalar output as a
  `Fin 1`-vector.  This is a genuine (if easy) induction, proved below.
* `CPWL` does **not** agree: `Agent043.CPWL` asks for agreement with an affine map on a
  *neighbourhood* of every point, which on connected `ℝⁿ` forces global affineness.
  So `cpwl` is false and we prove `cpwl_ne` instead.
-/

/-- A `Fin 1`-valued network is unchanged by re-reading its single output coordinate. -/
private lemma nc_apply_zero {p k : ℕ} {g : (Fin p → ℝ) → (Fin 1 → ℝ)}
    (hg : Agent043.NetworkComputes 1 k p g) :
    Agent043.NetworkComputes 1 k p (fun y _ => g y 0) := by
  have h : (fun y (_ : Fin 1) => g y 0) = g := by
    funext y i
    show g y 0 = g y i
    rw [Subsingleton.elim (0 : Fin 1) i]
  rw [h]
  exact hg

/-- The two network predicates denote the same thing: `Ref` keeps the output scalar,
`Agent043` keeps it as a vector of width `1`. -/
private lemma computedBy_iff (k : ℕ) : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Ref.ComputedBy n k f ↔ Agent043.NetworkComputes 1 k n (fun x _ => f x) := by
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨T, hT⟩
      refine ⟨⟨T.M, T.c⟩, ?_⟩
      funext x i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      exact hT x
    · rintro ⟨T, hT⟩
      exact ⟨⟨T.A, T.c⟩, fun x => congrFun (congrFun hT x) 0⟩
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, T, g, hg, hf⟩
      refine ⟨m, ⟨T.M, T.c⟩, fun y _ => g y, (ih m g).1 hg, ?_⟩
      funext x i
      exact hf x
    · rintro ⟨p, T, g, hg, hf⟩
      refine ⟨p, ⟨T.A, T.c⟩, fun y => g y 0, (ih p _).2 (nc_apply_zero hg), fun x => ?_⟩
      exact congrFun (congrFun hf x) 0

theorem relun (n k : ℕ) : Agent043.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent043.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (computedBy_iff j n f).2 hf⟩
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (computedBy_iff j n f).1 hf⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent043.depthBound n = Ref.depthBound n := rfl

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

/-- `x ↦ max 0 (x 0)` is *not* in `Agent043.CPWL`: neighbourhood agreement with a single
affine map at the origin forces `max 0 t = a * t + b` for all small `t`, which is absurd. -/
private lemma max_not_mem (n : ℕ) :
    (fun x : Fin (n + 1) → ℝ => max 0 (x 0)) ∉ Agent043.CPWL (n + 1) := by
  rintro ⟨-, N, A, c, h⟩
  obtain ⟨r, hr, i, hi⟩ := h 0
  have key : ∀ t : ℝ, |t| < r → max 0 t = (∑ j, A i j) * t + c i := by
    intro t ht
    have hd : dist (fun _ => t : Fin (n + 1) → ℝ) 0 < r := by
      rw [dist_pi_lt_iff hr]
      intro j
      simpa [Real.dist_eq] using ht
    simpa [Finset.sum_mul] using hi (fun _ => t) hd
  have h0 := key 0 (by simpa using hr)
  have h1 := key (r / 2) (by rw [abs_of_pos] <;> linarith)
  have h2 := key (-(r / 2)) (by rw [abs_of_neg] <;> linarith)
  rw [max_self] at h0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ r / 2)] at h1
  rw [max_eq_left (by linarith : -(r / 2) ≤ (0 : ℝ))] at h2
  nlinarith [h0, h1, h2]

/-- `Agent043.CPWL` is strictly stronger than `Ref.CPWL`, so the two differ. -/
theorem cpwl_ne : ∃ n, Agent043.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  have hmem : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent043.CPWL 1 := by
    rw [h]; exact max_mem_ref
  exact max_not_mem 0 hmem

/-- `max 0 (x 0)` on `ℝ³` is computed by one hidden layer, hence lies in `Agent043.ReLUn`. -/
private lemma relu3_mem :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent043.ReLUn 3 (Agent043.depthBound 3) := by
  have h1 : Agent043.NetworkComputes 1 1 3 (fun (x : Fin 3 → ℝ) (_ : Fin 1) => max 0 (x 0)) := by
    refine ⟨1, ⟨Matrix.of fun _ j => if j = 0 then (1 : ℝ) else 0, 0⟩,
      (⟨1, 0⟩ : Agent043.AffineT 1 1).eval, ⟨⟨1, 0⟩, rfl⟩, ?_⟩
    funext x i
    simp [Agent043.AffineT.eval, Agent043.reluVec, Agent043.relu, Matrix.mulVec,
      dotProduct, Matrix.one_apply, Fin.sum_univ_one, Fin.sum_univ_three]
  exact ⟨1, Nat.le_add_left 1 _, h1⟩

/-- The `Agent043` reading of Theorem 2 is outright false: its `CPWL` misses `relu`. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent043.CPWL n = Agent043.ReLUn n (Agent043.depthBound n)) := by
  intro h
  have hmem : (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent043.CPWL 3 := by
    rw [h 3 (by norm_num)]; exact relu3_mem
  exact max_not_mem 2 hmem

/-- The two readings of Theorem 2 are *not* equivalent: the left side is false
(`agent_side_false`), while the right side is the real Theorem 2, which is true.
Honest `sorry`: discharging it needs the true direction of `Ref.theorem2`, which is itself
`sorry`-ed in both files, and routing through it is forbidden. -/
theorem statement_ne :
    ¬ ((∀ n, 3 ≤ n → Agent043.CPWL n = Agent043.ReLUn n (Agent043.depthBound n)) ↔
      (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n))) := by
  intro hiff
  exact agent_side_false (hiff.2 (by sorry))

end Star_043

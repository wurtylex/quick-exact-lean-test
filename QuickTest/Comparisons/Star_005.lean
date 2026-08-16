import QuickTest.Formalizations.Thm2_005
import QuickTest.Reference

namespace Star_005

/-!
# Star comparison: `Agent005` vs `Ref`

* `depthBound` is *literally* the same term (`⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1`), so `depth` is `rfl`.
* `ReLUn` agrees: both files take **at most** `k` hidden layers, and the two recursive
  network predicates differ only bureaucratically (`Ref` packs the first affine map into a
  structure and states the layer equation pointwise, `Agent005` uses a bare matrix/bias pair
  and states it by function equality).  Proved below by induction on `k`.
* `CPWL` does **not** agree.  Despite the doc comment's claim of "a genuine local
  piecewise-affineness condition", `Agent005.CPWL` asks for an *open neighbourhood* `U ∋ x`
  on which `f` agrees with a single affine map (`IsOpen U ∧ x ∈ U ∧ Set.EqOn f g U`).  On
  connected `ℝⁿ` that forces `f` to be globally affine, so it is strictly stronger than
  CPWL: `cpwl` is false and we prove `cpwl_ne` and `agent_side_false`.
-/

/-- The two network predicates denote the same thing. -/
private lemma computed_iff (k : ℕ) : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent005.computesReLU k n f ↔ Ref.ComputedBy n k f := by
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨w, c, rfl⟩
      refine ⟨⟨Matrix.of fun _ j => w j, fun _ => c⟩, fun x => ?_⟩
      simp [Ref.Aff.eval, Agent005.affineScalar, Matrix.mulVec, dotProduct]
    · rintro ⟨T, hT⟩
      refine ⟨fun j => T.M 0 j, T.c 0, ?_⟩
      funext x
      simpa [Agent005.affineScalar, Ref.Aff.eval, Matrix.mulVec, dotProduct] using hT x
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, A, c, g, hg, rfl⟩
      exact ⟨m, ⟨A, c⟩, g, (ih m g).1 hg, fun _ => rfl⟩
    · rintro ⟨m, T, g, hg, hf⟩
      refine ⟨m, T.M, T.c, g, (ih m g).2 hg, ?_⟩
      funext x
      exact hf x

theorem relun (n k : ℕ) : Agent005.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent005.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (computed_iff j n f).1 hf⟩
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (computed_iff j n f).2 hf⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent005.depthBound n = Ref.depthBound n := rfl

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

/-- `x ↦ max 0 (x 0)` is *not* in `Agent005.CPWL`: an open neighbourhood of the origin on
which the function is affine contains a ball of radius `r`, and then `max 0 t = a * t + b`
for all `|t| < r`; `t = 0`, `t = r/2` and `t = -r/2` are jointly contradictory. -/
private lemma max_not_mem (n : ℕ) :
    (fun x : Fin (n + 1) → ℝ => max 0 (x 0)) ∉ Agent005.CPWL (n + 1) := by
  rintro ⟨-, F, hF, h⟩
  obtain ⟨g, hgF, U, hU, h0U, hEq⟩ := h 0
  obtain ⟨w, b, rfl⟩ := hF g hgF
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU 0 h0U
  have key : ∀ t : ℝ, |t| < r → max 0 t = (∑ i, w i) * t + b := by
    intro t ht
    have hmem : (fun _ => t : Fin (n + 1) → ℝ) ∈ U := by
      refine hball ?_
      rw [Metric.mem_ball, dist_pi_lt_iff hr]
      intro j
      simpa [Real.dist_eq] using ht
    simpa [Agent005.affineScalar, Finset.sum_mul] using hEq hmem
  have h0 := key 0 (by simpa using hr)
  have h1 := key (r / 2) (by rw [abs_of_pos] <;> linarith)
  have h2 := key (-(r / 2)) (by rw [abs_of_neg] <;> linarith)
  rw [max_self] at h0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ r / 2)] at h1
  rw [max_eq_left (by linarith : -(r / 2) ≤ (0 : ℝ))] at h2
  nlinarith [h0, h1, h2]

/-- `Agent005.CPWL` is strictly stronger than `Ref.CPWL`, so the two differ. -/
theorem cpwl_ne : ∃ n, Agent005.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  have hmem : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent005.CPWL 1 := by
    rw [h]; exact max_mem_ref
  exact max_not_mem 0 hmem

/-- `max 0 (x 0)` on `ℝ³` is a one-hidden-layer network, hence lies in `Agent005.ReLUn`. -/
private lemma relu3_mem :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent005.ReLUn 3 (Agent005.depthBound 3) := by
  have hg : Agent005.computesReLU 0 1 (Agent005.affineScalar (fun _ => (1 : ℝ)) 0) :=
    ⟨fun _ => (1 : ℝ), 0, rfl⟩
  have h1 : Agent005.computesReLU 1 3 (fun x : Fin 3 → ℝ => max 0 (x 0)) := by
    refine ⟨1, Matrix.of fun _ j => if j = 0 then (1 : ℝ) else 0, 0,
      Agent005.affineScalar (fun _ => (1 : ℝ)) 0, hg, ?_⟩
    funext x
    simp [Agent005.affineScalar, Agent005.reluVec, Agent005.relu, Agent005.affineComp,
      Matrix.mulVec, dotProduct, Fin.sum_univ_one, Fin.sum_univ_three]
  exact ⟨1, Nat.le_add_left 1 _, h1⟩

/-- The `Agent005` reading of Theorem 2 is outright false: its `CPWL` misses `relu`. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent005.CPWL n = Agent005.ReLUn n (Agent005.depthBound n)) := by
  intro h
  have hmem : (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent005.CPWL 3 := by
    rw [h 3 (by norm_num)]; exact relu3_mem
  exact max_not_mem 2 hmem

/-- The two readings of Theorem 2 are *not* equivalent: the left side is false
(`agent_side_false`), while the right side is the real Theorem 2, which is true.
Honest `sorry`: discharging it needs the true direction of `Ref.theorem2`, which is itself
`sorry`-ed, and routing through it is forbidden. -/
theorem statement_ne :
    ¬ ((∀ n, 3 ≤ n → Agent005.CPWL n = Agent005.ReLUn n (Agent005.depthBound n)) ↔
      (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n))) := by
  intro hiff
  exact agent_side_false (hiff.2 (by sorry))

end Star_005

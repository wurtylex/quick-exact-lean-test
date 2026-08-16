import QuickTest.Formalizations.Thm2_023
import QuickTest.Reference

namespace Star_023

/-!
# Star comparison: `Agent023` vs `Ref`

* `depthBound` is *literally* the same term (`⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1`), so `depth`
  is `rfl`.
* `ReLUn` agrees: both files read `ReLU_{n,k}` as **at most** `k` hidden layers, and the
  two recursive network predicates differ only in bookkeeping — `Ref` packages the depth-`0`
  affine map as a `1 × n` matrix while `Agent023` uses a linear functional, and `Agent023`
  states the layer equation as an equality of functions rather than pointwise.  This is a
  genuine (if easy) induction, proved below.
* `CPWL` does **not** agree: `Agent023.CPWL` asks, at every point, for an *open
  neighbourhood* on which `f` agrees with one member of a finite affine family.  On
  connected `ℝⁿ` that forces `f` to be globally affine, so it is strictly stronger than the
  reference polyhedral-cover condition.  Hence `cpwl` is false; we prove `cpwl_ne`, and
  moreover the `Agent023` reading of Theorem 2 is outright false (`agent_side_false`).
-/

/-- The two network predicates denote the same thing. -/
private lemma net_iff (k : ℕ) : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent023.IsReLUNetworkFunc k n f ↔ Ref.ComputedBy n k f := by
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨a, b, h⟩
      refine ⟨⟨Matrix.of fun _ j => a j, fun _ => b⟩, fun x => ?_⟩
      simp [Ref.Aff.eval, Matrix.mulVec, dotProduct, h]
    · rintro ⟨T, h⟩
      refine ⟨fun j => T.M 0 j, T.c 0, funext fun x => ?_⟩
      simpa [Ref.Aff.eval, Matrix.mulVec, dotProduct] using h x
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, T, g, hg, hf⟩
      exact ⟨m, ⟨T.A, T.c⟩, g, (ih m g).1 hg, fun x => congrFun hf x⟩
    · rintro ⟨m, T, g, hg, hf⟩
      exact ⟨m, ⟨T.M, T.c⟩, g, (ih m g).2 hg, funext fun x => hf x⟩

theorem relun (n k : ℕ) : Agent023.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent023.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (net_iff j n f).1 hf⟩
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (net_iff j n f).2 hf⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent023.depthBound n = Ref.depthBound n := rfl

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

/-- `x ↦ max 0 (x 0)` is *not* in `Agent023.CPWL`: an open neighbourhood of the origin on
which the function agrees with a single affine map gives `max 0 t = c * t + b` for all
small `t`, which is absurd (`t = 0` forces `b = 0`, `t > 0` forces `c = 1`, and then
`t < 0` fails). -/
private lemma max_not_mem (n : ℕ) :
    (fun x : Fin (n + 1) → ℝ => max 0 (x 0)) ∉ Agent023.CPWL (n + 1) := by
  rintro ⟨-, m, g, hg, hcov⟩
  obtain ⟨j, U, hU, h0U, hagree⟩ := hcov 0
  obtain ⟨a, b, hab⟩ := hg j
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU 0 h0U
  have key : ∀ t : ℝ, |t| < r → max 0 t = (∑ i, a i) * t + b := by
    intro t ht
    have hd : (fun _ => t : Fin (n + 1) → ℝ) ∈ Metric.ball (0 : Fin (n + 1) → ℝ) r := by
      simp only [Metric.mem_ball]
      rw [dist_pi_lt_iff hr]
      intro i
      simpa [Real.dist_eq] using ht
    simpa [hab, Finset.sum_mul] using hagree _ (hball hd)
  have h0 := key 0 (by simpa using hr)
  have h1 := key (r / 2) (by rw [abs_of_pos] <;> linarith)
  have h2 := key (-(r / 2)) (by rw [abs_of_neg] <;> linarith)
  rw [max_self] at h0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ r / 2)] at h1
  rw [max_eq_left (by linarith : -(r / 2) ≤ (0 : ℝ))] at h2
  nlinarith [h0, h1, h2]

/-- `Agent023.CPWL` is strictly stronger than `Ref.CPWL`, so the two differ. -/
theorem cpwl_ne : ∃ n, Agent023.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  have hmem : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent023.CPWL 1 := by
    rw [h]; exact max_mem_ref
  exact max_not_mem 0 hmem

/-- Reading off the single coordinate of `ℝ¹` is affine. -/
private lemma coord_affine : Agent023.IsAffineFun (fun y : Fin 1 → ℝ => y 0) :=
  ⟨fun _ => 1, 0, by funext y; simp⟩

/-- `max 0 (x 0)` on `ℝ³` is computed by one hidden layer, hence lies in `Agent023.ReLUn`. -/
private lemma relu3_mem :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent023.ReLUn 3 (Agent023.depthBound 3) := by
  refine ⟨1, Nat.le_add_left 1 _, 1,
    ⟨Matrix.of fun _ j => if j = 0 then (1 : ℝ) else 0, 0⟩, (fun y => y 0), coord_affine, ?_⟩
  funext x
  simp [Agent023.AffineMap.eval, Agent023.reluVec, Agent023.relu, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]

/-- The `Agent023` reading of Theorem 2 is outright false: its neighbourhood-based `CPWL`
misses `relu` of a coordinate, which its own `ReLUn` contains at depth `1`. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent023.CPWL n = Agent023.ReLUn n (Agent023.depthBound n)) := by
  intro h
  have hmem : (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent023.CPWL 3 := by
    rw [h 3 (by norm_num)]; exact relu3_mem
  exact max_not_mem 2 hmem

/-- The two readings of Theorem 2 are *not* equivalent: the left side is false
(`agent_side_false`), while the right side is the real Theorem 2, which is true.
Honest `sorry`: discharging it needs the true content of `Ref.theorem2`, which is itself
`sorry`-ed in the reference file, and routing through it is forbidden. -/
theorem statement_ne :
    ¬ ((∀ n, 3 ≤ n → Agent023.CPWL n = Agent023.ReLUn n (Agent023.depthBound n)) ↔
      (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n))) := by
  intro hiff
  exact agent_side_false (hiff.2 (by sorry))

end Star_023

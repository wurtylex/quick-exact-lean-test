import QuickTest.Formalizations.Thm2_019
import QuickTest.Reference

namespace Star_019

/-!
# Star comparison: `Agent019` vs `Ref`

* `depthBound` is *literally* the same term (`⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`), so
  `depth` is `rfl`.
* `ReLUn` agrees on paper — both files take **at most** `k` hidden layers — but
  `Agent019` bundles a network as a structure carrying a width function plus dependent
  layers, while `Ref` uses a recursive predicate.  Translating between them is a genuine
  induction through dependent `Fin (widths i)` casts; `relun` is an honest `sorry`.
* `CPWL` does **not** agree: `Agent019.CPWL` asks for agreement with one member of a
  finite affine family on a *neighbourhood* of every point, which on connected `ℝⁿ`
  forces global affineness.  So `cpwl` is false and we prove `cpwl_ne`, and in fact the
  `Agent019` reading of Theorem 2 is outright false (`agent_side_false`).
-/

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

/-- `x ↦ max 0 (x 0)` is *not* in `Agent019.CPWL`: agreement with a single affine map on a
neighbourhood of the origin forces `max 0 t = a * t + b` for all small `t`, which is absurd
(`t = 0` gives `b = 0`, `t > 0` gives `a = 1`, `t < 0` then gives `0 = t`). -/
private lemma max_not_mem (n : ℕ) :
    (fun x : Fin (n + 1) → ℝ => max 0 (x 0)) ∉ Agent019.CPWL (n + 1) := by
  rintro ⟨-, m, g, hg, h⟩
  obtain ⟨j, U, hU, hUy⟩ := h 0
  obtain ⟨a, b, hab⟩ := hg j
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  have key : ∀ t : ℝ, |t| < ε → max 0 t = (∑ i, a i) * t + b := by
    intro t ht
    have hd : (fun _ => t : Fin (n + 1) → ℝ) ∈ Metric.ball (0 : Fin (n + 1) → ℝ) ε := by
      simp only [Metric.mem_ball]
      rw [dist_pi_lt_iff hε]
      intro i
      simpa [Real.dist_eq] using ht
    have hval := hUy _ (hball hd)
    rw [hab] at hval
    simpa [Finset.sum_mul] using hval
  have h0 := key 0 (by simpa using hε)
  have h1 := key (ε / 2) (by rw [abs_of_pos] <;> linarith)
  have h2 := key (-(ε / 2)) (by rw [abs_of_neg] <;> linarith)
  rw [max_self] at h0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ ε / 2)] at h1
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0 : ℝ))] at h2
  nlinarith [h0, h1, h2]

/-- `Agent019.CPWL` is strictly stronger than `Ref.CPWL`, so the two differ at `n = 1`. -/
theorem cpwl_ne : ∃ n, Agent019.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  have hmem : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent019.CPWL 1 := by
    rw [h]; exact max_mem_ref
  exact max_not_mem 0 hmem

/-- The one-hidden-layer network on `ℝ³` computing `x ↦ max 0 (x 0)`: the first layer
projects onto the first coordinate, the second is the identity on `ℝ¹`. -/
private def net3 : Agent019.ReLUNetwork 3 1 where
  widths := fun i => if i = 0 then 3 else 1
  width_zero := rfl
  width_last := rfl
  layer := fun i _ =>
    match i with
    | 0 => (Matrix.of fun _ j => if j = 0 then (1 : ℝ) else 0, 0)
    | _ + 1 => (Matrix.of fun _ _ => (1 : ℝ), 0)

private lemma net3_eval (x : Fin 3 → ℝ) : net3.eval x = max 0 (x 0) := by
  have h1 : net3.vecAt x 1 = fun _ => max 0 (x 0) := by
    have hv : net3.vecAt x 1 = Agent019.reluVec ((net3.layer 0 (by omega)).apply x) := rfl
    rw [hv]
    funext i
    simp [net3, Agent019.AffineMap'.apply, Agent019.reluVec, Agent019.relu, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three]
  have h2 : net3.eval x =
      ((net3.layer 1 (by omega)).apply (net3.vecAt x 1)) ⟨0, by simp [net3]⟩ := rfl
  rw [h2, h1]
  simp [net3, Agent019.AffineMap'.apply, Matrix.mulVec, dotProduct, Fin.sum_univ_one]

/-- `max 0 (x 0)` on `ℝ³` is computed by one hidden layer, hence lies in `Agent019.ReLUn`. -/
private lemma relu3_mem :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent019.ReLUn 3 (Agent019.depthBound 3) := by
  refine ⟨1, ?_, net3, fun x => (net3_eval x).symm⟩
  unfold Agent019.depthBound
  omega

/-- The `Agent019` reading of Theorem 2 is outright false: `relu` of a coordinate is a
one-hidden-layer network, but its neighbourhood-agreement `CPWL` rejects the kink. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent019.CPWL n = Agent019.ReLUn n (Agent019.depthBound n)) := by
  intro h
  have hmem : (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent019.CPWL 3 := by
    rw [h 3 (by norm_num)]; exact relu3_mem
  exact max_not_mem 2 hmem

/-- Both files write the depth bound as `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent019.depthBound n = Ref.depthBound n := rfl

/-- Honest `sorry`: both sides mean "at most `k` hidden layers", but `Agent019` packages a
network as a `widths`/`layer` structure with dependent `Fin (widths i)` casts while `Ref`
uses a recursive predicate; the translation is a real bidirectional induction. -/
theorem relun (n k : ℕ) : Agent019.ReLUn n k = Ref.ReLUn n k := sorry

/-- The two readings of Theorem 2 are *not* equivalent: the left side is false
(`agent_side_false`), while the right side is the real Theorem 2, which is true.
Honest `sorry`: discharging it needs the true direction of `Ref.theorem2`, which is itself
`sorry`-ed in both files, and routing through it is forbidden. -/
theorem statement_ne :
    ¬ ((∀ n, 3 ≤ n → Agent019.CPWL n = Agent019.ReLUn n (Agent019.depthBound n)) ↔
      (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n))) := by
  intro hiff
  exact agent_side_false (hiff.2 (by sorry))

end Star_019

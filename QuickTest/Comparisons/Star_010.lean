import QuickTest.Formalizations.Thm2_010
import QuickTest.Reference

namespace Star_010

/-!
# Star comparison: `Agent010` vs `Ref`

* `depthBound` is *literally* the same term (`⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`), so `depth`
  is `rfl`.
* `ReLUn` agrees: both files read `ReLU_{n,k}` as **at most** `k` hidden layers, and the two
  network predicates differ only in bookkeeping (`Agent010` states the last step as an
  equality of functions, `Ref` as a pointwise equality, and the affine-map structures are
  the same pair `(matrix, translation)` under two names).  Proved below by induction.
* `CPWL` does **not** agree.  `Agent010.CPWL` asks that every point have a *neighbourhood*
  (`∀ᶠ y in nhds x`) on which `f` equals one member of a finite affine family.  On connected
  `ℝⁿ` that forces `f` to be globally affine, so it is strictly stronger than the reference's
  polyhedral-cover definition: `cpwl` is false and we prove `cpwl_ne`.
* Consequently the `Agent010` reading of Theorem 2 is *outright false* — `relu` of a
  coordinate is a one-hidden-layer network but is not locally affine at the origin.  That is
  `agent_side_false`, which needs no reference theorem at all.
-/

/-- The two network predicates denote the same thing. -/
private lemma net_iff (k : ℕ) : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent010.NetComputes n k f ↔ Ref.ComputedBy n k f := by
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨T, hT⟩
      exact ⟨⟨T.A, T.c⟩, hT⟩
    · rintro ⟨T, hT⟩
      exact ⟨⟨T.M, T.c⟩, hT⟩
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, T, g, hg, hf⟩
      exact ⟨m, ⟨T.A, T.c⟩, g, (ih m g).1 hg, fun x => congrFun hf x⟩
    · rintro ⟨m, T, g, hg, hf⟩
      exact ⟨m, ⟨T.M, T.c⟩, g, (ih m g).2 hg, funext hf⟩

theorem relun (n k : ℕ) : Agent010.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent010.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (net_iff j n f).1 hf⟩
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (net_iff j n f).2 hf⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent010.depthBound n = Ref.depthBound n := rfl

/-- Every halfspace is a polyhedron (the intersection of the one-element family). -/
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

/-- `x ↦ max 0 (x 0)` is *not* in `Agent010.CPWL`: agreement with one affine map on a whole
neighbourhood of the origin gives `max 0 t = a * t + b` for all small `t`, and testing at
`t = 0, ε/2, -ε/2` forces `ε ≤ 0`. -/
private lemma max_not_mem (n : ℕ) :
    (fun x : Fin (n + 1) → ℝ => max 0 (x 0)) ∉ Agent010.CPWL (n + 1) := by
  rintro ⟨-, m, φ, hloc⟩
  obtain ⟨i, hi⟩ := hloc (fun _ => (0 : ℝ))
  have htend : Filter.Tendsto (fun t : ℝ => (fun _ => t : Fin (n + 1) → ℝ)) (nhds 0)
      (nhds (fun _ => (0 : ℝ))) := (continuous_pi fun _ => continuous_id).tendsto 0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (htend.eventually hi)
  have key : ∀ t : ℝ, |t| < ε → max 0 t = (∑ j, (φ i).A 0 j) * t + (φ i).c 0 := by
    intro t ht
    have hd : dist t (0 : ℝ) < ε := by rw [Real.dist_eq, sub_zero]; exact ht
    simpa [Agent010.AffineMap.eval, Matrix.mulVec, dotProduct, Finset.sum_mul] using hball hd
  have h0 := key 0 (by simpa using hε)
  have h1 := key (ε / 2) (by rw [abs_of_pos (by linarith : (0 : ℝ) < ε / 2)]; linarith)
  have h2 := key (-(ε / 2)) (by rw [abs_of_neg (by linarith : -(ε / 2) < (0 : ℝ))]; linarith)
  rw [max_self, mul_zero, zero_add] at h0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ ε / 2), ← h0, add_zero] at h1
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0 : ℝ)), ← h0, add_zero, mul_neg] at h2
  linarith

/-- `Agent010.CPWL` is strictly stronger than `Ref.CPWL`, so the two differ. -/
theorem cpwl_ne : ∃ n, Agent010.CPWL n ≠ Ref.CPWL n :=
  ⟨1, fun h => max_not_mem 0 (by rw [h]; exact max_mem_ref)⟩

/-- `max 0 (x 0)` on `ℝ³` is computed by one hidden layer, hence lies in `Agent010.ReLUn`. -/
private lemma relu3_mem :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent010.ReLUn 3 (Agent010.depthBound 3) := by
  refine ⟨1, Nat.le_add_left 1 _, ?_⟩
  refine ⟨1, ⟨Matrix.of fun _ j => if j = 0 then (1 : ℝ) else 0, 0⟩, fun y => y 0,
    ⟨⟨1, 0⟩, fun y => ?_⟩, ?_⟩
  · simp [Agent010.AffineMap.eval, Matrix.mulVec, dotProduct, Matrix.one_apply,
      Fin.sum_univ_one]
  · funext x
    simp [Agent010.AffineMap.eval, Agent010.reluVec, Agent010.relu, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]

/-- The `Agent010` reading of Theorem 2 is outright false: its neighbourhood-agreement
`CPWL` misses `relu`, which its own `ReLUn` contains. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent010.CPWL n = Agent010.ReLUn n (Agent010.depthBound n)) := by
  intro h
  have hmem : (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent010.CPWL 3 := by
    rw [h 3 (by norm_num)]; exact relu3_mem
  exact max_not_mem 2 hmem

/-- Honest `sorry`: the left-hand side of the iff is *false* (`agent_side_false`), so the
iff holds exactly when the right-hand side fails.  But the right-hand side is the genuine
Theorem 2, which is `sorry`-ed in `Reference.lean`; proving or refuting it here is the whole
content of the paper, and routing through `Ref.theorem2` would prove nothing. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent010.CPWL n = Agent010.ReLUn n (Agent010.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_010

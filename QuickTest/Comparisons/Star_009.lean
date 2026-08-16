import QuickTest.Formalizations.Thm2_009
import QuickTest.Reference

namespace Star_009

/-!
# Star comparison: `Agent009` vs `Ref`

* `depthBound`: same term up to `↑(n - 1)` (ℕ-subtraction) vs `(n : ℝ) - 1`; equal for `n ≥ 1`.
* `ReLUn`: both files take **at most** `k` hidden layers, and the two recursive network
  predicates differ only bureaucratically (`Ref` packs the affine layer into a structure
  `Aff`, `Agent009` uses a predicate `IsAffineMap` on a bare function).  Proved by induction.
* `CPWL`: the doc comment advertises "a genuine finite polyhedral-subdivision style
  piecewise-linearity condition", but the actual definition is *local agreement*:
  `∀ x, ∃ i, ∀ᶠ y in nhds x, f y = g i y` for a finite family of **globally fixed** affine
  functionals.  There is no polyhedral cover at all, and on connected `ℝⁿ` this forces `f`
  to be globally affine.  So it is strictly stronger than CPWL: `cpwl` is false, and we
  prove `cpwl_ne` together with the bonus `agent_side_false`.
-/

/-! ### `ReLUn` -/

/-- The two network predicates denote the same thing. -/
private lemma computed_iff (k : ℕ) : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent009.ComputesWithHiddenLayers k n f ↔ Ref.ComputedBy n k f := by
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨a, c, h⟩
      refine ⟨⟨Matrix.of fun _ j => a j, fun _ => c⟩, fun x => ?_⟩
      simp [Ref.Aff.eval, Matrix.mulVec, dotProduct, h x]
    · rintro ⟨T, hT⟩
      refine ⟨fun j => T.M 0 j, T.c 0, fun x => ?_⟩
      simpa [Ref.Aff.eval, Matrix.mulVec, dotProduct] using hT x
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, T, g, ⟨A, c, hT⟩, hg, hf⟩
      have hTe : (⟨A, c⟩ : Ref.Aff n m).eval = T := by
        funext x i
        simp [Ref.Aff.eval, Matrix.mulVec, dotProduct, hT x i]
      refine ⟨m, ⟨A, c⟩, g, (ih m g).1 hg, ?_⟩
      rw [hTe]
      exact hf
    · rintro ⟨m, T, g, hg, hf⟩
      refine ⟨m, T.eval, g, ⟨T.M, T.c, fun x i => ?_⟩, (ih m g).2 hg, hf⟩
      simp [Ref.Aff.eval, Matrix.mulVec, dotProduct]

theorem relun (n k : ℕ) : Agent009.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent009.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, hf⟩; exact ⟨j, hj, (computed_iff j n f).1 hf⟩
  · rintro ⟨j, hj, hf⟩; exact ⟨j, hj, (computed_iff j n f).2 hf⟩

/-! ### `depthBound` -/

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent009.depthBound n = Ref.depthBound n := by
  have h1 : (1 : ℕ) ≤ n := le_trans (by norm_num) hn
  unfold Agent009.depthBound Ref.depthBound
  rw [Nat.cast_sub h1, Nat.cast_one]

/-! ### `CPWL` : the local-agreement definition is strictly stronger -/

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

/-- `x ↦ max 0 (x 0)` is *not* in `Agent009.CPWL`.  Local agreement at the origin gives a
radius `r` and a single affine functional with `max 0 t = (∑ w) * t + b` for all `|t| < r`;
`t = 0`, `t = r/2` and `t = -r/2` are jointly contradictory — this is the kink argument. -/
private lemma max_not_mem (n : ℕ) :
    (fun x : Fin (n + 1) → ℝ => max 0 (x 0)) ∉ Agent009.CPWL (n + 1) := by
  rintro ⟨-, m, G, hG, h⟩
  obtain ⟨i, hi⟩ := h 0
  obtain ⟨w, b, hwb⟩ := hG i
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hi
  have key : ∀ t : ℝ, |t| < r → max 0 t = (∑ j, w j) * t + b := by
    intro t ht
    have hd : dist (fun _ => t : Fin (n + 1) → ℝ) (0 : Fin (n + 1) → ℝ) < r := by
      rw [dist_pi_lt_iff hr]
      intro j
      simpa [Real.dist_eq] using ht
    simpa [hwb, Finset.sum_mul] using hball hd
  have h0 := key 0 (by simpa using hr)
  have h1 := key (r / 2) (by rw [abs_of_pos] <;> linarith)
  have h2 := key (-(r / 2)) (by rw [abs_of_neg] <;> linarith)
  rw [max_self] at h0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ r / 2)] at h1
  rw [max_eq_left (by linarith : -(r / 2) ≤ (0 : ℝ))] at h2
  nlinarith [h0, h1, h2]

/-- `Agent009.CPWL` is strictly stronger than `Ref.CPWL`, so the two differ. -/
theorem cpwl_ne : ∃ n, Agent009.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  have hmem : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent009.CPWL 1 := by
    rw [h]; exact max_mem_ref
  exact max_not_mem 0 hmem

/-! ### The bonus obligation -/

/-- `max 0 (x 0)` on `ℝ³` is a one-hidden-layer network, hence lies in `Agent009.ReLUn`. -/
private lemma relu3_mem :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent009.ReLUn 3 (Agent009.depthBound 3) := by
  have h1 : Agent009.ComputesWithHiddenLayers 1 3 (fun x : Fin 3 → ℝ => max 0 (x 0)) := by
    refine ⟨1, fun x => fun _ => x 0, fun v => v 0,
      ⟨Matrix.of fun _ j => if j = 0 then (1 : ℝ) else 0, 0, fun x i => ?_⟩,
      ⟨fun _ => (1 : ℝ), 0, fun v => ?_⟩, fun x => ?_⟩
    · simp [Fin.sum_univ_three]
    · simp
    · simp [Agent009.reluVec]
  exact ⟨1, Nat.le_add_left 1 _, h1⟩

/-- The `Agent009` reading of Theorem 2 is outright false: its `CPWL` misses `relu`,
which its own `ReLUn` certainly contains.  No reference theorem is needed for this. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent009.CPWL n = Agent009.ReLUn n (Agent009.depthBound n)) := by
  intro h
  have hmem : (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent009.CPWL 3 := by
    rw [h 3 (by norm_num)]; exact relu3_mem
  exact max_not_mem 2 hmem

/-! ### The statement -/

/-- Honest `sorry`.  The left side is false (`agent_side_false`), so the iff is equivalent
to the *negation* of the reference Theorem 2, i.e. it is false.  Refuting it needs the true
direction of `Ref.theorem2`, which is itself `sorry`-ed and which the spec forbids invoking;
there is no other route. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent009.CPWL n = Agent009.ReLUn n (Agent009.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_009

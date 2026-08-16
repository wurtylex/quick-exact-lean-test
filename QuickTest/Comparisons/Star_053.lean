import QuickTest.Formalizations.Thm2_053
import QuickTest.Reference

namespace Star_053

/-!
# Star comparison: `Agent053` vs `Ref`

* `depthBound` is *literally* the same term (`⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1`), so `depth`
  is `rfl`.
* `ReLUn` agrees on the nose: both files take **at most** `k` hidden layers, and the two
  recursive network predicates differ only by the argument order `(k, n)` vs `(n, k)` and
  the name of the affine-map structure.  Proved below by induction.
* `CPWL` does **not** agree.  Despite the doc comment advertising a "polyhedral-subdivision
  flavored" definition, `Agent053.CPWL` actually demands that every point have a
  *neighbourhood* (an `ε`-ball) on which `f` coincides with one of finitely many affine
  functions.  On connected `ℝⁿ` that forces `f` to be globally affine, so the class is
  strictly smaller than the real `CPWL_n`: `cpwl` is false and we prove `cpwl_ne`, plus the
  stronger `agent_side_false`.
-/

/-- The two network predicates denote the same thing; only the argument order and the
name of the affine-map structure differ. -/
private lemma computed_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent053.computesReLUExact k n f ↔ Ref.ComputedBy n k f := by
  intro k
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨T, hT⟩
      exact ⟨⟨T.A, T.c⟩, fun x => (hT x).trans rfl⟩
    · rintro ⟨T, hT⟩
      exact ⟨⟨T.M, T.c⟩, fun x => (hT x).trans rfl⟩
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, T, g, hg, hf⟩
      exact ⟨m, ⟨T.A, T.c⟩, g, (ih m g).1 hg, fun x => (hf x).trans rfl⟩
    · rintro ⟨m, T, g, hg, hf⟩
      exact ⟨m, ⟨T.M, T.c⟩, g, (ih m g).2 hg, fun x => (hf x).trans rfl⟩

theorem relun (n k : ℕ) : Agent053.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent053.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (computed_iff j n f).1 hf⟩
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (computed_iff j n f).2 hf⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent053.depthBound n = Ref.depthBound n := rfl

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

/-- `x ↦ max 0 (x 0)` is *not* in `Agent053.CPWL`: agreement with a single affine map on a
whole ball around the origin would force `max 0 t = a * t + b` for all small `t`, and the
three sample points `t = 0, ε/2, -ε/2` are inconsistent. -/
private lemma max_not_mem (n : ℕ) :
    (fun x : Fin (n + 1) → ℝ => max 0 (x 0)) ∉ Agent053.CPWL (n + 1) := by
  rintro ⟨-, N, pieces, haff, h⟩
  obtain ⟨i, ε, hε, hi⟩ := h 0
  obtain ⟨w, b, hw⟩ := haff i
  have key : ∀ t : ℝ, |t| < ε → max 0 t = (∑ j, w j) * t + b := by
    intro t ht
    have hd : dist (fun _ => t : Fin (n + 1) → ℝ) 0 < ε := by
      rw [dist_pi_lt_iff hε]
      intro j
      simpa [Real.dist_eq] using ht
    have hval := hi (fun _ => t) hd
    rw [hw] at hval
    simpa [Finset.sum_mul] using hval
  have h0 := key 0 (by simpa using hε)
  have h1 := key (ε / 2) (by rw [abs_of_pos] <;> linarith)
  have h2 := key (-(ε / 2)) (by rw [abs_of_neg] <;> linarith)
  rw [max_self] at h0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ ε / 2)] at h1
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0 : ℝ))] at h2
  nlinarith [h0, h1, h2]

/-- `Agent053.CPWL` is strictly stronger than `Ref.CPWL`, so the two differ. -/
theorem cpwl_ne : ∃ n, Agent053.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  have hmem : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent053.CPWL 1 := by
    rw [h]; exact max_mem_ref
  exact max_not_mem 0 hmem

/-- `max 0 (x 0)` on `ℝ³` is computed by a one-hidden-layer network: read off the first
coordinate, apply `ReLU`, then read off the (single) output. -/
private lemma relu_computed :
    Agent053.computesReLUExact 1 3 (fun x : Fin 3 → ℝ => max 0 (x 0)) := by
  refine ⟨1, ⟨Matrix.of fun _ j => if j = 0 then (1 : ℝ) else 0, 0⟩,
    (fun v : Fin 1 → ℝ => v 0), ⟨⟨1, 0⟩, fun x => ?_⟩, fun x => ?_⟩
  · simp [Agent053.AffineMap.apply, Matrix.one_mulVec]
  · simp [Agent053.AffineMap.apply, Agent053.reluVec, Agent053.relu, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three]

private lemma relu3_mem :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent053.ReLUn 3 (Agent053.depthBound 3) :=
  ⟨1, Nat.le_add_left 1 _, relu_computed⟩

/-- The `Agent053` reading of Theorem 2 is outright false: its `CPWL` is a class of globally
affine functions, so it misses `relu`, which its own `ReLUn` certainly contains. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent053.CPWL n = Agent053.ReLUn n (Agent053.depthBound n)) := by
  intro h
  have hmem : (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent053.CPWL 3 := by
    rw [h 3 (by norm_num)]; exact relu3_mem
  exact max_not_mem 2 hmem

/-- The two readings of Theorem 2 are *not* equivalent: the left side is false
(`agent_side_false`), while the right side is the real Theorem 2, which is true.
Honest `sorry`: discharging it needs the true content of `Ref.theorem2`, which is itself
`sorry`-ed in the reference file, and routing through it is forbidden. -/
theorem statement_ne :
    ¬ ((∀ n, 3 ≤ n → Agent053.CPWL n = Agent053.ReLUn n (Agent053.depthBound n)) ↔
      (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n))) := by
  intro hiff
  exact agent_side_false (hiff.2 (by sorry))

end Star_053

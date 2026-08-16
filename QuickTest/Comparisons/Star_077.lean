import QuickTest.Formalizations.Thm2_077
import QuickTest.Reference

namespace Star_077

/-!
# Star comparison: `Agent077` vs `Ref`

* `depthBound` is *literally* the same term (`⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`), so `depth`
  is `rfl`.
* `ReLUn` agrees: both files read `ReLU_{n,k}` as **at most** `k` hidden layers, and the two
  recursive network predicates (`Ref.ComputedBy` / `Agent077.Computes`) are the same
  definition up to the field name of the affine-map structure (`Ref.Aff.M` / `Agent077.Affine.A`).
  Proved by induction on the number of layers.
* `CPWL` does **not** agree.  Despite its doc comment ("a finite atlas of local affine
  pieces"), `Agent077.CPWL` demands that around *every* point `f` agree with one member of a
  finite affine family on a whole ball (`∃ ε > 0, ∀ y, dist y x < ε → f y = g i y`).  On
  connected `ℝⁿ` that forces `f` to be globally affine, so it is strictly stronger than the
  reference's polyhedral-cover condition: `cpwl` is false and we prove `cpwl_ne`.
  In fact the whole `Agent077` reading of Theorem 2 is false (`agent_side_false`).
-/

/-- The two network predicates denote the same thing; they differ only in the field name of
the affine-transformation structure (`Ref.Aff.M` vs `Agent077.Affine.A`). -/
private lemma computes_iff (k : ℕ) : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent077.Computes n k f ↔ Ref.ComputedBy n k f := by
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨T, hT⟩; exact ⟨⟨T.A, T.c⟩, hT⟩
    · rintro ⟨T, hT⟩; exact ⟨⟨T.M, T.c⟩, hT⟩
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, T, g, hg, hf⟩
      exact ⟨m, ⟨T.A, T.c⟩, g, (ih m g).1 hg, hf⟩
    · rintro ⟨m, T, g, hg, hf⟩
      exact ⟨m, ⟨T.M, T.c⟩, g, (ih m g).2 hg, hf⟩

theorem relun (n k : ℕ) : Agent077.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent077.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, hf⟩; exact ⟨j, hj, (computes_iff j n f).1 hf⟩
  · rintro ⟨j, hj, hf⟩; exact ⟨j, hj, (computes_iff j n f).2 hf⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent077.depthBound n = Ref.depthBound n := rfl

/-- Every halfspace is a polyhedron (the intersection of the one-element family). -/
private lemma poly_of_half {n : ℕ} {S : Set (Fin n → ℝ)} (h : Ref.IsHalfspace n S) :
    Ref.IsPolyhedron n S :=
  ⟨1, fun _ => S, fun _ => h, by rw [Set.iInter_const]⟩

/-- `x ↦ max 0 (x 0)` is CPWL in the reference sense: the two halflines `{x 0 ≤ 0}` and
`{-x 0 ≤ 0}` are polyhedra covering `ℝ`, and `f` is affine on each. -/
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

/-- `x ↦ max 0 (x 0)` is **not** in `Agent077.CPWL`: neighbourhood agreement with a single
affine map at the origin forces `max 0 t = a * t + b` for all small `t`, and the kink at
`0` refutes that (`t = 0` gives `b = 0`, `t = r/2` gives `a = 1`, `t = -r/2` gives `0 = r/2`). -/
private lemma max_not_mem (n : ℕ) :
    (fun x : Fin (n + 1) → ℝ => max 0 (x 0)) ∉ Agent077.CPWL (n + 1) := by
  rintro ⟨-, m, g, haff, hloc⟩
  obtain ⟨i, r, hr, hi⟩ := hloc 0
  obtain ⟨w, b, hw⟩ := haff i
  have key : ∀ t : ℝ, |t| < r → max 0 t = (∑ j, w j) * t + b := by
    intro t ht
    have hd : dist (fun _ => t : Fin (n + 1) → ℝ) 0 < r := by
      rw [dist_pi_lt_iff hr]
      intro j
      simpa [Real.dist_eq] using ht
    have h := hi (fun _ => t) hd
    rw [hw] at h
    simpa [Finset.sum_mul] using h
  have h0 := key 0 (by simpa using hr)
  have h1 := key (r / 2) (by rw [abs_of_pos] <;> linarith)
  have h2 := key (-(r / 2)) (by rw [abs_of_neg] <;> linarith)
  rw [max_self] at h0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ r / 2)] at h1
  rw [max_eq_left (by linarith : -(r / 2) ≤ (0 : ℝ))] at h2
  nlinarith [h0, h1, h2]

/-- **Refutation of `cpwl`.** `Agent077.CPWL` is strictly stronger than `Ref.CPWL`; the
function `x ↦ max 0 (x 0)` on `ℝ¹` separates them. -/
theorem cpwl_ne : ∃ n, Agent077.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  have hmem : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent077.CPWL 1 := by
    rw [h]; exact max_mem_ref
  exact max_not_mem 0 hmem

/-- `x ↦ max 0 (x 0)` on `ℝ³` is a one-hidden-layer ReLU network, hence lies in
`Agent077.ReLUn 3 (depthBound 3)` since `depthBound 3 = ⌈log₃ 2⌉₊ + 1 ≥ 1`. -/
private lemma relu3_mem :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent077.ReLUn 3 (Agent077.depthBound 3) := by
  have h0 : Agent077.Computes 1 0 (fun y : Fin 1 → ℝ => y 0) :=
    ⟨⟨1, 0⟩, by intro x; simp [Agent077.Affine.eval, Matrix.one_mulVec]⟩
  have h1 : Agent077.Computes 3 1 (fun x : Fin 3 → ℝ => max 0 (x 0)) := by
    refine ⟨1, ⟨Matrix.of fun _ j => if j = 0 then (1 : ℝ) else 0, 0⟩,
      (fun y : Fin 1 → ℝ => y 0), h0, fun x => ?_⟩
    simp [Agent077.Affine.eval, Agent077.reluVec, Agent077.relu, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]
  exact ⟨1, Nat.le_add_left 1 _, h1⟩

/-- **Bonus.** The `Agent077` reading of Theorem 2 is outright false — no reference theorem
needed: its neighbourhood-agreement `CPWL` consists of globally affine functions, so it misses
the one-hidden-layer network `x ↦ max 0 (x 0)`. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent077.CPWL n = Agent077.ReLUn n (Agent077.depthBound n)) := by
  intro h
  have hmem : (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent077.CPWL 3 := by
    rw [h 3 (by norm_num)]; exact relu3_mem
  exact max_not_mem 2 hmem

/-- The two readings of Theorem 2 are **not** equivalent: the left side is false
(`agent_side_false`), while the right side is the genuine Theorem 2, which is true.
Honest `sorry`: closing it requires *proving* `Ref.theorem2`, the entire content of the
paper, and routing through the `sorry`-ed `Ref.theorem2` is forbidden. -/
theorem statement_ne :
    ¬ ((∀ n, 3 ≤ n → Agent077.CPWL n = Agent077.ReLUn n (Agent077.depthBound n)) ↔
      (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n))) := by
  intro hiff
  exact agent_side_false (hiff.2 (by sorry))

end Star_077

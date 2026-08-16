import QuickTest.Formalizations.Thm2_066
import QuickTest.Reference

namespace Star_066

/-!
# Star comparison: `Agent066` vs `Ref`

* `depthBound` is *literally* the same term (`⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1`), so `depth`
  is `rfl`.
* `ReLUn` agrees: both take **at most** `k` hidden layers, and the two recursive network
  predicates differ only in that `Ref` bundles each layer's affine map into `Ref.Aff`.
* `CPWL` does **not** agree: `Agent066.CPWL` asks for agreement with one member of a finite
  family of affine maps on a *neighbourhood* (`=ᶠ[nhds x]`) of every point, which on
  connected `ℝⁿ` forces global affineness.  So `cpwl` is false: we prove `cpwl_ne`, and in
  fact the whole `Agent066` reading of Theorem 2 is false (`agent_side_false`).
-/

/-- Restriction of an affine functional to the diagonal line `t ↦ (t, …, t)` is affine
in `t`, with slope `A.linear 1` and intercept `A 0`. -/
private lemma affine_line {N : ℕ} (A : (Fin N → ℝ) →ᵃ[ℝ] ℝ) (t : ℝ) :
    A (fun _ => t) = t * A.linear (fun _ => 1) + A 0 := by
  have h1 : (fun _ : Fin N => t) = t • (fun _ : Fin N => (1 : ℝ)) := by
    funext j; simp
  have h2 := A.map_vadd (0 : Fin N → ℝ) (t • (fun _ : Fin N => (1 : ℝ)))
  rw [h1]
  simpa using h2

/-- The two network predicates denote the same thing. -/
private lemma computedBy_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent066.ReLUComputable n k f ↔ Ref.ComputedBy n k f := by
  intro k
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨A, b, hf⟩; exact ⟨⟨A, b⟩, hf⟩
    · rintro ⟨T, hf⟩; exact ⟨T.M, T.c, hf⟩
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, A, b, g, hg, hf⟩; exact ⟨m, ⟨A, b⟩, g, (ih m g).1 hg, hf⟩
    · rintro ⟨m, T, g, hg, hf⟩; exact ⟨m, T.M, T.c, g, (ih m g).2 hg, hf⟩

theorem relun (n k : ℕ) : Agent066.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent066.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, hf⟩; exact ⟨j, hj, (computedBy_iff j n f).1 hf⟩
  · rintro ⟨j, hj, hf⟩; exact ⟨j, hj, (computedBy_iff j n f).2 hf⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent066.depthBound n = Ref.depthBound n := rfl

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

/-- `x ↦ max 0 (x 0)` is *not* in `Agent066.CPWL`: neighbourhood agreement with a single
affine map at the origin forces `max 0 t = a * t + b` for all small `t`, which is absurd
(`t = 0` gives `b = 0`, `t = r/2` gives `a = 1`, `t = -r/2` then gives `0 = -r/2`). -/
private lemma max_not_mem (n : ℕ) :
    (fun x : Fin (n + 1) → ℝ => max 0 (x 0)) ∉ Agent066.CPWL (n + 1) := by
  rintro ⟨-, m, g, hg⟩
  obtain ⟨i, hi⟩ := hg (fun _ => (0 : ℝ))
  have hi' : ∀ᶠ y : Fin (n + 1) → ℝ in nhds (fun _ => (0 : ℝ)),
      max 0 (y 0) = (g i) y := hi
  have hc : Continuous (fun t : ℝ => (fun _ : Fin (n + 1) => t)) :=
    continuous_pi fun _ => continuous_id
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 ((hc.tendsto 0).eventually hi')
  have key : ∀ t : ℝ, |t| < r →
      max 0 t = t * (g i).linear (fun _ => 1) + (g i) 0 := by
    intro t ht
    have hd : dist t (0 : ℝ) < r := by rwa [Real.dist_eq, sub_zero]
    exact (hball hd).trans (affine_line (g i) t)
  have h0 := key 0 (by simpa using hr)
  have h1 := key (r / 2) (by rw [abs_of_pos] <;> linarith)
  have h2 := key (-(r / 2)) (by rw [abs_of_neg] <;> linarith)
  rw [max_self] at h0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ r / 2)] at h1
  rw [max_eq_left (by linarith : -(r / 2) ≤ (0 : ℝ))] at h2
  nlinarith [h0, h1, h2]

/-- `Agent066.CPWL` (local agreement) is strictly stronger than `Ref.CPWL`, so the two
sets differ already at `n = 1`. -/
theorem cpwl_ne : ∃ n, Agent066.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  have hmem : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent066.CPWL 1 := by
    rw [h]; exact max_mem_ref
  exact max_not_mem 0 hmem

/-- `max 0 (x 0)` on `ℝ³` is computed by one hidden layer, hence lies in `Agent066.ReLUn`. -/
private lemma relu3_mem :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent066.ReLUn 3 (Agent066.depthBound 3) := by
  refine ⟨1, Nat.le_add_left 1 _, 1, Matrix.of fun _ j => if j = 0 then (1 : ℝ) else 0, 0,
    fun v : Fin 1 → ℝ => v 0, ⟨1, 0, ?_⟩, ?_⟩
  · intro v
    simp [Matrix.one_mulVec]
  · intro x
    simp [Agent066.reluVec, Agent066.relu, Matrix.mulVec, dotProduct, Matrix.one_apply,
      Fin.sum_univ_one, Fin.sum_univ_three]

/-- The `Agent066` reading of Theorem 2 is outright false: its `CPWL` misses `relu`, which
its own `ReLUn` contains.  No reference theorem is needed for this. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent066.CPWL n = Agent066.ReLUn n (Agent066.depthBound n)) := by
  intro h
  have hmem : (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent066.CPWL 3 := by
    rw [h 3 (by norm_num)]; exact relu3_mem
  exact max_not_mem 2 hmem

/-- Since the agent side is false, the comparison `↔` says exactly that the reference side
fails too.  So refuting it is *equivalent* to disproving the real Theorem 2. -/
theorem statement_iff_ref_false :
    ((∀ n, 3 ≤ n → Agent066.CPWL n = Agent066.ReLUn n (Agent066.depthBound n)) ↔
      (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n))) ↔
    ¬ (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) :=
  ⟨fun h hr => agent_side_false (h.2 hr),
   fun h => ⟨fun ha => absurd ha agent_side_false, fun hr => absurd hr h⟩⟩

/-- Honest `sorry`.  By `statement_iff_ref_false` this `↔` is *false* iff the reference
side (the true Theorem 2) holds, so both proving and refuting it require the reference
Theorem 2, which is `sorry`-ed in `Reference.lean`; routing through it is forbidden. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent066.CPWL n = Agent066.ReLUn n (Agent066.depthBound n)) ↔
      (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_066

import QuickTest.Formalizations.Thm2_048
import QuickTest.Reference

namespace Star_048

/-!
`Agent048` vs `Ref`.

* `ReLUn` and `depthBound` agree on the nose (both use *at most* `k` hidden
  layers, and the two affine-map structures carry the same data).
* `CPWL` does **not** agree.  Despite the "polyhedral-subdivision-style" prose
  in the docstring, `Agent048.CPWL` contains no polyhedra: it asks that every
  point have a *neighbourhood* on which `f` coincides with one of finitely many
  affine functions.  On connected `ℝⁿ` that forces `f` to be globally affine,
  so it is strictly stronger than the reference's polyhedral-cover condition —
  see `cpwl_ne`, and `agent_side_false` for the stronger, reference-free claim.
-/

/-- `Agent048.Computes k n` and `Ref.ComputedBy n k` are the same predicate:
the two affine-map structures carry the same data, and `Matrix.mulVec` unfolds
definitionally to the reference's explicit sum. -/
private lemma computes_iff (k n : ℕ) (f : (Fin n → ℝ) → ℝ) :
    Agent048.Computes k n f ↔ Ref.ComputedBy n k f := by
  induction k generalizing n f with
  | zero =>
      constructor
      · rintro ⟨T, hT⟩; exact ⟨⟨T.A, T.c⟩, hT⟩
      · rintro ⟨T, hT⟩; exact ⟨⟨T.M, T.c⟩, hT⟩
  | succ k ih =>
      constructor
      · rintro ⟨m, T, g, hg, hf⟩
        exact ⟨m, ⟨T.A, T.c⟩, g, (ih m g).1 hg, hf⟩
      · rintro ⟨m, T, g, hg, hf⟩
        exact ⟨m, ⟨T.M, T.c⟩, g, (ih m g).2 hg, hf⟩

theorem relun (n k : ℕ) : Agent048.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent048.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  exact exists_congr fun j => and_congr_right fun _ => computes_iff j n f

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent048.depthBound n = Ref.depthBound n := rfl

/-- The kink function `x ↦ max 0 x₀` is not in `Agent048.CPWL n`: neighbourhood
agreement at the origin with a single affine `g i` forces `max 0 t = c t + b`
for all small `t`, which is contradictory. -/
private lemma kink_not_agent (n : ℕ) [NeZero n] :
    (fun x : Fin n → ℝ => max 0 (x 0)) ∉ Agent048.CPWL n := by
  intro hmem
  simp only [Agent048.CPWL, Set.mem_setOf_eq] at hmem
  obtain ⟨-, N, g, hg, hloc⟩ := hmem
  obtain ⟨i, hi⟩ := hloc (fun _ => (0 : ℝ))
  obtain ⟨a, b, hab⟩ := hg i
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ∀ t : ℝ, g i (fun _ => t) = c * t + b :=
    ⟨∑ j, a j, fun t => by simp [hab, Finset.sum_mul]⟩
  have hcont : Continuous (fun t : ℝ => (fun _ => t : Fin n → ℝ)) :=
    continuous_pi fun _ => continuous_id
  have h1 : ∀ᶠ t : ℝ in nhds (0 : ℝ), max 0 t = c * t + b := by
    filter_upwards [(hcont.tendsto (0 : ℝ)).eventually hi] with t ht
    simpa [hc] using ht
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 h1
  have e0 : max 0 (0 : ℝ) = c * 0 + b := hball (by simpa using hε)
  have e1 : max 0 (ε / 2) = c * (ε / 2) + b := by
    refine hball ?_
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
    linarith
  have e2 : max 0 (-(ε / 2)) = c * (-(ε / 2)) + b := by
    refine hball ?_
    rw [Real.dist_eq, sub_zero, abs_of_neg (by linarith)]
    linarith
  rw [max_self] at e0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ ε / 2)] at e1
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0 : ℝ))] at e2
  nlinarith [e0, e1, e2]

/-- The two halfspaces `{x₀ ≤ 0}` and `{-x₀ ≤ 0}` of `ℝ¹`. -/
private def P : Fin 2 → Set (Fin 1 → ℝ) :=
  ![{x | (∑ i, (1 : ℝ) * x i) ≤ 0}, {x | (∑ i, (-1 : ℝ) * x i) ≤ 0}]

/-- The two affine pieces `0` and `x ↦ x₀`. -/
private def Q : Fin 2 → ((Fin 1 → ℝ) → ℝ) := ![fun _ => 0, fun x => x 0]

/-- The same kink function *is* in `Ref.CPWL 1`: the two halfspaces above are a
polyhedral cover of `ℝ¹` on which it agrees with `Q 0`, `Q 1`. -/
private lemma kink_mem_ref : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Ref.CPWL 1 := by
  show Ref.IsCPWL 1 (fun x : Fin 1 → ℝ => max 0 (x 0))
  refine ⟨continuous_const.max (continuous_apply 0), 2, P, Q, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨1, fun _ => P i, fun _ => ?_, (Set.iInter_const _).symm⟩
    fin_cases i
    · exact ⟨fun _ => 1, 0, rfl⟩
    · exact ⟨fun _ => -1, 0, rfl⟩
  · intro i
    fin_cases i
    · exact ⟨0, 0, fun x => by simp [Q]⟩
    · exact ⟨fun _ => 1, 0, fun x => by simp [Q]⟩
  · refine Set.eq_univ_of_forall fun x => ?_
    rcases le_total (x 0) 0 with h | h
    · exact Set.mem_iUnion.2 ⟨0, by simpa [P] using h⟩
    · exact Set.mem_iUnion.2 ⟨1, by simpa [P] using h⟩
  · intro i x hx
    fin_cases i
    · have h : x 0 ≤ 0 := by simpa [P] using hx
      show max 0 (x 0) = 0
      exact max_eq_left h
    · have h : (0 : ℝ) ≤ x 0 := by simpa [P] using hx
      show max 0 (x 0) = x 0
      exact max_eq_right h

/-- `Agent048.CPWL` is strictly stronger than `Ref.CPWL`, already at `n = 1`. -/
theorem cpwl_ne : ∃ n, Agent048.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => kink_not_agent 1 ?_⟩
  rw [h]
  exact kink_mem_ref

/-- `x ↦ max 0 x₀` on `ℝ³` is a one-hidden-layer ReLU network. -/
private lemma kink_mem_relun :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent048.ReLUn 3 (Agent048.depthBound 3) := by
  show ∃ k' ≤ Agent048.depthBound 3,
    Agent048.Computes k' 3 (fun x : Fin 3 → ℝ => max 0 (x 0))
  refine ⟨1, by simp [Agent048.depthBound], 1,
    ⟨fun _ j => if j = 0 then 1 else 0, 0⟩, fun v => v 0,
    ⟨⟨fun _ _ => 1, 0⟩, fun v => ?_⟩, fun x => ?_⟩
  · simp [Agent048.AffineMap.eval]
  · simp [Agent048.AffineMap.eval, Agent048.reluVec, ite_mul]

/-- The bonus obligation: Agent048's own Theorem 2 is false, no reference
needed.  At `n = 3` the kink function is a one-hidden-layer network but is not
in `Agent048.CPWL 3`. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent048.CPWL n = Agent048.ReLUn n (Agent048.depthBound n)) := by
  intro h
  refine kink_not_agent 3 ?_
  rw [h 3 le_rfl]
  exact kink_mem_relun

/-- `statement` itself is **false** and so is not stated positively: its left
side is refuted by `agent_side_false`, so the `↔` would force the reference
side of Theorem 2 to be false as well.  Refuting the `↔` is therefore exactly
proving `Ref.theorem2` — the whole mathematical content of arXiv:2505.14338,
which is `sorry` in `Reference.lean`.  Honest `sorry`. -/
theorem statement_ne :
    ¬ ((∀ n, 3 ≤ n → Agent048.CPWL n = Agent048.ReLUn n (Agent048.depthBound n)) ↔
      (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n))) := sorry

end Star_048

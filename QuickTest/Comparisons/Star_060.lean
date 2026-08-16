import QuickTest.Formalizations.Thm2_060
import QuickTest.Reference

namespace Star_060

/-!
# Star comparison: `Agent060` vs `Ref`

* `depthBound` — literally the same definition; `rfl`.
* `ReLUn` — same "at most `k`" reading, same alternating-composition recursion;
  the only gap is the repackaging `AffMap ↔ Aff`, so the two are provably equal.
* `CPWL` — `Agent060` uses the *pointwise / neighbourhood-agreement* form, which
  on connected `ℝⁿ` forces `f` to be globally affine.  Strictly stronger than
  `Ref.IsCPWL`, so `cpwl` is **false** and we prove `cpwl_ne`.
-/

/-! ## `ReLUn` -/

/-- The two network predicates agree: `Agent060.represents` and `Ref.ComputedBy`
are the same alternating composition, modulo `AffMap` vs `Aff`. -/
private lemma computedBy_iff (n k : ℕ) (f : Agent060.Vec n → ℝ) :
    Agent060.represents n k f ↔ Ref.ComputedBy n k (show (Fin n → ℝ) → ℝ from f) := by
  induction k generalizing n f with
  | zero =>
    constructor
    · rintro ⟨T, hT⟩
      exact ⟨⟨T.A, T.bias⟩, hT⟩
    · rintro ⟨T, hT⟩
      exact ⟨⟨T.M, T.c⟩, hT⟩
  | succ k ih =>
    constructor
    · rintro ⟨m, T, g, hg, hf⟩
      exact ⟨m, ⟨T.A, T.bias⟩, g, (ih m g).1 hg, hf⟩
    · rintro ⟨m, T, g, hg, hf⟩
      exact ⟨m, ⟨T.M, T.c⟩, g, (ih m g).2 hg, hf⟩

theorem relun (n k : ℕ) : Agent060.ReLUn n k = Ref.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, (computedBy_iff n j f).1 h⟩
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, (computedBy_iff n j f).2 h⟩

/-! ## `depthBound` -/

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent060.depthBound n = Ref.depthBound n := rfl

/-! ## `CPWL` : refutation -/

/-- The separating witness `x ↦ max 0 (x 0)` on `ℝ¹`. -/
private def fwit : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

/-- `fwit` is a genuine CPWL function in the reference (polyhedral-cover) sense:
the two halflines `{x 0 ≤ 0}` and `{-x 0 ≤ 0}` cover `ℝ¹`. -/
private lemma fwit_mem_ref : fwit ∈ Ref.CPWL 1 := by
  refine ⟨Continuous.max continuous_const (continuous_apply 0), 2,
    ![{x : Fin 1 → ℝ | (∑ i, (1 : ℝ) * x i) ≤ 0},
      {x : Fin 1 → ℝ | (∑ i, (-1 : ℝ) * x i) ≤ 0}],
    ![fun _ => 0, fun x => x 0], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact ⟨1, fun _ => {x : Fin 1 → ℝ | (∑ i, (1 : ℝ) * x i) ≤ 0},
        fun _ => ⟨fun _ => (1 : ℝ), 0, rfl⟩, (Set.iInter_const _).symm⟩
    · exact ⟨1, fun _ => {x : Fin 1 → ℝ | (∑ i, (-1 : ℝ) * x i) ≤ 0},
        fun _ => ⟨fun _ => (-1 : ℝ), 0, rfl⟩, (Set.iInter_const _).symm⟩
  · intro i
    fin_cases i
    · exact ⟨0, 0, by intro x; simp⟩
    · exact ⟨fun _ => (1 : ℝ), 0, by intro x; simp⟩
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    rcases le_total (x 0) 0 with h | h
    · exact ⟨0, by simpa [Fin.sum_univ_one] using h⟩
    · exact ⟨1, by simpa [Fin.sum_univ_one] using h⟩
  · intro i
    fin_cases i
    · intro x hx
      have hx0 : x 0 ≤ 0 := by simpa [Fin.sum_univ_one] using hx
      simp [fwit, max_eq_left hx0]
    · intro x hx
      have hx0 : (0 : ℝ) ≤ x 0 := by simpa [Fin.sum_univ_one] using hx
      simp [fwit, max_eq_right hx0]

/-- `fwit` is **not** in `Agent060.CPWL 1`: agreeing with a single affine map on a
whole neighbourhood of `0` is impossible for `max 0 ·`. -/
private lemma fwit_not_mem_agent : fwit ∉ Agent060.CPWL 1 := by
  intro hmem
  obtain ⟨-, S, hS, hcov⟩ := hmem
  obtain ⟨g, hgS, U, hU, h0U, hEq⟩ := hcov (fun _ => (0 : ℝ))
  obtain ⟨a, b, hab⟩ := hS g hgS
  have hc : Continuous (fun t : ℝ => (fun _ => t : Fin 1 → ℝ)) :=
    continuous_pi fun _ => continuous_id
  have hV : IsOpen ((fun t : ℝ => (fun _ => t : Fin 1 → ℝ)) ⁻¹' U) := hU.preimage hc
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV 0 h0U
  have key : ∀ t : ℝ, |t| < ε → max 0 t = a 0 * t + b := by
    intro t ht
    have htU : (fun _ => t : Fin 1 → ℝ) ∈ U :=
      hball (Metric.mem_ball.2 (by rw [Real.dist_eq, sub_zero]; exact ht))
    have h := hEq htU
    simpa [fwit, hab, Fin.sum_univ_one] using h
  have h1 := key 0 (by simpa using hε)
  have h2 := key (ε / 2) (by rw [abs_of_pos (by linarith)]; linarith)
  have h3 := key (-(ε / 2)) (by rw [abs_of_neg (by linarith)]; linarith)
  rw [max_self, mul_zero, zero_add] at h1
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ ε / 2), ← h1, add_zero] at h2
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0 : ℝ)), ← h1, add_zero, mul_neg] at h3
  linarith

/-- `Agent060.CPWL` is the neighbourhood-agreement condition, which is strictly
stronger than the reference's polyhedral-cover condition. -/
theorem cpwl_ne : ∃ n, Agent060.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => fwit_not_mem_agent ?_⟩
  rw [h]
  exact fwit_mem_ref

/-! ## The statement -/

/-- Honest `sorry`.  The two sides are *not* equivalent: `Agent060`'s side is false
(`fwit`-style functions on `ℝⁿ` lie in `ReLUn n (depthBound n)` but not in the
neighbourhood-agreement `CPWL n`), while `Ref`'s side is Theorem 2 itself.  So the
only available proof is `statement_ne`, and refuting the `←` direction requires
proving `Ref.theorem2` — the actual mathematical content, which is out of reach
here and is `sorry`-ed in both source files. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent060.CPWL n = Agent060.ReLUn n (Agent060.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_060

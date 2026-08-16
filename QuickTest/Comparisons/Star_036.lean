import QuickTest.Formalizations.Thm2_036
import QuickTest.Reference

namespace Star_036

/-!
# Agent036 vs the reference

* `depthBound`  — literally the same term, `rfl`.
* `ReLUn`       — the same "at most `k` hidden layers" reading; the only difference is
  the affine-map record (`Agent036.Affine` vs `Ref.Aff`), so the two recursive
  predicates are transported into one another field by field.
* `CPWL`        — **different**.  Agent036 asks for agreement with an affine map on a
  *neighbourhood* of every point (`nhds`).  On connected `ℝⁿ` that forces global
  affineness, so it is strictly stronger than the reference's polyhedral-cover
  condition.  We refute `cpwl` with `wit = fun x => max 0 (x 0)` at `n = 1`.
-/

/-! ### Networks -/

/-- The two network predicates agree; only the affine-map record differs. -/
private lemma netOutput_iff :
    ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ), Agent036.NetOutput n k f ↔ Ref.ComputedBy n k f := by
  intro k
  induction k with
  | zero =>
    intro n f
    constructor
    · intro h
      obtain ⟨T, hT⟩ : ∃ T : Agent036.Affine n 1, ∀ x, f x = T.eval x 0 := h
      show ∃ T : Ref.Aff n 1, ∀ x, f x = T.eval x 0
      exact ⟨⟨T.A, T.c⟩, hT⟩
    · intro h
      obtain ⟨T, hT⟩ : ∃ T : Ref.Aff n 1, ∀ x, f x = T.eval x 0 := h
      show ∃ T : Agent036.Affine n 1, ∀ x, f x = T.eval x 0
      exact ⟨⟨T.M, T.c⟩, hT⟩
  | succ k ih =>
    intro n f
    constructor
    · intro h
      obtain ⟨m, T, g, hg, hf⟩ :
          ∃ (m : ℕ) (T : Agent036.Affine n m) (g : (Fin m → ℝ) → ℝ),
            Agent036.NetOutput m k g ∧ ∀ x, f x = g (Agent036.reluVec (T.eval x)) := h
      show ∃ (m : ℕ) (T : Ref.Aff n m) (g : (Fin m → ℝ) → ℝ),
          Ref.ComputedBy m k g ∧ ∀ x, f x = g (Ref.reluVec (T.eval x))
      exact ⟨m, ⟨T.A, T.c⟩, g, (ih m g).mp hg, hf⟩
    · intro h
      obtain ⟨m, T, g, hg, hf⟩ :
          ∃ (m : ℕ) (T : Ref.Aff n m) (g : (Fin m → ℝ) → ℝ),
            Ref.ComputedBy m k g ∧ ∀ x, f x = g (Ref.reluVec (T.eval x)) := h
      show ∃ (m : ℕ) (T : Agent036.Affine n m) (g : (Fin m → ℝ) → ℝ),
          Agent036.NetOutput m k g ∧ ∀ x, f x = g (Agent036.reluVec (T.eval x))
      exact ⟨m, ⟨T.M, T.c⟩, g, (ih m g).mpr hg, hf⟩

theorem relun (n k : ℕ) : Agent036.ReLUn n k = Ref.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨j, hj, h⟩; exact ⟨j, hj, (netOutput_iff j n f).mp h⟩
  · rintro ⟨j, hj, h⟩; exact ⟨j, hj, (netOutput_iff j n f).mpr h⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent036.depthBound n = Ref.depthBound n := rfl

/-! ### The witness separating the two `CPWL`s -/

/-- `x ↦ max 0 (x 0)` on `ℝ¹`. -/
private noncomputable def wit : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

private def coef : Fin 2 → (Fin 1 → ℝ) := ![fun _ => 1, fun _ => -1]

private def piece (i : Fin 2) : Set (Fin 1 → ℝ) := {x | (∑ j, coef i j * x j) ≤ 0}

private noncomputable def slope : Fin 2 → ((Fin 1 → ℝ) → ℝ) := ![fun _ => 0, fun x => x 0]

private lemma mem_piece (i : Fin 2) (x : Fin 1 → ℝ) : x ∈ piece i ↔ coef i 0 * x 0 ≤ 0 := by
  show (∑ j, coef i j * x j) ≤ 0 ↔ _
  rw [Fin.sum_univ_one]

/-- `wit` is CPWL in the reference sense: two halfspaces, `0` on one and `x 0` on the other. -/
private lemma wit_mem_ref : wit ∈ Ref.CPWL 1 := by
  show Ref.IsCPWL 1 wit
  refine ⟨continuous_const.max (continuous_apply 0), 2, piece, slope, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨1, fun _ => piece i, fun _ => ⟨coef i, 0, rfl⟩, ?_⟩
    exact (Set.iInter_const _).symm
  · intro i
    fin_cases i
    · exact ⟨fun _ => 0, 0, fun x => by simp [slope, Fin.sum_univ_one]⟩
    · exact ⟨fun _ => 1, 0, fun x => by simp [slope, Fin.sum_univ_one]⟩
  · refine Set.eq_univ_of_forall fun x => ?_
    rw [Set.mem_iUnion]
    rcases le_or_gt (x 0) 0 with h | h
    · exact ⟨0, (mem_piece 0 x).mpr (by show (1 : ℝ) * x 0 ≤ 0; linarith)⟩
    · exact ⟨1, (mem_piece 1 x).mpr (by show (-1 : ℝ) * x 0 ≤ 0; linarith)⟩
  · intro i x hx
    rw [mem_piece] at hx
    fin_cases i
    · have h : (1 : ℝ) * x 0 ≤ 0 := hx
      show max 0 (x 0) = 0
      exact max_eq_left (by linarith)
    · have h : (-1 : ℝ) * x 0 ≤ 0 := hx
      show max 0 (x 0) = x 0
      exact max_eq_right (by linarith)

/-- `wit` is *not* CPWL in Agent036's sense: near `0` it would have to coincide with a
single affine map, but `max 0 y = a * y + b` on `|y| < ε` is impossible. -/
private lemma wit_not_mem_agent : wit ∉ Agent036.CPWL 1 := by
  intro hmem
  obtain ⟨-, m, g, hg, hloc⟩ := hmem
  obtain ⟨i, U, hU, hUeq⟩ := hloc 0
  obtain ⟨T, hT⟩ := hg i
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  have key : ∀ w : Fin 1 → ℝ, (∀ j, |w j| < ε) → wit w = (T.A.mulVec w) 0 + T.c 0 := by
    intro w hw
    have hwU : w ∈ U := hball (by
      rw [Metric.mem_ball, dist_pi_lt_iff hε]
      intro j
      simpa [Real.dist_eq] using hw j)
    rw [hUeq w hwU, hT w]
    rfl
  have hpos : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨v, hv0⟩ : ∃ v : Fin 1 → ℝ, v 0 = ε / 2 := ⟨fun _ => ε / 2, rfl⟩
  have hjv : ∀ j : Fin 1, |v j| < ε := by
    intro j
    rw [Subsingleton.elim j 0, hv0, abs_of_pos hpos]
    linarith
  have hjnv : ∀ j : Fin 1, |(-v) j| < ε := by
    intro j
    rw [Subsingleton.elim j 0]
    show |(-(v 0))| < ε
    rw [abs_neg, hv0, abs_of_pos hpos]
    linarith
  have hc : T.c 0 = 0 := by
    have h0 := key 0 (fun j => by simpa using hε)
    simp only [wit, Pi.zero_apply, max_self, Matrix.mulVec_zero, zero_add] at h0
    linarith
  have hv := key v hjv
  have hnv := key (-v) hjnv
  rw [hc, add_zero] at hv hnv
  rw [Matrix.mulVec_neg, Pi.neg_apply] at hnv
  have e1 : wit v = ε / 2 := by
    show max 0 (v 0) = ε / 2
    rw [hv0]; exact max_eq_right hpos.le
  have e2 : wit (-v) = 0 := by
    show max 0 (-(v 0)) = 0
    rw [hv0]; exact max_eq_left (by linarith)
  rw [e1] at hv
  rw [e2] at hnv
  linarith

/-- `cpwl` is **false**: local (neighbourhood) agreement is strictly stronger than the
reference's polyhedral-cover definition. -/
theorem cpwl_ne : ∃ n, Agent036.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => wit_not_mem_agent ?_⟩
  rw [h]
  exact wit_mem_ref

/-- Honest `sorry`.  This iff is in fact **false** (Agent036's side fails: `ReLUn` contains
non-affine functions such as `relu`, which the `nhds` definition of `CPWL` excludes, while
the reference side is the genuine Theorem 2).  Refuting it therefore requires proving
`Ref.theorem2`, the hard direction of the paper, which is itself `sorry`. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent036.CPWL n = Agent036.ReLUn n (Agent036.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_036

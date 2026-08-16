import QuickTest.Formalizations.Thm2_007
import QuickTest.Reference

/-!
# Star comparison: `Agent007` vs `Ref`

`Agent007.depthBound` is syntactically identical to `Ref.depthBound`.

`Agent007.CPWL` is the *neighbourhood-agreement* definition: `f` must agree, on an
open neighbourhood of **every** point, with one member of a fixed finite family of
affine functions.  On connected `ℝⁿ` this forces `f` to be globally affine, so it is
strictly stronger than continuous piecewise linearity.  Hence `cpwl` is false
(`cpwl_ne`), and Agent007's Theorem 2 is itself false (`agent_side_false`).
-/

namespace Star_007

/-- The witness `x ↦ max 0 (x 0)` on `ℝ³`: continuous piecewise linear, but not
affine on any neighbourhood of the origin. -/
noncomputable def wit : (Fin 3 → ℝ) → ℝ := fun x => max 0 (x 0)

private lemma wit_continuous : Continuous wit :=
  continuous_const.max (continuous_apply 0)

private lemma sum_e0 (x : Fin 3 → ℝ) :
    (∑ j, (if j = 0 then (1 : ℝ) else 0) * x j) = x 0 := by
  simp [Fin.sum_univ_three]

private lemma sum_me0 (x : Fin 3 → ℝ) :
    (∑ j, (if j = 0 then (-1 : ℝ) else 0) * x j) = -x 0 := by
  simp [Fin.sum_univ_three]

private lemma mulVec_apply' {a b : ℕ} (A : Matrix (Fin b) (Fin a) ℝ)
    (x : Fin a → ℝ) (i : Fin b) : A.mulVec x i = ∑ j, A i j * x j := rfl

private lemma polyhedron_of_halfspace {n : ℕ} {S : Set (Fin n → ℝ)}
    (h : Ref.IsHalfspace n S) : Ref.IsPolyhedron n S :=
  ⟨1, fun _ => S, fun _ => h, (Set.iInter_const S).symm⟩

/-- The witness is genuinely CPWL in the reference sense: the two halfspaces
`x 0 ≤ 0` and `-x 0 ≤ 0` cover `ℝ³` and `wit` is affine on each. -/
theorem wit_mem_ref : wit ∈ Ref.CPWL 3 := by
  refine ⟨wit_continuous, 2,
    ![{x : Fin 3 → ℝ | (∑ j, (if j = 0 then (1 : ℝ) else 0) * x j) ≤ 0},
      {x : Fin 3 → ℝ | (∑ j, (if j = 0 then (-1 : ℝ) else 0) * x j) ≤ 0}],
    ![fun _ => (0 : ℝ), fun x => x 0], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> exact polyhedron_of_halfspace ⟨_, _, rfl⟩
  · intro i
    fin_cases i
    · exact ⟨0, 0, by simp⟩
    · refine ⟨fun j => if j = 0 then (1 : ℝ) else 0, 0, fun x => ?_⟩
      rw [sum_e0]
      show (x 0 : ℝ) = x 0 + 0
      ring
  · refine Set.eq_univ_of_forall fun x => ?_
    rcases le_or_gt (x 0) 0 with h | h
    · refine Set.mem_iUnion.2 ⟨0, ?_⟩
      show (∑ j, (if j = 0 then (1 : ℝ) else 0) * x j) ≤ 0
      rw [sum_e0]; exact h
    · refine Set.mem_iUnion.2 ⟨1, ?_⟩
      show (∑ j, (if j = 0 then (-1 : ℝ) else 0) * x j) ≤ 0
      rw [sum_me0]; linarith
  · intro i
    fin_cases i
    · intro x hx
      have hx' : (∑ j, (if j = 0 then (1 : ℝ) else 0) * x j) ≤ 0 := hx
      rw [sum_e0] at hx'
      show max (0 : ℝ) (x 0) = 0
      exact max_eq_left hx'
    · intro x hx
      have hx' : (∑ j, (if j = 0 then (-1 : ℝ) else 0) * x j) ≤ 0 := hx
      rw [sum_me0] at hx'
      show max (0 : ℝ) (x 0) = x 0
      exact max_eq_right (by linarith)

/-- The kink at the origin defeats neighbourhood agreement: on the diagonal line
`t ↦ (t,t,t)` the witness is `max 0 t`, which is not affine near `t = 0`. -/
theorem wit_not_mem_agent : wit ∉ Agent007.CPWL 3 := by
  rintro ⟨-, S, hS⟩
  obtain ⟨a, -, U, hU, h0U, hUa⟩ := hS 0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU 0 h0U
  have key : ∀ t : ℝ, |t| < ε → max 0 t = (∑ i : Fin 3, a.1 i) * t + a.2 := by
    intro t ht
    have hmem : (fun _ => t : Fin 3 → ℝ) ∈ Metric.ball (0 : Fin 3 → ℝ) ε := by
      rw [Metric.mem_ball, dist_pi_lt_iff hε]
      intro i
      simpa [Real.dist_eq] using ht
    have h := hUa _ (hball hmem)
    simpa [wit, Agent007.AffineFun.eval, Finset.sum_mul] using h
  have h0 : (0 : ℝ) = a.2 := by simpa using key 0 (by simpa using hε)
  have hp := key (ε / 2) (by rw [abs_of_pos (by linarith)]; linarith)
  have hm := key (-(ε / 2)) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ ε / 2)] at hp
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0 : ℝ)), mul_neg] at hm
  linarith

/-- `wit` is computed by a one-hidden-layer ReLU network. -/
private lemma wit_representable : Agent007.Representable 3 1 wit := by
  refine ⟨1, Agent007.affineEval
      (Matrix.of fun (_ : Fin 1) (j : Fin 3) => if j = 0 then (1 : ℝ) else 0) 0,
    Matrix.of fun (_ : Fin 1) (_ : Fin 1) => (1 : ℝ), 0, ⟨_, _, rfl⟩, ?_⟩
  funext x i
  simp [wit, Agent007.affineEval, Agent007.reluVec, Agent007.relu, mulVec_apply',
    Fin.sum_univ_one, sum_e0]

/-! ## The four obligations -/

/-- `cpwl` is **false**: at `n = 3` the witness lies in `Ref.CPWL` but not in
`Agent007.CPWL`. -/
theorem cpwl_ne : ∃ n, Agent007.CPWL n ≠ Ref.CPWL n :=
  ⟨3, fun h => wit_not_mem_agent (by rw [h]; exact wit_mem_ref)⟩

-- Both sides read "at most `k` hidden layers", but `Agent007.Representable` and
-- `Ref.ComputedBy` peel the layers in different shapes (function equality with a
-- `Fin 1`-valued output versus pointwise equality of scalars).  Identifying them
-- needs an induction on `k` transporting networks across the two encodings; that
-- is real work and is not done here.
theorem relun (n k : ℕ) : Agent007.ReLUn n k = Ref.ReLUn n k := sorry

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent007.depthBound n = Ref.depthBound n := rfl

-- The agent side is false (`agent_side_false` below), so the iff holds iff the
-- reference side is false too.  But the reference side *is* Theorem 2, which is
-- `sorry`-ed in `Reference.lean`; refuting or proving this iff would require
-- proving the real theorem.
theorem statement :
    (∀ n, 3 ≤ n → Agent007.CPWL n = Agent007.ReLUn n (Agent007.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

/-! ## Bonus: Agent007's Theorem 2 is false outright -/

/-- `max 0 (x 0)` is a one-hidden-layer ReLU network on `ℝ³`, hence lies in
`Agent007.ReLUn 3 (depthBound 3)`; but its kink at the origin keeps it out of
`Agent007.CPWL 3`.  So Agent007's statement of Theorem 2 is false, with no
appeal to the reference formalization. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent007.CPWL n = Agent007.ReLUn n (Agent007.depthBound n)) := by
  intro h
  have h3 := h 3 le_rfl
  have hmem : wit ∈ Agent007.ReLUn 3 (Agent007.depthBound 3) :=
    ⟨1, by unfold Agent007.depthBound; omega, wit_representable⟩
  exact wit_not_mem_agent (by rw [h3]; exact hmem)

end Star_007

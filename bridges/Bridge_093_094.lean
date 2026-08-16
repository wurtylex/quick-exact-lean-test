namespace Bridge_093_094

/-- Both agents define `depthBound n` by the *identical* term
`⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1` (`⌈·⌉₊` is notation for `Nat.ceil`), so the two
definitions are syntactically/definitionally equal and the bound `3 ≤ n` is not even
needed. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent093.depthBound n = Agent094.depthBound n := rfl

-- `relun`: Agent093 encodes "at most k hidden layers" via a dependent `Layers` GADT
-- indexed by an explicit list of widths, while Agent094 encodes it via a recursive
-- existential `ComputedWithHiddenLayers` on `k`. Both are genuinely "at most k"
-- families and should coincide, but bridging the two representations needs a
-- structural induction translating a `Layers` chain into a nested
-- `ComputedWithHiddenLayers` witness (and back), which is not attempted here.
theorem relun (n k : ℕ) : Agent093.ReLUn n k = Agent094.ReLUn n k := by
  sorry

/-- Refutation of `cpwl`. Agent094's `CPWL` uses *local agreement* (spec's case (b)):
a single, fixed, finite family of affine pieces such that every point has a *whole
neighbourhood* on which `f` agrees with one piece. Agent093 uses a genuine polyhedral
subdivision (case (a)). The one-dimensional ReLU `x ↦ max 0 (x 0)` lies in Agent093's
`CPWL 1` (two half-space pieces) but *not* in Agent094's: no single affine function can
agree with it on a whole neighbourhood of `0`, since arbitrarily close to `0` it is `x 0`
on one side and `0` on the other. -/
theorem cpwl_ne : ∃ n, Agent093.CPWL n ≠ Agent094.CPWL n := by
  refine ⟨1, fun hEq => ?_⟩
  have heval : ∀ (w b : ℝ) (x : Fin 1 → ℝ),
      (((fun _ _ => w), (fun _ => b)) : Agent093.AffFun 1).eval x = w * x 0 + b := by
    intro w b x
    simp [Agent093.AffFun.eval, Agent093.AffineMap'.apply, Fin.sum_univ_one]
  have hpoly0 : Agent093.IsPolyhedron 1 {x : Fin 1 → ℝ | 0 ≤ x 0} := by
    refine ⟨1, fun _ => (((fun _ _ => (-1 : ℝ)), (fun _ => (0 : ℝ))) : Agent093.AffFun 1), ?_⟩
    ext x
    simp only [Set.mem_setOf_eq, Fin.forall_fin_one, heval]
    constructor <;> intro h <;> linarith
  have hpoly1 : Agent093.IsPolyhedron 1 {x : Fin 1 → ℝ | x 0 ≤ 0} := by
    refine ⟨1, fun _ => (((fun _ _ => (1 : ℝ)), (fun _ => (0 : ℝ))) : Agent093.AffFun 1), ?_⟩
    ext x
    simp only [Set.mem_setOf_eq, Fin.forall_fin_one, heval]
    constructor <;> intro h <;> linarith
  have hmem093 : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent093.CPWL 1 := by
    refine ⟨continuous_const.max (continuous_apply 0), 2,
      ![{x : Fin 1 → ℝ | 0 ≤ x 0}, {x : Fin 1 → ℝ | x 0 ≤ 0}],
      ![(((fun _ _ => (1 : ℝ)), (fun _ => (0 : ℝ))) : Agent093.AffFun 1),
        (((fun _ _ => (0 : ℝ)), (fun _ => (0 : ℝ))) : Agent093.AffFun 1)], ?_, ?_, ?_⟩
    · ext x
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      rcases le_total (0 : ℝ) (x 0) with h0 | h0
      · exact ⟨0, by simp only [Matrix.cons_val_zero, Set.mem_setOf_eq]; exact h0⟩
      · exact ⟨1, by simp only [Matrix.cons_val_one, Matrix.head_cons, Set.mem_setOf_eq]; exact h0⟩
    · intro i
      fin_cases i
      · simpa using hpoly0
      · simpa using hpoly1
    · intro i x hx
      fin_cases i
      · simp only [Matrix.cons_val_zero, Set.mem_setOf_eq] at hx ⊢
        rw [heval, max_eq_right hx]; ring
      · simp only [Matrix.cons_val_one, Matrix.head_cons, Set.mem_setOf_eq] at hx ⊢
        rw [heval, max_eq_left hx]; ring
  have hnot094 : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∉ Agent094.CPWL 1 := by
    rintro ⟨-, m, g, hg, hloc⟩
    obtain ⟨i, U, hU, hEqOn⟩ := hloc (fun _ => 0)
    have h0U : (fun _ : Fin 1 => (0 : ℝ)) ∈ U := mem_of_mem_nhds hU
    have hc0 : g i (fun _ => (0 : ℝ)) = 0 := by simpa using (hEqOn h0U).symm
    obtain ⟨a, c, hgi⟩ := hg i
    have hceq : c = 0 := by
      rw [hgi] at hc0; simpa [Fin.sum_univ_one] using hc0
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
    have htpos : (0 : ℝ) < ε / 2 := by positivity
    have hp : (fun _ : Fin 1 => ε / 2) ∈ U := hball (by
      rw [Metric.mem_ball, dist_pi_lt_iff hε]
      intro b
      simp only [Real.dist_eq, sub_zero]
      rw [abs_of_pos htpos]; linarith)
    have hq : (fun _ : Fin 1 => -(ε / 2)) ∈ U := hball (by
      rw [Metric.mem_ball, dist_pi_lt_iff hε]
      intro b
      simp only [Real.dist_eq, sub_zero]
      rw [abs_of_neg (by linarith : (-(ε / 2) : ℝ) < 0)]; linarith)
    have heqp := hEqOn hp
    have heqq := hEqOn hq
    rw [hgi] at heqp heqq
    simp only [Fin.sum_univ_one] at heqp heqq
    rw [max_eq_right htpos.le] at heqp
    rw [max_eq_left (by linarith : (-(ε / 2) : ℝ) ≤ 0)] at heqq
    rw [hceq] at heqp heqq
    have hX : a 0 * (ε / 2) = ε / 2 := by linarith
    have hY : a 0 * -(ε / 2) = 0 := by linarith
    have hrel : a 0 * (ε / 2) = -(a 0 * -(ε / 2)) := by ring
    rw [hX, hY] at hrel
    linarith
  exact hnot094 (hEq ▸ hmem093)

-- `statement`: this global iff asks whether Agent093's own Theorem 2 and Agent094's own
-- Theorem 2 are simultaneously true or simultaneously false. Both source `theorem2`s are
-- `sorry` (and cannot be used per the rules), `cpwl_ne` above shows the two `CPWL`
-- predicates differ from *each other* but says nothing about either side's internal
-- theorem, and `relun` is unresolved; with no independent handle on either side, this is
-- left open rather than guessed at.
theorem statement :
    (∀ n, 3 ≤ n → Agent093.CPWL n = Agent093.ReLUn n (Agent093.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent094.CPWL n = Agent094.ReLUn n (Agent094.depthBound n)) := by
  sorry

end Bridge_093_094

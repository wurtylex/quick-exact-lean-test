namespace Bridge_080_081

/-- Both `depthBound`s unfold to the identical expression
`⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1`, so they agree for every `n`. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) :
    Agent080.depthBound n = Agent081.depthBound n := by
  unfold Agent080.depthBound Agent081.depthBound
  rfl

/-- `Agent080.CPWL` demands one affine function agree with `f` on a whole
neighbourhood of every point (even kink points); `Agent081.CPWL` only needs
a finite polyhedral cover. `x ↦ max 0 (x 0)` on `ℝ^1` lies in the latter
(affine on `x 0 ≤ 0` and on `x 0 ≥ 0`) but not the former: matching one
affine map on all small `t > 0`, `t < 0`, and `t = 0` near `0` forces
`c = 0`, `a = 1`, `a = 0` simultaneously. -/
theorem cpwl_ne : ∃ n, Agent080.CPWL n ≠ Agent081.CPWL n := by
  refine ⟨1, fun heq => ?_⟩
  have h81 : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent081.CPWL 1 := by
    refine ⟨continuous_const.max (continuous_apply 0), 2,
      ![{x : Fin 1 → ℝ | x 0 ≤ 0}, {x : Fin 1 → ℝ | 0 ≤ x 0}],
      ![(⟨fun _ _ => (0:ℝ), fun _ => (0:ℝ)⟩ : Agent081.Affine 1 1),
        (⟨fun _ _ => (1:ℝ), fun _ => (0:ℝ)⟩ : Agent081.Affine 1 1)],
      ?_, ?_, ?_⟩
    · rw [Set.eq_univ_iff_forall]
      intro x
      simp only [Set.mem_iUnion]
      rcases le_total (x 0) 0 with h | h
      · exact ⟨0, by simp only [Matrix.cons_val_zero, Set.mem_setOf_eq]; exact h⟩
      · exact ⟨1, by
          simp only [Matrix.cons_val_one, Matrix.head_cons, Set.mem_setOf_eq]; exact h⟩
    · intro i
      fin_cases i
      · refine ⟨1, fun _ _ => 1, fun _ => 0, ?_⟩
        ext x
        simp only [Matrix.cons_val_zero, Set.mem_setOf_eq]
        constructor
        · intro hx j; fin_cases j; simpa [Fin.sum_univ_one] using hx
        · intro hx; simpa [Fin.sum_univ_one] using hx 0
      · refine ⟨1, fun _ _ => -1, fun _ => 0, ?_⟩
        ext x
        simp only [Matrix.cons_val_one, Matrix.head_cons, Set.mem_setOf_eq]
        constructor
        · intro hx j; fin_cases j; simp only [Fin.sum_univ_one]; linarith
        · intro hx
          have h0 := hx 0
          simp only [Fin.sum_univ_one] at h0
          linarith
    · intro i
      fin_cases i
      · intro x hx
        simp only [Matrix.cons_val_zero, Set.mem_setOf_eq] at hx
        simp only [Matrix.cons_val_zero]
        simp [Agent081.Affine.eval, Matrix.mulVec, Matrix.dotProduct,
          Fin.sum_univ_one, max_eq_left hx]
      · intro x hx
        simp only [Matrix.cons_val_one, Matrix.head_cons, Set.mem_setOf_eq] at hx
        simp only [Matrix.cons_val_one, Matrix.head_cons]
        simp [Agent081.Affine.eval, Matrix.mulVec, Matrix.dotProduct,
          Fin.sum_univ_one, max_eq_right hx]
  have h80 : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∉ Agent080.CPWL 1 := by
    rintro ⟨-, ι, _, g, hg_aff, hg_cov⟩
    obtain ⟨i, hi⟩ := hg_cov (0 : Fin 1 → ℝ)
    obtain ⟨T, hT⟩ := hg_aff i
    set φ : ℝ → (Fin 1 → ℝ) := fun t _ => t with hφdef
    have hφ0 : φ 0 = (0 : Fin 1 → ℝ) := by ext j; simp [hφdef]
    have hφc : Continuous φ := by
      rw [hφdef]; exact continuous_pi fun _ => continuous_id
    have htend : Filter.Tendsto φ (nhds (0:ℝ)) (nhds (0 : Fin 1 → ℝ)) := by
      rw [← hφ0]; exact hφc.tendsto 0
    have hev := htend.eventually hi
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
    have key : ∀ t : ℝ, |t| < ε → max 0 t = T.A 0 0 * t + T.c 0 := by
      intro t ht
      have ht' : dist t (0:ℝ) < ε := by rw [Real.dist_eq, sub_zero]; exact ht
      have h1 := hball ht'
      simpa [hφdef, hT, Agent080.AffineMap.eval, Fin.sum_univ_one] using h1
    have e0 := key 0 (by simpa using hε)
    simp only [max_self, mul_zero, zero_add] at e0
    have e1 := key (ε/2) (by rw [abs_of_pos (by linarith)]; linarith)
    rw [max_eq_right (by linarith : (0:ℝ) ≤ ε/2), ← e0, add_zero] at e1
    have e2 := key (-(ε/2)) (by rw [abs_of_neg (by linarith)]; linarith)
    rw [max_eq_left (by linarith : -(ε/2) ≤ (0:ℝ)), ← e0, add_zero] at e2
    have hεpos : (0:ℝ) < ε/2 := by linarith
    have e1' : (1:ℝ) * (ε/2) = T.A 0 0 * (ε/2) := by rw [one_mul]; exact e1
    have hA1 : (1:ℝ) = T.A 0 0 := mul_right_cancel₀ (ne_of_gt hεpos) e1'
    have hA0 : T.A 0 0 = 0 :=
      (mul_eq_zero.mp e2.symm).resolve_right (by intro h; linarith)
    linarith [hA1, hA0]
  rw [heq] at h80
  exact h80 h81

/-- "Exactly `k` layers" (Agent080) vs. "at most `k` layers" (Agent081)
coincide only via an unproved padding lemma (`k'`-layer nets are
`k`-layer nets for `k' ≤ k`, via `x = relu x - relu (-x)` as an identity
layer); building that, or an impossibility argument for the converse
direction, is out of scope for this budget. -/
theorem relun (n k : ℕ) : Agent080.ReLUn n k = Agent081.ReLUn n k := by
  sorry

/-- Compares two restatements of Theorem 2 itself (each still `sorry` in
its source file); deciding this iff needs actually proving or refuting
Theorem 2 in both encodings, which is out of scope. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent080.CPWL n = Agent080.ReLUn n (Agent080.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent081.CPWL n = Agent081.ReLUn n (Agent081.depthBound n)) := by
  sorry

end Bridge_080_081

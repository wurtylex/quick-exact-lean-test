namespace Bridge_007_008

/-! ## depth

Both files define `depthBound` with the *syntactically identical* expression
`⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`, so the two functions are definitionally equal. -/

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent007.depthBound n = Agent008.depthBound n := rfl

/-! ## cpwl : refuted

Agent007's `CPWL` uses "local agreement": at every point `x` there must be an open
neighbourhood `U` of `x` on which `f` equals *one fixed affine function on all of `U`*.
Agent008's `CPWL` uses a genuine finite polyhedral subdivision. These differ: the
"local agreement" reading forces `f` to be affine on a two-sided neighbourhood of every
point, so it *excludes* functions with an honest kink, e.g. `x ↦ max 0 (x 0)`, which is
exactly the kind of function a polyhedral subdivision (and a ReLU network!) can capture.
We exhibit this witness at `n = 1`. -/

private lemma mulVecC (c : ℝ) (x : Fin 1 → ℝ) :
    (fun _ _ : Fin 1 => c).mulVec x 0 = c * x 0 := by
  simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_one]

private lemma mem_P0 (x : Fin 1 → ℝ) :
    ((fun _ _ : Fin 1 => (1 : ℝ)).mulVec x ≤ fun _ => (0 : ℝ)) ↔ x 0 ≤ 0 := by
  rw [Pi.le_def]
  constructor
  · intro h; have h0 := h 0; rw [mulVecC] at h0; linarith
  · intro h i; fin_cases i; rw [mulVecC]; linarith

private lemma mem_P1 (x : Fin 1 → ℝ) :
    ((fun _ _ : Fin 1 => (-1 : ℝ)).mulVec x ≤ fun _ => (0 : ℝ)) ↔ 0 ≤ x 0 := by
  rw [Pi.le_def]
  constructor
  · intro h; have h0 := h 0; rw [mulVecC] at h0; linarith
  · intro h i; fin_cases i; rw [mulVecC]; linarith

private def bridgeF : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

private lemma bridgeF_mem_008 : bridgeF ∈ Agent008.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2,
    ![{y : Fin 1 → ℝ | (fun _ _ : Fin 1 => (1 : ℝ)).mulVec y ≤ fun _ => (0 : ℝ)},
      {y : Fin 1 → ℝ | (fun _ _ : Fin 1 => (-1 : ℝ)).mulVec y ≤ fun _ => (0 : ℝ)}],
    ![(⟨fun _ _ => 0, fun _ => 0⟩ : Agent008.AffineMap' 1 1),
      (⟨fun _ _ => 1, fun _ => 0⟩ : Agent008.AffineMap' 1 1)], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact ⟨1, fun _ _ => 1, fun _ => 0, rfl⟩
    · exact ⟨1, fun _ _ => -1, fun _ => 0, rfl⟩
  · apply Set.eq_univ_iff_forall.mpr
    intro x
    simp only [Set.mem_iUnion]
    rcases le_total (x 0) 0 with h | h
    · exact ⟨0, by simp only [Matrix.cons_val_zero]; exact (mem_P0 x).mpr h⟩
    · exact ⟨1, by simp only [Matrix.cons_val_one, Matrix.head_cons]; exact (mem_P1 x).mpr h⟩
  · intro i
    fin_cases i
    · intro x hx
      simp only [Matrix.cons_val_zero] at hx
      have hx0 : x 0 ≤ 0 := (mem_P0 x).mp hx
      simp [bridgeF, Agent008.AffineMap'.apply, Pi.add_apply, mulVecC, max_eq_left hx0]
    · intro x hx
      simp only [Matrix.cons_val_one, Matrix.head_cons] at hx
      have hx0 : 0 ≤ x 0 := (mem_P1 x).mp hx
      simp [bridgeF, Agent008.AffineMap'.apply, Pi.add_apply, mulVecC, max_eq_right hx0]

private lemma bridgeF_not_mem_007 : bridgeF ∉ Agent007.CPWL 1 := by
  rintro ⟨-, S, hS⟩
  obtain ⟨a, -, U, hUopen, hU0, hUagree⟩ := hS (fun _ : Fin 1 => (0 : ℝ))
  have hcont : Continuous (fun t : ℝ => (fun _ : Fin 1 => t)) :=
    continuous_pi (fun _ => continuous_id)
  have hnhds : (fun t : ℝ => (fun _ : Fin 1 => t)) ⁻¹' U ∈ nhds (0 : ℝ) :=
    hcont.continuousAt.preimage_mem_nhds (hUopen.mem_nhds hU0)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  have key : ∀ t : ℝ, |t| < δ → bridgeF (fun _ : Fin 1 => t) = a.1 0 * t + a.2 := by
    intro t ht
    have hmem : (fun _ : Fin 1 => t) ∈ U :=
      hball (Metric.mem_ball.mpr (by rw [Real.dist_eq, sub_zero]; exact ht))
    have heq := hUagree _ hmem
    have heval : a.eval (fun _ : Fin 1 => t) = a.1 0 * t + a.2 := by
      simp [Agent007.AffineFun.eval, Fin.sum_univ_one]
    rw [heval] at heq
    exact heq
  have e1 := key (δ / 2) (by rw [abs_of_pos (by linarith : (0:ℝ) < δ / 2)]; linarith)
  have e2 := key (δ / 4) (by rw [abs_of_pos (by linarith : (0:ℝ) < δ / 4)]; linarith)
  have e3 := key (-(δ / 2)) (by rw [abs_of_neg (by linarith : -(δ / 2) < (0:ℝ))]; linarith)
  simp only [bridgeF, max_eq_right (by linarith : (0:ℝ) ≤ δ / 2)] at e1
  simp only [bridgeF, max_eq_right (by linarith : (0:ℝ) ≤ δ / 4)] at e2
  simp only [bridgeF, max_eq_left (by linarith : -(δ / 2) ≤ (0:ℝ))] at e3
  have step : δ / 4 * (1 - a.1 0) = 0 := by linear_combination e1 - e2
  have hδ4 : δ / 4 ≠ 0 := by positivity
  have ha1 : a.1 0 = 1 := by
    rcases mul_eq_zero.mp step with h | h
    · exact absurd h hδ4
    · linarith
  have ha2 : a.2 = 0 := by rw [ha1] at e2; linarith
  rw [ha1, ha2] at e3
  linarith

theorem cpwl_ne : ∃ n, Agent007.CPWL n ≠ Agent008.CPWL n := by
  refine ⟨1, fun h => bridgeF_not_mem_007 ?_⟩
  rw [h]
  exact bridgeF_mem_008

/-! ## relun : sorry

Both `ReLUn n k` are `{f | ∃ j ≤ k, <exactly-j-layer predicate> f}`, so they would coincide
once the underlying "exactly `j` hidden layers" predicates coincide. But Agent007's
`RepresentableVec` recurses by peeling off the *outermost* (output-side) affine layer at
each step, while Agent008's `NetworkComputes` recurses by peeling off the *innermost*
(input-side) affine layer. Both describe the same class of "chains of `j+1` alternating
affine/ReLU layers", but proving the two peeling orders agree needs an
associativity/regrouping induction that is not stated (or needed) in either source file,
and reconstructing it is beyond what is tractable here. -/

theorem relun (n k : ℕ) : Agent007.ReLUn n k = Agent008.ReLUn n k := by
  sorry

/-! ## statement : sorry

The left side is in fact false: `x ↦ max 0 (x 0)` (extended to `Fin 3 → ℝ` by ignoring the
extra coordinates) is representable with `1 ≤ Agent007.depthBound 3 = 2` hidden layers, so
it lies in `Agent007.ReLUn 3 (Agent007.depthBound 3)`, yet by the same kink argument as in
`cpwl_ne` it is not in `Agent007.CPWL 3`. So the left `∀ n, ...` statement fails already at
`n = 3`. The right side, however, is literally the paper's Theorem 2 stated for Agent008's
faithful (polyhedral) encoding, i.e. exactly the deep, unproved content of `theorem2` in
`Thm2_008.lean`. Without proving or refuting that theorem outright we cannot determine the
right side's truth value, hence cannot resolve this `Iff` in either direction. -/

theorem statement :
    (∀ n, 3 ≤ n → Agent007.CPWL n = Agent007.ReLUn n (Agent007.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent008.CPWL n = Agent008.ReLUn n (Agent008.depthBound n)) := by
  sorry

end Bridge_007_008

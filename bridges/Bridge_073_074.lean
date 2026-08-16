namespace Bridge_073_074

/-- The one-dimensional ReLU kink `x ↦ max 0 x₀`, embedded on `ℝ^1`. -/
noncomputable def kink : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

/-- `Agent073.CPWL` requires literal local agreement with *one* affine map on a whole
neighbourhood of each point; `Agent074.CPWL` uses a finite polyhedral subdivision, on
each piece of which `f` merely has to agree with *some* affine map on that piece.
`kink` has a genuine kink at `0`: no single affine map can equal it on a full
neighbourhood of `0`, so it fails Agent073's condition but obviously satisfies
Agent074's (two half-space pieces). Hence the two `CPWL`s differ. -/
theorem cpwl_ne : ∃ n, Agent073.CPWL n ≠ Agent074.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  have hcont : Continuous kink := continuous_const.max (continuous_apply 0)
  have hmem74 : kink ∈ Agent074.CPWL 1 := by
    refine ⟨hcont, Bool, inferInstance,
      (fun b => if b then {x : Fin 1 → ℝ | -x 0 ≤ 0} else {x : Fin 1 → ℝ | x 0 ≤ 0}),
      fun i => ?_, ?_, fun i => ?_⟩
    · cases i with
      | true =>
          exact ⟨Unit, inferInstance, fun _ _ => (-1 : ℝ), fun _ => 0, by
            ext x; constructor
            · exact fun hx _ => by simpa [Fin.sum_univ_one, neg_one_mul] using hx
            · exact fun hx => by simpa [Fin.sum_univ_one, neg_one_mul] using hx ()⟩
      | false =>
          exact ⟨Unit, inferInstance, fun _ _ => (1 : ℝ), fun _ => 0, by
            ext x; constructor
            · exact fun hx _ => by simpa [Fin.sum_univ_one] using hx
            · exact fun hx => by simpa [Fin.sum_univ_one] using hx ()⟩
    · ext x
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      rcases le_total 0 (x 0) with hx | hx
      · exact ⟨true, show -x 0 ≤ 0 by linarith⟩
      · exact ⟨false, hx⟩
    · cases i with
      | true =>
          refine ⟨fun x => x 0, ⟨fun _ => 1, 0, fun x => by simp [Fin.sum_univ_one]⟩,
            fun x hx => ?_⟩
          have hx' : -x 0 ≤ 0 := hx
          simp [kink, max_eq_right (show (0:ℝ) ≤ x 0 by linarith)]
      | false =>
          refine ⟨fun _ => 0, ⟨fun _ => 0, 0, fun x => by simp⟩, fun x hx => ?_⟩
          have hx' : x 0 ≤ 0 := hx
          simp [kink, max_eq_left hx']
  have hnot73 : kink ∉ Agent073.CPWL 1 := by
    rintro ⟨-, S, hS⟩
    obtain ⟨T, -, U, hU, hT⟩ := hS (fun _ => (0 : ℝ))
    have hcm : Continuous (fun t : ℝ => (fun _ : Fin 1 => t)) :=
      continuous_pi fun _ => continuous_id
    obtain ⟨ε, hε, hsub⟩ :=
      Metric.mem_nhds_iff.mp (hcm.continuousAt.preimage_mem_nhds hU)
    have hδ : (0 : ℝ) < ε / 2 := by linarith
    have h0 : (fun _ : Fin 1 => (0:ℝ)) ∈ U := hsub (by simp [Metric.mem_ball, hε])
    have h1 : (fun _ : Fin 1 => (ε/2:ℝ)) ∈ U :=
      hsub (by simp only [Metric.mem_ball, Real.dist_eq, abs_of_pos hδ]; linarith)
    have h2 : (fun _ : Fin 1 => (-(ε/2):ℝ)) ∈ U :=
      hsub (by
        simp only [Metric.mem_ball, Real.dist_eq, abs_of_neg (show -(ε/2) < (0:ℝ) by linarith)]
        linarith)
    have e0 := hT _ h0
    have e1 := hT _ h1
    have e2 := hT _ h2
    simp only [kink, AffineMap.eval, Matrix.mulVec, dotProduct, Fin.sum_univ_one,
      Pi.add_apply] at e0 e1 e2
    have m0 : max (0:ℝ) 0 = 0 := max_self 0
    have m1 : max (0:ℝ) (ε/2) = ε/2 := max_eq_right hδ.le
    have m2 : max (0:ℝ) (-(ε/2)) = 0 := max_eq_left (by linarith)
    rw [m0] at e0; rw [m1] at e1; rw [m2] at e2
    nlinarith [e0, e1, e2]
  exact hnot73 (h ▸ hmem74)

/-- Both files write the depth bound with the identical expression
`⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1` (`⌈·⌉₊` is notation for `Nat.ceil`), so the two
`depthBound`s are the same function on the nose, no `3 ≤ n` needed. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent073.depthBound n = Agent074.depthBound n := by
  simp only [Agent073.depthBound, Agent074.depthBound]

-- `relun`: Agent073's `ReLUn` uses *exactly* `k` hidden layers (`IsReLURep`'s recursion
-- bottoms out at exactly `k`), while Agent074's uses *at most* `k` (`∃ k' ≤ k, …`). The
-- inclusion "exactly k ⊆ at most k" is a routine relabelling induction, but the converse
-- needs the padding lemma `x = ReLU x - ReLU (-x)` applied layer-by-layer to promote a
-- `k'`-layer network (`k' < k`) to an exactly-`k`-layer one; neither source file proves
-- this and it is too large a lemma to redo safely here, so this is left as `sorry`.
theorem relun (n k : ℕ) : Agent073.ReLUn n k = Agent074.ReLUn n k := sorry

-- `statement`: this is equivalent to comparing the two (sorry'd) `theorem2`s, which we
-- are barred from using; proving it honestly would mean reformalizing Theorem 2's real
-- analytic content from scratch, well beyond this bridge's scope, so left as `sorry`.
theorem statement :
    (∀ n, 3 ≤ n → Agent073.CPWL n = Agent073.ReLUn n (Agent073.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent074.CPWL n = Agent074.ReLUn n (Agent074.depthBound n)) := sorry

end Bridge_073_074

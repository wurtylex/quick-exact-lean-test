namespace Bridge_046_047

/-- Agent046's `CPWL` uses a genuine polyhedral-subdivision reading (finitely many closed
polyhedra covering `ℝⁿ`, with `f` affine on each), while Agent047's `CPWL` instead requires
`f` to *locally* agree with a single affine function in a full neighbourhood of every point.
The function `x ↦ max 0 (x 0)` is piecewise-linear in the usual sense (two half-spaces) but
is not locally affine at `0`: points with `x 0 > 0` and `x 0 < 0` occur in every neighbourhood
of `0`, and no single affine function can equal `max 0 (x 0)` on both sides at once. Hence the
two `CPWL` predicates disagree already at `n = 1`. -/
theorem cpwl_ne : ∃ n, Agent046.CPWL n ≠ Agent047.CPWL n := by
  refine ⟨1, ?_⟩
  set f : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0) with hf
  intro hEq
  have hmem046 : f ∈ Agent046.CPWL 1 := by
    refine ⟨continuous_const.max (continuous_apply 0), 2,
      ![fun _ => (0:ℝ), fun x => x 0],
      ![{x : Fin 1 → ℝ | x 0 ≤ 0}, {x : Fin 1 → ℝ | 0 ≤ x 0}], ?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact ⟨fun _ => 0, 0, fun x => by simp⟩
      · exact ⟨fun _ => 1, 0, fun x => by simp [Fin.sum_univ_one]⟩
    · intro i
      fin_cases i
      · refine ⟨1, fun _ _ => 1, fun _ => 0, ?_⟩
        ext x; simp only [Set.mem_setOf_eq, Set.mem_iInter, Fin.sum_univ_one]
        constructor <;> intro h <;> linarith
      · refine ⟨1, fun _ _ => -1, fun _ => 0, ?_⟩
        ext x; simp only [Set.mem_setOf_eq, Set.mem_iInter, Fin.sum_univ_one]
        constructor <;> intro h <;> linarith
    · ext x
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      rcases le_total (x 0) 0 with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    · intro i
      fin_cases i
      · intro x hx
        simp only [Matrix.cons_val_zero, Set.mem_setOf_eq] at hx ⊢
        simp [hf, max_eq_left hx]
      · intro x hx
        simp only [Matrix.cons_val_one, Matrix.head_cons, Set.mem_setOf_eq] at hx ⊢
        simp [hf, max_eq_right hx]
  have hmem047 : f ∈ Agent047.CPWL 1 := by rw [← hEq]; exact hmem046
  obtain ⟨-, m, g, haff, hloc⟩ := hmem047
  obtain ⟨i, h⟩ := hloc (fun _ => 0)
  obtain ⟨c, d, hcd⟩ := haff i
  have hcont0 : Filter.Tendsto (fun t : ℝ => (fun _ : Fin 1 => t)) (nhds 0)
      (nhds (fun _ : Fin 1 => (0:ℝ))) := (continuous_pi fun _ => continuous_id).tendsto 0
  have key : ∀ᶠ t in nhds (0:ℝ), max 0 t = c 0 * t + d := by
    filter_upwards [hcont0.eventually h] with t ht
    simp only [hf, hcd, Fin.sum_univ_one] at ht
    linarith [ht]
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp key
  have hball' : ∀ t : ℝ, |t| < ε → max 0 t = c 0 * t + d := fun t ht =>
    hball (by simpa [Metric.mem_ball, Real.dist_eq] using ht)
  set s : ℝ := ε / 4 with hs_def
  have hs : 0 < s := by rw [hs_def]; linarith
  have h1 : s = c 0 * s + d := by
    have := hball' s (by rw [abs_of_pos hs]; linarith)
    rwa [max_eq_right hs.le] at this
  have h2 : 2 * s = c 0 * (2 * s) + d := by
    have := hball' (2 * s) (by rw [abs_of_pos (by linarith : (0:ℝ) < 2 * s)]; linarith)
    rwa [max_eq_right (by linarith : (0:ℝ) ≤ 2 * s)] at this
  have h3 : 0 = c 0 * (-s) + d := by
    have := hball' (-s) (by rw [abs_of_neg (by linarith : -s < (0:ℝ))]; linarith)
    rwa [max_eq_left (by linarith : (-s:ℝ) ≤ 0)] at this
  have e2 : c 0 * (2 * s) = 2 * (c 0 * s) := by ring
  have e3 : c 0 * (-s) = -(c 0 * s) := by ring
  rw [e2] at h2
  rw [e3] at h3
  linarith [h1, h2, h3, hs]

/-- Not attempted: Agent046's `NetComputes` recurses by peeling the *first* affine-ReLU
layer off the input side (`f = g ∘ ReLU ∘ T`, `T` first), while Agent047's peels the *last*
layer off the output side (`f = affine ∘ ReLU ∘ g`, `g` first). Proving the two "at most `k`
hidden layers" classes coincide needs a network-composition lemma (extending a network by one
more layer at the *opposite* end from its own recursion) that neither source file supplies and
that is a genuine, nontrivial piece of formalization, not a quick derivation. -/
theorem relun (n k : ℕ) : Agent046.ReLUn n k = Agent047.ReLUn n k := sorry

/-- Both files use the literal formula `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`, so the two
`depthBound`s are syntactically identical definitions. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent046.depthBound n = Agent047.depthBound n := rfl

/-- Not attempted: `statement` compares each agent's own rendering of Theorem 2 against
*itself* (`CPWLᵢ = ReLUnᵢ (depthBoundᵢ)`), not `CPWL046` against `CPWL047` directly, so
`cpwl_ne` above does not settle it either way. Both underlying `theorem2` proofs are `sorry`
in the source files, so deciding this iff would require actually proving or refuting the real
Theorem 2 for at least one encoding, which is out of scope for a bridge. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent046.CPWL n = Agent046.ReLUn n (Agent046.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent047.CPWL n = Agent047.ReLUn n (Agent047.depthBound n)) := sorry

end Bridge_046_047

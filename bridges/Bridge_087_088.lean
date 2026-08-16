namespace Bridge_087_088

/-- Both agents write `depthBound n = ⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1`
(the `⌈·⌉₊` notation for Agent087 is definitionally `Nat.ceil` for Agent088),
so the two definitions are literally the same term. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) :
    Agent087.depthBound n = Agent088.depthBound n := by
  simp only [Agent087.depthBound, Agent088.depthBound]

/-!
`cpwl` is **refuted**. Agent087's `CPWL` requires `f` to agree with one of a
*finite family of globally affine functionals* on a neighbourhood of every
point; Agent088's `CPWL` requires a finite cover by closed polyhedra on each
of which `f` agrees with an affine function. Witness: `n = 1`,
`f x = max 0 (x 0)` (the 1-D ReLU) lies in Agent088's `CPWL 1` (cover by the
two half-lines `x 0 ≤ 0` and `0 ≤ x 0`) but not in Agent087's `CPWL 1`,
since near `0` no single global affine functional can agree with `f` on a
whole neighbourhood (it agrees with the zero map on one side and the
identity on the other).
-/
theorem cpwl_ne : ∃ n, Agent087.CPWL n ≠ Agent088.CPWL n := by
  have hP0 : Agent088.IsPolyhedron 1 {x : Fin 1 → ℝ | x 0 ≤ 0} := by
    refine ⟨1, fun _ _ => 1, fun _ => 0, ?_⟩
    ext x
    simp only [Set.mem_setOf_eq, Fin.sum_univ_one, Fin.forall_fin_one]
    constructor <;> intro h <;> linarith
  have hP1 : Agent088.IsPolyhedron 1 {x : Fin 1 → ℝ | 0 ≤ x 0} := by
    refine ⟨1, fun _ _ => -1, fun _ => 0, ?_⟩
    ext x
    simp only [Set.mem_setOf_eq, Fin.sum_univ_one, Fin.forall_fin_one]
    constructor <;> intro h <;> linarith
  have hunion :
      (⋃ j, ![{x : Fin 1 → ℝ | x 0 ≤ 0}, {x : Fin 1 → ℝ | 0 ≤ x 0}] j) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    rcases le_total (x 0) 0 with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  have hAff0 : Agent088.IsAffineOn 1 (fun x : Fin 1 → ℝ => max 0 (x 0))
      {x : Fin 1 → ℝ | x 0 ≤ 0} := by
    refine ⟨fun _ => 0, 0, fun x hx => ?_⟩
    simp only [Set.mem_setOf_eq] at hx
    rw [max_eq_left hx]
    simp [Fin.sum_univ_one]
  have hAff1 : Agent088.IsAffineOn 1 (fun x : Fin 1 → ℝ => max 0 (x 0))
      {x : Fin 1 → ℝ | 0 ≤ x 0} := by
    refine ⟨fun _ => 1, 0, fun x hx => ?_⟩
    simp only [Set.mem_setOf_eq] at hx
    rw [max_eq_right hx]
    simp [Fin.sum_univ_one]
  have hPall : ∀ j : Fin 2, Agent088.IsPolyhedron 1
      (![{x : Fin 1 → ℝ | x 0 ≤ 0}, {x : Fin 1 → ℝ | 0 ≤ x 0}] j) := by
    intro j; fin_cases j
    · simpa using hP0
    · simpa using hP1
  have hAffall : ∀ j : Fin 2, Agent088.IsAffineOn 1 (fun x : Fin 1 → ℝ => max 0 (x 0))
      (![{x : Fin 1 → ℝ | x 0 ≤ 0}, {x : Fin 1 → ℝ | 0 ≤ x 0}] j) := by
    intro j; fin_cases j
    · simpa using hAff0
    · simpa using hAff1
  have hmem88 : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent088.CPWL 1 :=
    ⟨continuous_const.max (continuous_apply 0), 2,
      ![{x : Fin 1 → ℝ | x 0 ≤ 0}, {x : Fin 1 → ℝ | 0 ≤ x 0}], hPall, hunion, hAffall⟩
  have hnot87 : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∉ Agent087.CPWL 1 := by
    rintro ⟨-, r, a, ha, hloc⟩
    obtain ⟨i, hi⟩ := hloc (0 : Fin 1 → ℝ)
    obtain ⟨c, b, hab⟩ := ha i
    set g : ℝ → (Fin 1 → ℝ) := fun t _ => t with hg_def
    have hgc : Continuous g := continuous_pi (fun _ => continuous_id)
    have hg0 : g 0 = (0 : Fin 1 → ℝ) := by funext j; simp [hg_def]
    have htend : Filter.Tendsto g (nhds (0 : ℝ)) (nhds (0 : Fin 1 → ℝ)) := by
      have h := hgc.tendsto (0 : ℝ)
      rwa [hg0] at h
    have h2 : ∀ᶠ t in nhds (0 : ℝ),
        (fun x : Fin 1 → ℝ => max 0 (x 0)) (g t) = a i (g t) := htend.eventually hi
    rw [Metric.eventually_nhds_iff] at h2
    obtain ⟨ε, hε, hball⟩ := h2
    have e0 : max 0 (0 : ℝ) = a i (g 0) := hball (by simpa using hε)
    have e1 : max 0 (ε / 2) = a i (g (ε / 2)) :=
      hball (by rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]; linarith)
    have e2 : max 0 (-(ε / 2)) = a i (g (-(ε / 2))) :=
      hball (by
        rw [Real.dist_eq, sub_zero, abs_of_neg (by linarith : -(ε / 2) < (0 : ℝ))]
        linarith)
    simp only [hg_def, hab, Fin.sum_univ_one] at e0 e1 e2
    rw [max_self] at e0
    rw [max_eq_right (le_of_lt (half_pos hε))] at e1
    rw [max_eq_left (by linarith : -(ε / 2) ≤ (0 : ℝ))] at e2
    simp only [mul_zero, zero_add, mul_neg] at e0 e2
    linarith [e0, e1, e2, hε]
  exact ⟨1, fun heq => hnot87 (heq ▸ hmem88)⟩

-- `relun` (exact-k vs at-most-k hidden layers) coincides only via a padding
-- argument (turning an identity map into an extra ReLU layer via
-- `x = ReLU x - ReLU (-x)`), which neither agent's file proves; left open.
theorem relun (n k : ℕ) : Agent087.ReLUn n k = Agent088.ReLUn n k := by
  sorry

-- `statement` builds on `cpwl` (refuted above) and `relun` (open above), so
-- it cannot be settled independently of those.
theorem statement :
    (∀ n, 3 ≤ n → Agent087.CPWL n = Agent087.ReLUn n (Agent087.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent088.CPWL n = Agent088.ReLUn n (Agent088.depthBound n)) := by
  sorry

end Bridge_087_088

namespace Bridge_025_026

/-!
`depthBound` is defined by literally the same formula in both files
(`⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`), so `depth` is `rfl`.

`cpwl` is **false**: Agent025's `CPWL` requires `f` to agree with one affine
function on a *full neighbourhood* of every point, which (via the standard
"punch a hole" trick along a single coordinate) forces every member of
`Agent025.CPWL n` to be genuinely affine everywhere. Agent026's `CPWL` is the
honest polyhedral-subdivision notion and contains truly kinked functions such
as `x ↦ max 0 (x 0)`. We refute `cpwl` using exactly this witness at `n = 1`.

`relun` and `statement` are left `sorry`; see the comments above each.
-/

theorem cpwl_ne : ∃ n, Agent025.CPWL n ≠ Agent026.CPWL n := by
  refine ⟨1, fun hEq => ?_⟩
  have hCont : Continuous (fun x : Fin 1 → ℝ => max 0 (x 0)) :=
    continuous_const.max (continuous_apply 0)
  have hPoly0 : Agent026.IsPolyhedron {x : Fin 1 → ℝ | 0 ≤ x 0} :=
    ⟨1, fun _ _ => -1, fun _ => 0, by
      ext x
      constructor
      · intro hx
        simp only [Set.mem_iInter, Set.mem_setOf_eq, Fin.sum_univ_one]
        intro i; linarith
      · intro hx
        simp only [Set.mem_iInter, Set.mem_setOf_eq, Fin.sum_univ_one] at hx
        have := hx 0
        simp only [Set.mem_setOf_eq]; linarith⟩
  have hPoly1 : Agent026.IsPolyhedron {x : Fin 1 → ℝ | x 0 ≤ 0} :=
    ⟨1, fun _ _ => 1, fun _ => 0, by
      ext x
      constructor
      · intro hx
        simp only [Set.mem_iInter, Set.mem_setOf_eq, Fin.sum_univ_one]
        intro i; linarith
      · intro hx
        simp only [Set.mem_iInter, Set.mem_setOf_eq, Fin.sum_univ_one] at hx
        have := hx 0
        simp only [Set.mem_setOf_eq]; linarith⟩
  have h26 : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent026.CPWL 1 := by
    refine ⟨hCont, 2, ![{x : Fin 1 → ℝ | 0 ≤ x 0}, {x : Fin 1 → ℝ | x 0 ≤ 0}],
      ![fun _ : Fin 1 => (1 : ℝ), fun _ : Fin 1 => (0 : ℝ)], ![(0 : ℝ), 0], ?_, ?_, ?_⟩
    · intro i; fin_cases i
      · simpa using hPoly0
      · simpa using hPoly1
    · ext x
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      rcases le_total 0 (x 0) with h | h
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩
    · intro i x hx
      fin_cases i
      · simp only [Matrix.cons_val_zero] at hx ⊢
        simp [Fin.sum_univ_one, max_eq_left hx]
      · simp only [Matrix.cons_val_one, Matrix.head_cons] at hx ⊢
        simp [Fin.sum_univ_one, max_eq_right hx]
  rw [← hEq] at h26
  obtain ⟨-, m, g, hAff, hcov⟩ := h26
  obtain ⟨i, hi⟩ := hcov (fun _ : Fin 1 => (0 : ℝ))
  obtain ⟨a, c, hga⟩ := hAff i
  have hmap : Continuous (fun t : ℝ => (fun _ : Fin 1 => t)) := continuous_pi fun _ => continuous_id
  have key : ∀ᶠ t in nhds (0 : ℝ), max 0 t = a 0 * t + c := by
    have hev := (hmap.tendsto 0).eventually hi
    simpa [hga, Fin.sum_univ_one] using hev
  rw [(Metric.nhds_basis_ball).eventually_iff] at key
  obtain ⟨ε, hε, hkey⟩ := key
  have h1 := hkey (x := ε / 2) (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
  have h2 := hkey (x := -(ε / 2)) (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_neg (by linarith)]; linarith)
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ ε / 2)] at h1
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0 : ℝ))] at h2
  linarith

/- `Agent025.ReLUn` requires *exactly* `k` hidden layers, while `Agent026.ReLUn`
allows *at most* `k`. These agree only via a padding lemma (using
`relu t - relu (-t) = t` to simulate an identity layer and bump the exact depth
up by one), which neither source file proves and which is too long to build
here from scratch. -/
theorem relun (n k : ℕ) : Agent025.ReLUn n k = Agent026.ReLUn n k := by
  sorry

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent025.depthBound n = Agent026.depthBound n := rfl

/- Both agents leave `theorem2` as `sorry` in the source files, so resolving this
iff outright would require independently settling the truth value of each
formalization's version of Theorem 2 (which in turn depends on the unresolved
`relun` padding lemma above and, on the `cpwl` side, on the fact established
above that `Agent025.CPWL` collapses to genuinely affine functions) — well
beyond what a definitional bridge can establish. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent025.CPWL n = Agent025.ReLUn n (Agent025.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent026.CPWL n = Agent026.ReLUn n (Agent026.depthBound n)) := by
  sorry

end Bridge_025_026

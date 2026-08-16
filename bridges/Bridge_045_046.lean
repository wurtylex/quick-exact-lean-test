namespace Bridge_045_046

/-!
`ReLUn`/`ComputesWithHidden`/`NetComputes`/`depthBound` match closely: both use the
"at most `k` hidden layers" reading and the literal `⌈Real.logb 3 ((n:ℝ)-1)⌉₊ + 1` depth
bound, and the affine-layer structures (`AffineTransform` vs `AffineMap`) have identical
`A`/bias fields and identical `eval`/`apply` formulas, just spelled with a pointwise
equation (045) vs a function equation (046). Where they genuinely differ is `CPWL`:
`Agent045.CPWL` is a "local agreement with a single *global* affine function on a whole
neighbourhood of every point" definition, while `Agent046.CPWL` is a genuine polyhedral
subdivision. The former is strictly stronger: it fails for `relu (x 0)` at `x = 0`, even
though `relu (x 0)` is the textbook CPWL function. We use this to refute `cpwl`.
-/

/-- Convert between the two (field-for-field identical) affine-map structures. -/
private def toAM {a b : ℕ} (T : Agent045.AffineTransform a b) : Agent046.AffineMap a b :=
  ⟨T.A, T.c⟩

private def toAT {a b : ℕ} (T : Agent046.AffineMap a b) : Agent045.AffineTransform a b :=
  ⟨T.A, T.bias⟩

private theorem computes_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent045.ComputesWithHidden k n f ↔ Agent046.NetComputes n k f
  | 0, n, f => by
      constructor
      · rintro ⟨T, hT⟩; exact ⟨toAM T, funext fun x => hT x⟩
      · rintro ⟨T, hT⟩; exact ⟨toAT T, fun x => by rw [hT]⟩
  | (k+1), n, f => by
      constructor
      · rintro ⟨m, T, g, hg, hf⟩
        exact ⟨m, toAM T, g, (computes_iff k m g).mp hg, funext fun x => hf x⟩
      · rintro ⟨m, T, g, hg, hf⟩
        exact ⟨m, toAT T, g, (computes_iff k m g).mpr hg, fun x => by rw [hf]⟩

theorem relun (n k : ℕ) : Agent045.ReLUn n k = Agent046.ReLUn n k := by
  ext f
  simp only [Agent045.ReLUn, Agent046.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k', hk', h⟩; exact ⟨k', hk', (computes_iff k' n f).mp h⟩
  · rintro ⟨k', hk', h⟩; exact ⟨k', hk', (computes_iff k' n f).mpr h⟩

theorem depth (n : ℕ) (_hn : 3 ≤ n) : Agent045.depthBound n = Agent046.depthBound n := by
  unfold Agent045.depthBound Agent046.depthBound
  rfl

/-- The counterexample distinguishing the two `CPWL` definitions: `relu` of the single
coordinate on `ℝ^1`. It is genuinely piecewise-affine (046's polyhedral sense) but not
locally equal to a single fixed affine function near `0` (045's sense). -/
private def kink (x : Fin 1 → ℝ) : ℝ := max 0 (x 0)

private theorem kink_mem_046 : kink ∈ Agent046.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2,
    ![fun _ : Fin 1 → ℝ => (0 : ℝ), fun x : Fin 1 → ℝ => x 0],
    ![{x : Fin 1 → ℝ | x 0 ≤ 0}, {x : Fin 1 → ℝ | 0 ≤ x 0}], ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact ⟨0, 0, by simp⟩
    · exact ⟨fun _ => 1, 0, by simp [Fin.sum_univ_one]⟩
  · intro i; fin_cases i
    · refine ⟨1, fun _ _ => 1, fun _ => 0, ?_⟩
      ext x
      simp only [Set.mem_iInter, Fin.forall_fin_one, Set.mem_setOf_eq, Fin.sum_univ_one,
        one_mul]
    · refine ⟨1, fun _ _ => -1, fun _ => 0, ?_⟩
      ext x
      simp only [Set.mem_iInter, Fin.forall_fin_one, Set.mem_setOf_eq, Fin.sum_univ_one]
      constructor <;> intro h <;> linarith
  · apply Set.eq_univ_iff_forall.mpr
    intro x
    rcases le_total (x 0) 0 with h | h
    · exact Set.mem_iUnion.mpr ⟨0, h⟩
    · exact Set.mem_iUnion.mpr ⟨1, h⟩
  · intro i; fin_cases i
    · intro x hx
      simp only [kink, Matrix.cons_val_zero, Set.mem_setOf_eq] at hx ⊢
      exact max_eq_left hx
    · intro x hx
      simp only [kink, Matrix.cons_val_one, Matrix.head_cons, Set.mem_setOf_eq] at hx ⊢
      exact max_eq_right hx

private theorem kink_not_mem_045 : kink ∉ Agent045.CPWL 1 := by
  rintro ⟨-, m, g, hgaff, hloc⟩
  obtain ⟨i, hev⟩ := hloc (0 : Fin 1 → ℝ)
  obtain ⟨a, b, hgi⟩ := hgaff i
  have hιcont : Continuous (fun t : ℝ => (fun _ : Fin 1 => t)) :=
    continuous_pi (fun _ => continuous_id)
  have htendsto :
      Filter.Tendsto (fun t : ℝ => (fun _ : Fin 1 => t)) (nhds 0) (nhds (0 : Fin 1 → ℝ)) :=
    hιcont.tendsto 0
  have hev' : ∀ᶠ t in nhds (0 : ℝ),
      kink (fun _ : Fin 1 => t) = g i (fun _ : Fin 1 => t) := htendsto.eventually hev
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hev'
  have hd0 : dist (0 : ℝ) 0 < ε := by simpa using hε
  have hd1 : dist (ε / 2) (0 : ℝ) < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith : (0:ℝ) < ε / 2)]; linarith
  have hd2 : dist (-(ε / 2)) (0 : ℝ) < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_neg (by linarith : -(ε / 2) < (0:ℝ))]; linarith
  have e0 := hsub hd0
  have e1 := hsub hd1
  have e2 := hsub hd2
  simp only [kink, hgi, Fin.sum_univ_one] at e0 e1 e2
  rw [max_self] at e0
  simp only [mul_zero, zero_add] at e0
  rw [max_eq_right (by linarith : (0:ℝ) ≤ ε / 2)] at e1
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0:ℝ))] at e2
  have hb : b = 0 := e0.symm
  rw [hb, add_zero] at e1 e2
  have hring : a 0 * -(ε / 2) = -(a 0 * (ε / 2)) := by ring
  rw [hring] at e2
  linarith [e1, e2, hε]

/-- **Refuted.** `Agent045.CPWL` (local agreement with a single global affine piece near
every point) and `Agent046.CPWL` (polyhedral subdivision) disagree already at `n = 1`. -/
theorem cpwl_ne : ∃ n, Agent045.CPWL n ≠ Agent046.CPWL n :=
  ⟨1, fun h => kink_not_mem_045 (by rw [h]; exact kink_mem_046)⟩

/-- `statement`: by the same `kink`-style counterexample, `relu (x 0)` (padded with unused
coordinates) is a one-hidden-layer ReLU network for any `n ≥ 3`, hence lies in
`Agent045.ReLUn n (depthBound n)` (depth bound is always `≥ 1`), yet is not in
`Agent045.CPWL n` by the local-affine-at-`0` argument above. So the LHS `∀ n, ...`
statement (Agent045's reading of Theorem 2) is false. Whether the RHS (Agent046's reading,
the paper's actual depth-separation theorem) is true is the hard mathematical content of
arXiv:2505.14338 and is out of scope here, so the `↔` itself is open; we leave it `sorry`
rather than fake either direction. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent045.CPWL n = Agent045.ReLUn n (Agent045.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent046.CPWL n = Agent046.ReLUn n (Agent046.depthBound n)) := sorry

end Bridge_045_046

namespace Bridge_068_069

/-!
Both files define `ReLUn` with the "at most k hidden layers" reading, and `depthBound` with
the literal expression `⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1` (no ℕ-truncated subtraction). Where
they genuinely differ is `CPWL`: `Agent068.CPWL` is a polyhedral-subdivision definition
(finite family of convex regions covering `ℝⁿ`, `f` affine on each), while `Agent069.CPWL`
is a "local agreement with one of finitely many *global* affine functions" definition. The
latter is strictly stronger than genuine piecewise-linearity: it forces `f` to coincide with
a single fixed affine function on a whole neighbourhood of every point, which fails for
`relu(x 0)` at `x = 0` even though `relu(x 0)` is the textbook example of a CPWL function.
We use this to refute `cpwl`.
-/

/-- The counterexample distinguishing the two `CPWL` definitions: `relu` of the single
coordinate, on `ℝ^1`. It is genuinely piecewise-affine (068's sense) but not locally equal
to a single fixed affine function near `0` (069's sense). -/
private def f068069 (x : Fin 1 → ℝ) : ℝ := max 0 (x 0)

private theorem f_mem_068 : f068069 ∈ Agent068.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2,
    ![(fun x : Fin 1 → ℝ => x 0), (fun _ : Fin 1 → ℝ => (0 : ℝ))],
    ![{x : Fin 1 → ℝ | 0 ≤ x 0}, {x : Fin 1 → ℝ | x 0 ≤ 0}], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact ⟨fun _ => 1, 0, by intro x; simp [Fin.sum_univ_one]⟩
    · exact ⟨fun _ => 0, 0, by intro x; simp [Fin.sum_univ_one]⟩
  · intro i
    fin_cases i
    · intro x hx y hy a b ha hb hab
      simp only [Set.mem_setOf_eq] at hx hy ⊢
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith
    · intro x hx y hy a b ha hb hab
      simp only [Set.mem_setOf_eq] at hx hy ⊢
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith
  · apply Set.eq_univ_iff_forall.mpr
    intro x
    rcases le_total 0 (x 0) with h | h
    · exact Set.mem_iUnion.mpr ⟨0, h⟩
    · exact Set.mem_iUnion.mpr ⟨1, h⟩
  · intro i
    fin_cases i
    · intro x hx
      exact max_eq_right hx
    · intro x hx
      exact max_eq_left hx

private theorem f_not_mem_069 : f068069 ∉ Agent069.CPWL 1 := by
  rintro ⟨-, m, g, hgaff, hloc⟩
  obtain ⟨i, hev⟩ := hloc (0 : Fin 1 → ℝ)
  obtain ⟨a, b, hgi⟩ := hgaff i
  have hιcont : Continuous (fun t : ℝ => (fun _ : Fin 1 => t)) :=
    continuous_pi (fun _ => continuous_id)
  have htendsto :
      Filter.Tendsto (fun t : ℝ => (fun _ : Fin 1 => t)) (nhds 0) (nhds (0 : Fin 1 → ℝ)) :=
    hιcont.tendsto 0
  have hev' : ∀ᶠ t in nhds (0 : ℝ),
      f068069 (fun _ : Fin 1 => t) = g i (fun _ : Fin 1 => t) := htendsto.eventually hev
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hev'
  have hd0 : dist (0 : ℝ) 0 < ε := by simpa using hε
  have hd1 : dist (ε / 2) (0 : ℝ) < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith : (0:ℝ) < ε / 2)]; linarith
  have hd2 : dist (-(ε / 2)) (0 : ℝ) < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_neg (by linarith : -(ε / 2) < (0:ℝ))]; linarith
  have e0 := hsub hd0
  have e1 := hsub hd1
  have e2 := hsub hd2
  simp only [f068069, hgi, Fin.sum_univ_one] at e0 e1 e2
  rw [max_self] at e0
  simp only [mul_zero, zero_add] at e0
  rw [max_eq_right (by linarith : (0:ℝ) ≤ ε / 2)] at e1
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0:ℝ))] at e2
  have hb : b = 0 := e0.symm
  rw [hb, add_zero] at e1 e2
  have hring : a 0 * -(ε / 2) = -(a 0 * (ε / 2)) := by ring
  rw [hring] at e2
  linarith [e1, e2, hε]

/-- **Refuted.** `Agent068.CPWL` (polyhedral subdivision) and `Agent069.CPWL` (local
agreement with a single global affine piece near every point) disagree already at `n = 1`:
`relu` of the coordinate is genuinely piecewise-affine but is not locally equal to one fixed
affine function near `0`. -/
theorem cpwl_ne : ∃ n, Agent068.CPWL n ≠ Agent069.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  apply f_not_mem_069
  rw [← h]
  exact f_mem_068

/-- `relun`: both sides use the "at most `k` hidden layers" reading over real-weighted
affine maps, so the represented function classes are almost certainly equal, but the two
network encodings are structurally very different (068: arbitrary width-indexed layers into
an infinite ambient "vector" `ℕ → ℝ`, evaluated by truncating matrix sums to `inDim`; 069: a
`Fin`-indexed inductive `ReLUNet` with genuine `Matrix (Fin b) (Fin a) ℝ` layers). Proving
equality needs an explicit depth-induction translating networks (and their evaluation) back
and forth between these encodings, which is substantially more than a short bridge file can
responsibly discharge, so we leave it open rather than fake it. -/
theorem relun (n k : ℕ) : Agent068.ReLUn n k = Agent069.ReLUn n k := sorry

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent068.depthBound n = Agent069.depthBound n := by
  unfold Agent068.depthBound Agent069.depthBound
  rfl

/-- `statement`: the RHS (Agent069's Theorem-2 claim) is in fact false, by the very same
`f068069`-style counterexample used for `cpwl_ne`: for any `n ≥ 3`, `relu (x 0)` (padded by
zero on the remaining coordinates) is a genuine one-hidden-layer ReLU network, hence lies in
`Agent069.ReLUn n (depthBound n)`, yet by the local-affine-at-`0` argument above it is not in
`Agent069.CPWL n`. So `Agent069.CPWL n ≠ Agent069.ReLUn n (depthBound n)` for every `n ≥ 3`,
making the RHS `∀ n, ...` statement false. But the LHS is exactly the paper's Theorem 2 for
Agent068's (faithful-looking) encoding, whose actual proof is far beyond the scope of a
single bridge file, so we cannot determine whether LHS is also false (in which case the iff
holds) or true (in which case it fails) without redoing the paper's argument. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent068.CPWL n = Agent068.ReLUn n (Agent068.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent069.CPWL n = Agent069.ReLUn n (Agent069.depthBound n)) := sorry

end Bridge_068_069

namespace Bridge_032_033

/-!
## Summary

* `depthBound`: both agents write the *identical* formula
  `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`. **PROVED** by `rfl`.
* `ReLUn`: both agents use the same "exactly `k` hidden layers" recursion built from
  a field-for-field identical `A : Matrix (Fin b) (Fin a) ℝ`, `c : Fin b → ℝ` structure
  (`AffineMap'` vs `AffineMapRn`), evaluated by the same formula (`Agent033` merely
  spells it via `Matrix.mulVec` where `Agent032` spells it via an explicit sum, but these
  reduce to the same value), and the same `relu = max 0 ·`, `reluVec`. So the two notions
  of "computable with exactly/at most `k` hidden layers" coincide for every `n k`.
  **PROVED**.
* `CPWL`: `Agent032` uses a genuine polyhedral-subdivision definition (family (a) in the
  spec); `Agent033` uses "for every point `x` there is an open neighbourhood `U` of `x`
  on which `f` agrees with *one* of finitely many fixed affine functions" (family (b)).
  These differ: `f = fun x => max 0 (x 0)` is CPWL under `Agent032`'s definition (two
  half-spaces `x 0 ≤ 0` / `x 0 ≥ 0`) but fails `Agent033`'s definition at `x = 0`, since
  no single affine function can agree with `f` on an entire neighbourhood of `0` (it would
  have to equal `t` for small `t > 0` and `0` for small `t < 0` simultaneously).
  **REFUTED** (`cpwl_ne`).
* `statement`: the right-hand side (Agent033's Theorem 2 statement) is false for the same
  reason as `cpwl_ne` (e.g. at `n = 3`, `Agent033.ReLUn 3 (depthBound 3)` contains
  `max 0 (x 0)` — a 1-hidden-layer network — which is not `Agent033.CPWL`). The
  left-hand side is exactly a restatement of the paper's actual Theorem 2 for `Agent032`'s
  (faithful) encoding, which neither `Agent032` nor this bridge proves (it is `sorry`ed in
  the source file). Resolving `statement` therefore requires resolving that open
  mathematical question, not just relating the two encodings. **SORRY**.
-/

/-! ### `depthBound` -/

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent032.depthBound n = Agent033.depthBound n := rfl

/-! ### `ReLUn` -/

private def toB {a b : ℕ} (T : Agent032.AffineMap' a b) : Agent033.AffineMapRn a b :=
  ⟨T.A, T.c⟩

private def toA {a b : ℕ} (T : Agent033.AffineMapRn a b) : Agent032.AffineMap' a b :=
  ⟨T.A, T.c⟩

/-- Same recursive shape on both sides; the only work is repackaging the (field-for-field
identical) affine-map structures, and `eval`/`reluVec`/`relu` all reduce to the same
values on both sides, so each step closes by `rfl` (with a `simp` fallback that unfolds
`Matrix.mulVec`/`dotProduct` explicitly in case the reduction is not immediate). -/
private lemma computes_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent032.ReLUComputable n k f ↔ Agent033.ComputesReLU n k f := by
  intro k
  induction k with
  | zero =>
      intro n f
      constructor
      · rintro ⟨T, hT⟩
        refine ⟨toB T, fun x => ?_⟩
        rw [hT]
        first
          | rfl
          | simp [Agent032.AffineMap'.eval, Agent033.AffineMapRn.eval, toB, Matrix.mulVec,
              dotProduct]
      · rintro ⟨T, hT⟩
        refine ⟨toA T, fun x => ?_⟩
        rw [hT]
        first
          | rfl
          | simp [Agent032.AffineMap'.eval, Agent033.AffineMapRn.eval, toA, Matrix.mulVec,
              dotProduct]
  | succ k ih =>
      intro n f
      constructor
      · rintro ⟨m, T, g, hg, hf⟩
        refine ⟨m, toB T, g, (ih m g).1 hg, fun x => ?_⟩
        rw [hf]
        first
          | rfl
          | simp [Agent032.reluVec, Agent033.reluVec, Agent032.relu, Agent033.relu,
              Agent032.AffineMap'.eval, Agent033.AffineMapRn.eval, toB, Matrix.mulVec,
              dotProduct]
      · rintro ⟨m, T, g, hg, hf⟩
        refine ⟨m, toA T, g, (ih m g).2 hg, fun x => ?_⟩
        rw [hf]
        first
          | rfl
          | simp [Agent032.reluVec, Agent033.reluVec, Agent032.relu, Agent033.relu,
              Agent032.AffineMap'.eval, Agent033.AffineMapRn.eval, toA, Matrix.mulVec,
              dotProduct]

theorem relun (n k : ℕ) : Agent032.ReLUn n k = Agent033.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, (computes_iff j n f).1 h⟩
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, (computes_iff j n f).2 h⟩

/-! ### `CPWL` -/

/-- The counterexample: the one-input-coordinate ReLU function. It is CPWL in the
polyhedral-subdivision sense (`Agent032`) but not in the local-agreement sense
(`Agent033`), since no single affine function can agree with it on a whole neighbourhood
of `0`. -/
private def f032 (x : Fin 1 → ℝ) : ℝ := max 0 (x 0)

private def x0 : Fin 1 → ℝ := fun _ => 0

private def φ032 (t : ℝ) : Fin 1 → ℝ := fun _ => t

private lemma φ032_continuous : Continuous φ032 :=
  continuous_pi (fun _ => continuous_id)

private lemma φ032_zero : φ032 0 = x0 := rfl

private lemma f032_continuous : Continuous f032 :=
  continuous_const.max (continuous_apply 0)

/-- The two half-spaces `x 0 ≤ 0` and `x 0 ≥ 0`, used as the polyhedral subdivision. -/
private def P032 : Bool → Set (Fin 1 → ℝ)
  | true => {x | x 0 ≤ 0}
  | false => {x | 0 ≤ x 0}

private lemma isPoly_true : Agent032.IsPolyhedron (P032 true) := by
  refine ⟨1, fun _ _ => 1, fun _ => 0, ?_⟩
  apply Set.ext
  intro x
  simp only [P032, Set.mem_setOf_eq]
  constructor
  · intro h j
    simpa [Fin.sum_univ_one] using h
  · intro h
    have h0 := h 0
    simpa [Fin.sum_univ_one] using h0

private lemma isPoly_false : Agent032.IsPolyhedron (P032 false) := by
  refine ⟨1, fun _ _ => -1, fun _ => 0, ?_⟩
  apply Set.ext
  intro x
  simp only [P032, Set.mem_setOf_eq]
  constructor
  · intro h j
    have : (-1 : ℝ) * x 0 ≤ 0 := by linarith
    simpa [Fin.sum_univ_one] using this
  · intro h
    have h0 := h 0
    simp only [Fin.sum_univ_one] at h0
    linarith

private lemma isAffine_true : Agent032.IsAffineOn f032 (P032 true) := by
  refine ⟨fun _ => 0, 0, ?_⟩
  intro x hx
  simp only [P032, Set.mem_setOf_eq] at hx
  show max 0 (x 0) = (∑ _i : Fin 1, (0 : ℝ) * x _i) + 0
  simp only [Fin.sum_univ_one, zero_mul, add_zero]
  exact max_eq_left hx

private lemma isAffine_false : Agent032.IsAffineOn f032 (P032 false) := by
  refine ⟨fun _ => 1, 0, ?_⟩
  intro x hx
  simp only [P032, Set.mem_setOf_eq] at hx
  show max 0 (x 0) = (∑ _i : Fin 1, (1 : ℝ) * x _i) + 0
  simp only [Fin.sum_univ_one, one_mul, add_zero]
  exact max_eq_right hx

private lemma f032_mem_032 : f032 ∈ Agent032.CPWL 1 := by
  refine ⟨f032_continuous, Bool, inferInstance, P032, ?_, ?_, ?_⟩
  · intro i
    cases i with
    | false => exact isPoly_false
    | true => exact isPoly_true
  · apply Set.eq_univ_of_forall
    intro x
    rcases le_total (x 0) 0 with h | h
    · exact Set.mem_iUnion.mpr ⟨true, h⟩
    · exact Set.mem_iUnion.mpr ⟨false, h⟩
  · intro i
    cases i with
    | false => exact isAffine_false
    | true => exact isAffine_true

private lemma f032_not_mem_033 : f032 ∉ Agent033.CPWL 1 := by
  rintro ⟨-, m, a, b, hprop⟩
  obtain ⟨i, U, hUopen, hx0U, hU⟩ := hprop x0
  have hpre_open : IsOpen (φ032 ⁻¹' U) := hUopen.preimage φ032_continuous
  have h0pre : (0 : ℝ) ∈ φ032 ⁻¹' U := by
    show φ032 0 ∈ U
    rw [φ032_zero]; exact hx0U
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hpre_open 0 h0pre
  have hball1 : (r / 2 : ℝ) ∈ Metric.ball (0 : ℝ) r := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith : (0:ℝ) < r / 2)]
    linarith
  have hy1 : φ032 (r / 2) ∈ U := hsub hball1
  have hball2 : (-(r / 2) : ℝ) ∈ Metric.ball (0 : ℝ) r := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero,
      abs_of_neg (by linarith : (-(r / 2) : ℝ) < 0)]
    linarith
  have hy2 : φ032 (-(r / 2)) ∈ U := hsub hball2
  have e0 := hU x0 hx0U
  have e1 := hU (φ032 (r / 2)) hy1
  have e2 := hU (φ032 (-(r / 2))) hy2
  unfold f032 φ032 x0 at e0 e1 e2
  simp only [Fin.sum_univ_one, mul_neg, mul_zero] at e0 e1 e2
  rw [max_self] at e0
  rw [max_eq_right (by linarith : (0:ℝ) ≤ r / 2)] at e1
  rw [max_eq_left (by linarith : -(r / 2) ≤ (0:ℝ))] at e2
  linarith [e0, e1, e2, hr]

theorem cpwl_ne : ∃ n, Agent032.CPWL n ≠ Agent033.CPWL n :=
  ⟨1, fun h => f032_not_mem_033 (h ▸ f032_mem_032)⟩

/-! ### `statement` -/

-- The right-hand side of this biconditional is false (`Agent033.CPWL` fails to equal
-- `ReLUn _ (depthBound _)`, by the same local-agreement defect as `cpwl_ne`, e.g. at
-- `n = 3`), but the left-hand side is exactly a restatement of the paper's actual
-- Theorem 2 for `Agent032`'s own (faithful) encoding, which neither `Agent032` nor this
-- bridge proves (it is `sorry`ed in `Thm2_032.lean`). Resolving `statement` therefore
-- requires resolving that open mathematical question, not just relating the two files.
theorem statement :
    (∀ n, 3 ≤ n → Agent032.CPWL n = Agent032.ReLUn n (Agent032.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent033.CPWL n = Agent033.ReLUn n (Agent033.depthBound n)) := by
  sorry

end Bridge_032_033

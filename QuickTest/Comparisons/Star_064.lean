import QuickTest.Formalizations.Thm2_064
import QuickTest.Reference

namespace Star_064

/-!
# Star comparison: `Agent064` vs `Ref`

* `depthBound` agrees, but only after the cast bridge `((n-1 : ℕ) : ℝ) = (n : ℝ) - 1`,
  which needs `1 ≤ n`; `hn` supplies it.
* `ReLUn` : `Agent064` takes **exactly** `k` hidden layers (a dimension-tagged `List Layer`
  evaluated through a `Σ'`-packaged state), `Ref` takes **at most** `k`.  These denote the
  same set, but only through the padding identity `x = relu x - relu (-x)`, a real theorem.
  Honest `sorry`.
* `CPWL` does **not** agree.  Despite the doc comment, `Agent064.CPWL` is the
  *neighbourhood-agreement* definition: every point has an **open** neighbourhood on which
  `f` coincides with one member of a finite affine family.  On connected `ℝⁿ` that forces
  `f` to be globally affine, so it is strictly stronger than `Ref.CPWL`: we refute `cpwl`
  and, better, prove the agent's own Theorem 2 false (`agent_side_false`).
-/

theorem relun (n k : ℕ) : Agent064.ReLUn n k = Ref.ReLUn n k := by
  -- Honest `sorry`: `Agent064` says *exactly* `k` hidden layers, `Ref` says *at most* `k`.
  -- Equality of the two sets is the padding theorem `x = relu x - relu (-x)`, not a
  -- bookkeeping translation.
  sorry

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent064.depthBound n = Ref.depthBound n := by
  have h : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  simp only [Agent064.depthBound, Ref.depthBound, h]

/-! ### `CPWL`: the agent's neighbourhood-agreement definition is strictly stronger -/

/-- Every halfspace is a polyhedron (intersection of the one-element family). -/
private lemma poly_of_half {n : ℕ} {S : Set (Fin n → ℝ)} (h : Ref.IsHalfspace n S) :
    Ref.IsPolyhedron n S :=
  ⟨1, fun _ => S, fun _ => h, by rw [Set.iInter_const]⟩

/-- `x ↦ max 0 (x 0)` is CPWL in the reference sense: the two halflines cover `ℝ`. -/
private lemma max_mem_ref : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Ref.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2,
    ![{x : Fin 1 → ℝ | ∑ j, (1 : ℝ) * x j ≤ 0}, {x : Fin 1 → ℝ | ∑ j, (-1 : ℝ) * x j ≤ 0}],
    ![fun _ => 0, fun x => x 0], ?_, ?_, ?_, ?_⟩
  · exact Fin.forall_fin_two.2 ⟨poly_of_half ⟨fun _ => 1, 0, rfl⟩,
      poly_of_half ⟨fun _ => -1, 0, rfl⟩⟩
  · exact Fin.forall_fin_two.2 ⟨⟨0, 0, by simp⟩, ⟨fun _ => 1, 0, by simp⟩⟩
  · refine Set.eq_univ_of_forall fun x => ?_
    rcases le_or_gt (x 0) 0 with hx | hx
    · refine Set.mem_iUnion.2 ⟨0, ?_⟩
      simp only [Matrix.cons_val_zero, Set.mem_setOf_eq, Fin.sum_univ_one, one_mul]
      linarith
    · refine Set.mem_iUnion.2 ⟨1, ?_⟩
      simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, Set.mem_setOf_eq,
        Fin.sum_univ_one, neg_mul, one_mul]
      linarith
  · refine Fin.forall_fin_two.2 ⟨fun x hx => ?_, fun x hx => ?_⟩
    · simp only [Matrix.cons_val_zero, Set.mem_setOf_eq, Fin.sum_univ_one, one_mul] at hx ⊢
      exact max_eq_left (by linarith)
    · simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, Set.mem_setOf_eq,
        Fin.sum_univ_one, neg_mul, one_mul] at hx ⊢
      exact max_eq_right (by linarith)

/-- `x ↦ max 0 (x 0)` is *not* in `Agent064.CPWL`: agreement with one affine map on an open
neighbourhood of the origin forces `max 0 t = a * t + b` for all small `t`; evaluating at
`0`, `r/2` and `-r/2` kills that. -/
private lemma max_not_mem (n : ℕ) :
    (fun x : Fin (n + 1) → ℝ => max 0 (x 0)) ∉ Agent064.CPWL (n + 1) := by
  rintro ⟨-, m, a, b, hloc⟩
  obtain ⟨i, U, hUo, h0U, hagree⟩ := hloc 0
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hUo 0 h0U
  have key : ∀ t : ℝ, |t| < r → max 0 t = (∑ j, a i j) * t + b i := by
    intro t ht
    have hd : (fun _ => t : Fin (n + 1) → ℝ) ∈ Metric.ball (0 : Fin (n + 1) → ℝ) r := by
      rw [Metric.mem_ball, dist_pi_lt_iff hr]
      intro j
      simpa [Real.dist_eq] using ht
    simpa [Finset.sum_mul] using hagree _ (hball hd)
  have h0 := key 0 (by simpa using hr)
  have h1 := key (r / 2) (by rw [abs_of_pos] <;> linarith)
  have h2 := key (-(r / 2)) (by rw [abs_of_neg] <;> linarith)
  rw [max_self] at h0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ r / 2)] at h1
  rw [max_eq_left (by linarith : -(r / 2) ≤ (0 : ℝ))] at h2
  nlinarith [h0, h1, h2]

/-- `Agent064.CPWL` is strictly stronger than `Ref.CPWL`, so the two differ. -/
theorem cpwl_ne : ∃ n, Agent064.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  have hmem : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent064.CPWL 1 := by
    rw [h]; exact max_mem_ref
  exact max_not_mem 0 hmem

/-! ### The agent's own Theorem 2 is false -/

private lemma depthBound_three : Agent064.depthBound 3 = 2 := by
  have hpos : (0 : ℝ) < Real.logb 3 2 := Real.logb_pos (by norm_num) (by norm_num)
  have hle : Real.logb 3 2 ≤ 1 := by
    rw [Real.logb, div_le_one (Real.log_pos (by norm_num))]
    gcongr <;> norm_num
  have hceil : ⌈Real.logb 3 (2 : ℝ)⌉₊ = 1 :=
    le_antisymm (Nat.ceil_le.mpr (by exact_mod_cast hle)) (Nat.ceil_pos.mpr hpos)
  have h : Agent064.depthBound 3 = ⌈Real.logb 3 (2 : ℝ)⌉₊ + 1 := by
    unfold Agent064.depthBound; norm_num
  rw [h, hceil]

/-- First layer: `ℝ³ → ℝ¹`, `x ↦ x 0`. -/
private def L1 : Agent064.Layer :=
  ⟨3, 1, ⟨Matrix.of fun _ j => if j = 0 then (1 : ℝ) else 0, 0⟩⟩

/-- The identity of `ℝ¹`, used as the second and third affine layer. -/
private def L2 : Agent064.Layer := ⟨1, 1, ⟨Matrix.of fun _ _ => (1 : ℝ), 0⟩⟩

/-- `max 0 (x 0)` on `ℝ³` is computed by a network with **exactly** two hidden layers:
read off `x 0`, then re-apply `relu`, which is idempotent. -/
private lemma relu3_mem :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent064.ReLUn 3 2 := by
  have hidem : ∀ t : ℝ, max 0 (max 0 t) = max 0 t := fun t => max_eq_right (le_max_left 0 t)
  refine ⟨[L1, L2, L2], rfl, fun x => ?_⟩
  have hstep : Agent064.evalLayers [L1, L2, L2] ⟨3, x⟩
      = ⟨1, L2.map.eval (Agent064.reluV (L2.map.eval (Agent064.reluV (L1.map.eval x))))⟩ := rfl
  refine hstep.trans (congrArg (fun v : Fin 1 → ℝ => (⟨1, v⟩ : Σ' b : ℕ, Fin b → ℝ)) ?_)
  funext i
  simp [L1, L2, Agent064.Affine.eval, Agent064.reluV, Agent064.reluR, Fin.sum_univ_one,
    Fin.sum_univ_three, hidem]

/-- The `Agent064` reading of Theorem 2 is outright false, with no reference theorem
involved: at `n = 3` the ramp is a two-hidden-layer network but its neighbourhood-agreement
`CPWL` rejects the kink at the origin. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent064.CPWL n = Agent064.ReLUn n (Agent064.depthBound n)) := by
  intro h
  have h3 := h 3 (by norm_num)
  rw [depthBound_three] at h3
  refine max_not_mem 2 ?_
  rw [h3]
  exact relu3_mem

/-- The two readings of Theorem 2 are *not* equivalent: the left side is false
(`agent_side_false`), while the right side is the real Theorem 2, which is true.
Honest `sorry`: discharging it needs the true direction of `Ref.theorem2`, which is itself
`sorry`-ed, and routing through it is forbidden. -/
theorem statement_ne :
    ¬ ((∀ n, 3 ≤ n → Agent064.CPWL n = Agent064.ReLUn n (Agent064.depthBound n)) ↔
      (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n))) := by
  intro hiff
  exact agent_side_false (hiff.2 (by sorry))

end Star_064

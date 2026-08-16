namespace Bridge_082_083

/-- Both agents compute `depthBound` via the literally identical expression
`⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1` (`Nat.ceil` and the notation `⌈·⌉₊` are the same thing),
so the two functions are definitionally equal. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent082.depthBound n = Agent083.depthBound n := rfl

/-- Witness distinguishing the two `CPWL` definitions on `n = 1`: `f x = max 0 (x 0)`.
Agent082's `CPWL` demands *local* agreement (an open neighbourhood on which `f` coincides with a
single affine piece); Agent083's demands a *global* polyhedral cover by closed convex pieces.
`f` is a textbook piecewise-affine function, hence lies in Agent083's `CPWL 1` (pieces
`{x 0 ≤ 0}`, `{0 ≤ x 0}`), but at `x = 0` no single affine function can agree with `f` on an
entire open neighbourhood (any such neighbourhood meets both `x 0 > 0` and `x 0 < 0`), so `f`
fails Agent082's local-agreement definition. -/
noncomputable def f : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

theorem f_cont : Continuous f := continuous_const.max (continuous_apply 0)

def pieces083 : Fin 2 → Set (Fin 1 → ℝ) :=
  fun i => if i = 0 then {x | x 0 ≤ 0} else {x | 0 ≤ x 0}

def affines083 : Fin 2 → ((Fin 1 → ℝ) → ℝ) :=
  fun i => if i = 0 then (fun _ => 0) else (fun x => x 0)

theorem f_mem_083 : f ∈ Agent083.CPWL 1 := by
  refine ⟨f_cont, 2, pieces083, affines083, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; by_cases hi : i = 0
    · simp only [affines083, if_pos hi]
      exact ⟨fun _ => 0, 0, fun x => by simp⟩
    · simp only [affines083, if_neg hi]
      exact ⟨fun _ => 1, 0, fun x => by simp [Fin.sum_univ_one]⟩
  · intro i; by_cases hi : i = 0
    · simp only [pieces083, if_pos hi]
      intro x hx y hy a b ha hb hab
      simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
      nlinarith [mul_nonneg ha (neg_nonneg.mpr hx), mul_nonneg hb (neg_nonneg.mpr hy)]
    · simp only [pieces083, if_neg hi]
      intro x hx y hy a b ha hb hab
      simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
      nlinarith [mul_nonneg ha hx, mul_nonneg hb hy]
  · intro i; by_cases hi : i = 0
    · simp only [pieces083, if_pos hi]
      exact isClosed_le (continuous_apply 0) continuous_const
    · simp only [pieces083, if_neg hi]
      exact isClosed_le continuous_const (continuous_apply 0)
  · apply Set.eq_univ_iff_forall.mpr
    intro x
    rcases le_total (x 0) 0 with h | h
    · refine Set.mem_iUnion.mpr ⟨0, ?_⟩
      simp only [pieces083, if_pos (rfl : (0 : Fin 2) = 0), Set.mem_setOf_eq]
      exact h
    · refine Set.mem_iUnion.mpr ⟨1, ?_⟩
      simp only [pieces083, if_neg (by decide : ¬ (1 : Fin 2) = 0), Set.mem_setOf_eq]
      exact h
  · intro i; by_cases hi : i = 0
    · simp only [pieces083, affines083, if_pos hi]
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      simp [f, max_eq_left hx]
    · simp only [pieces083, affines083, if_neg hi]
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      simp [f, max_eq_right hx]

theorem f_not_mem_082 : f ∉ Agent082.CPWL 1 := by
  rintro ⟨-, m, g, hg_affine, hloc⟩
  obtain ⟨j, U, hU, hUeq⟩ := hloc (fun _ => (0 : ℝ))
  have hcont : Continuous (fun t : ℝ => (fun _ : Fin 1 => t)) := continuous_pi fun _ => continuous_id
  have hca : ContinuousAt (fun t : ℝ => (fun _ : Fin 1 => t)) 0 := hcont.continuousAt
  have hpre : (fun t : ℝ => (fun _ : Fin 1 => t)) ⁻¹' U ∈ nhds (0 : ℝ) := hca.preimage_mem_nhds hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  obtain ⟨a, b, hab⟩ := hg_affine j
  have hballpt : ∀ t : ℝ, |t| < ε → (fun _ : Fin 1 => t) ∈ U := fun t ht' =>
    hball (by rw [Metric.mem_ball, Real.dist_eq, sub_zero]; exact ht')
  have h0 : (fun _ : Fin 1 => (0 : ℝ)) ∈ U := hballpt 0 (by rw [abs_zero]; exact hε)
  have ht : (fun _ : Fin 1 => (ε / 2 : ℝ)) ∈ U :=
    hballpt (ε / 2) (by rw [abs_of_pos (show (0 : ℝ) < ε / 2 by linarith)]; linarith)
  have hmt : (fun _ : Fin 1 => (-(ε / 2) : ℝ)) ∈ U :=
    hballpt (-(ε / 2)) (by rw [abs_of_neg (show -(ε / 2 : ℝ) < 0 by linarith)]; linarith)
  have e0 := hUeq _ h0
  have et := hUeq _ ht
  have emt := hUeq _ hmt
  simp only [f, hab, Fin.sum_univ_one] at e0 et emt
  rw [max_self] at e0
  rw [max_eq_right (show (0 : ℝ) ≤ ε / 2 by linarith)] at et
  rw [max_eq_left (show -(ε / 2 : ℝ) ≤ 0 by linarith)] at emt
  nlinarith [e0, et, emt, hε]

theorem cpwl_ne : ∃ n, Agent082.CPWL n ≠ Agent083.CPWL n := by
  refine ⟨1, fun h => f_not_mem_082 ?_⟩
  rw [h]; exact f_mem_083

-- `relun`: both agents define `ReLUn n k` as "at most k layers" over a structurally similar but
-- syntactically different exact-representation notion (Agent082.NetComputes is a recursive
-- Prop, Agent083.ReLUNet is an inductive type); proving them equal needs an induction on `k`
-- matching the two peeling schemes against each other, which is not attempted here.
theorem relun (n k : ℕ) : Agent082.ReLUn n k = Agent083.ReLUn n k := sorry

-- `statement`: relates each agent's own unproved rendering of Theorem 2. Since `cpwl_ne` shows
-- the `CPWL` definitions genuinely differ, this iff cannot be derived cheaply from the other
-- three bridges, and proving it directly would require proving Theorem 2 itself for at least
-- one agent, which is out of scope for this bridge.
theorem statement :
    (∀ n, 3 ≤ n → Agent082.CPWL n = Agent082.ReLUn n (Agent082.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent083.CPWL n = Agent083.ReLUn n (Agent083.depthBound n)) := sorry

end Bridge_082_083

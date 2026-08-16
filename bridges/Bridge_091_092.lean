namespace Bridge_091_092

-- Counterexample separating the two `CPWL` readings: a kink at `0`, showing
-- Agent091's global polyhedral-subdivision reading and Agent092's pointwise
-- local-affine-agreement reading disagree (the latter excludes ReLU itself).
def bump : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

-- The two half-space pieces `x 0 ≥ 0` and `x 0 ≤ 0` covering `Fin 1 → ℝ`.
def bumpHS (i : Fin 2) : Fin 1 → Agent091.Halfspace 1 :=
  fun _ => if i = 0 then ⟨fun _ => (-1 : ℝ), 0⟩ else ⟨fun _ => (1 : ℝ), 0⟩

-- Matching affine pieces: `x ↦ x 0` on the first, `x ↦ 0` on the second.
def bumpAF (i : Fin 2) : Agent091.AffineFun 1 1 :=
  if i = 0 then (fun _ _ => (1 : ℝ), fun _ => (0 : ℝ))
  else (fun _ _ => (0 : ℝ), fun _ => (0 : ℝ))

theorem bump_mem_091 : bump ∈ Agent091.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2, fun _ => 1, bumpHS, bumpAF, ?_, ?_⟩
  · ext x
    simp only [Set.mem_iUnion, Set.mem_iInter, Set.mem_univ, iff_true]
    rcases le_total (x 0) 0 with h | h
    · refine ⟨1, fun _ => ?_⟩
      simp only [bumpHS, if_neg (show (1 : Fin 2) ≠ 0 by decide), Agent091.Halfspace.set,
        Set.mem_setOf_eq, Fin.sum_univ_one]
      linarith
    · refine ⟨0, fun _ => ?_⟩
      simp only [bumpHS, if_pos rfl, Agent091.Halfspace.set, Set.mem_setOf_eq, Fin.sum_univ_one]
      linarith
  · intro i x hx
    by_cases hi : i = 0
    · have h0 : 0 ≤ x 0 := by
        have hj := hx 0
        simp only [bumpHS, if_pos hi, Agent091.Halfspace.set, Set.mem_setOf_eq,
          Fin.sum_univ_one] at hj
        linarith
      simp only [bumpAF, if_pos hi, Agent091.AffineFun.eval, Fin.sum_univ_one, bump,
        one_mul, add_zero]
      exact max_eq_right_iff.2 h0
    · have h0 : x 0 ≤ 0 := by
        have hj := hx 0
        simp only [bumpHS, if_neg hi, Agent091.Halfspace.set, Set.mem_setOf_eq,
          Fin.sum_univ_one] at hj
        linarith
      simp only [bumpAF, if_neg hi, Agent091.AffineFun.eval, Fin.sum_univ_one, bump,
        zero_mul, add_zero]
      exact max_eq_left_iff.2 h0

theorem bump_not_mem_092 : bump ∉ Agent092.CPWL 1 := by
  rintro ⟨-, m, g, hg⟩
  obtain ⟨i, hi⟩ := hg (fun _ => (0 : ℝ))
  rw [Metric.eventually_nhds_iff] at hi
  obtain ⟨ε, hε, hball⟩ := hi
  have e0 : bump (fun _ => (0 : ℝ)) = (g i).eval (fun _ => (0 : ℝ)) := by
    apply hball; rw [dist_self]; exact hε
  have e1 : bump (fun _ => (ε / 2 : ℝ)) = (g i).eval (fun _ => (ε / 2 : ℝ)) := by
    apply hball
    rw [dist_pi_const, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]; linarith
  have e2 : bump (fun _ => (-(ε / 2) : ℝ)) = (g i).eval (fun _ => (-(ε / 2) : ℝ)) := by
    apply hball
    rw [dist_pi_const, Real.dist_eq, sub_zero, abs_neg, abs_of_pos (half_pos hε)]; linarith
  simp only [bump, Agent092.AffineFunc.eval, Agent092.affineEval, Pi.add_apply, Matrix.mulVec,
    Matrix.dotProduct, Fin.sum_univ_one, max_self, mul_zero, zero_add] at e0 e1 e2
  rw [← e0, add_zero] at e1 e2
  rw [max_eq_right_iff.2 (by linarith : (0 : ℝ) ≤ ε / 2)] at e1
  rw [max_eq_left_iff.2 (by linarith : (-(ε / 2) : ℝ) ≤ 0)] at e2
  rcases mul_eq_zero.mp e2.symm with hc | hc
  · rw [hc, zero_mul] at e1; linarith
  · linarith

-- cpwl is false: the two `CPWL` readings disagree already at `n = 1`.
theorem cpwl_ne : ∃ n, Agent091.CPWL n ≠ Agent092.CPWL n := by
  refine ⟨1, fun h => bump_not_mem_092 ?_⟩
  rw [← h]; exact bump_mem_091

-- relun: Agent091 reads "at most k" hidden layers, Agent092 reads "exactly k".
-- The two coincide only via the identity-padding trick x = relu x - relu (-x),
-- iterated k - k' times; nobody has proved this padding lemma (BRIDGE_SPEC.md)
-- and it does not fit this bridge's line budget, so it is left open.
theorem relun (n k : ℕ) : Agent091.ReLUn n k = Agent092.ReLUn n k := by
  sorry

theorem depth (n : ℕ) (hn : 3 ≤ n) :
    Agent091.depthBound n = Agent092.depthBound n := by
  unfold Agent091.depthBound Agent092.depthBound
  congr 1
  have hm1 : 1 < n - 1 := by omega
  have hb : (1 : ℕ) < 3 := by norm_num
  have h1 : n - 1 ≤ 3 ^ Nat.clog 3 (n - 1) := Nat.le_pow_clog hb (n - 1)
  have h2 : 3 ^ (Nat.clog 3 (n - 1) - 1) < n - 1 := Nat.pow_pred_clog_lt_self hb hm1
  have hk0 : Nat.clog 3 (n - 1) ≠ 0 := by
    intro h0; rw [h0, pow_zero] at h1; omega
  have hcastx : ((n : ℝ) - 1) = ((n - 1 : ℕ) : ℝ) := by
    have hle : (1 : ℕ) ≤ n := by omega
    rw [Nat.cast_sub hle, Nat.cast_one]
  have hbR : (1 : ℝ) < 3 := by norm_num
  have hxpos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - 1)
  have hub : Real.logb 3 ((n - 1 : ℕ) : ℝ) ≤ ((Nat.clog 3 (n - 1) : ℕ) : ℝ) := by
    rw [Real.logb_le_iff_le_rpow hbR hxpos, Real.rpow_natCast]
    exact_mod_cast h1
  have hlb : ((Nat.clog 3 (n - 1) - 1 : ℕ) : ℝ) < Real.logb 3 ((n - 1 : ℕ) : ℝ) := by
    rw [Real.lt_logb_iff_rpow_lt hbR hxpos, Real.rpow_natCast]
    exact_mod_cast h2
  have hceil : Nat.ceil (Real.logb 3 ((n - 1 : ℕ) : ℝ)) = Nat.clog 3 (n - 1) := by
    rw [Nat.ceil_eq_iff hk0]; exact ⟨hlb, hub⟩
  rw [hcastx, hceil]

-- statement: cpwl_ne shows CPWL genuinely differs via a kink argument that works
-- at every n ≥ 1, including throughout n ≥ 3, so there is no CPWL equality to
-- transport through the iff; deciding it outright needs the truth of each
-- agent's theorem2 independently, which we are told not to use. Left open.
theorem statement :
    (∀ n, 3 ≤ n → Agent091.CPWL n = Agent091.ReLUn n (Agent091.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent092.CPWL n = Agent092.ReLUn n (Agent092.depthBound n)) := by
  sorry

end Bridge_091_092

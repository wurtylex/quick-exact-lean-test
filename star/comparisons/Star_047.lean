namespace Star_047

/-! # Agent 047 vs. the reference

Agent 047 defines `CPWL n` by agreement with one of finitely many affine maps on a
**neighbourhood** of every point (`∀ᶠ y in nhds x, f y = g i y`).  On the connected
space `ℝⁿ` that condition is strictly stronger than piecewise linearity, so its `CPWL`
is a proper subset of the reference's and its Theorem 2 is *false* outright.

`depthBound` is literally the reference's definition, so `depth` is `rfl`.
`ReLUn` agrees semantically but is built from the output side rather than the input
side, so `relun` needs a genuine network-reversal argument; it is left `sorry`. -/

private def kink (n : ℕ) (i : Fin n) : (Fin n → ℝ) → ℝ := fun x => max 0 (x i)

/-- The coordinate line `t ↦ t • eᵢ`, used to pull a neighbourhood of `0` in `ℝⁿ`
back to a neighbourhood of `0` in `ℝ`. -/
private def bump (n : ℕ) (i : Fin n) : ℝ → (Fin n → ℝ) := fun t j => if j = i then t else 0

private lemma bump_continuous (n : ℕ) (i : Fin n) : Continuous (bump n i) :=
  continuous_pi fun j => by
    by_cases h : j = i
    · simp only [bump, if_pos h]; exact continuous_id
    · simp only [bump, if_neg h]; exact continuous_const

private lemma bump_zero (n : ℕ) (i : Fin n) : bump n i 0 = 0 := by
  funext j; simp [bump]

/-- No affine functional agrees with `x ↦ max 0 (x i)` on a whole neighbourhood of `0`:
the kink at the origin obstructs it. -/
private lemma kink_not_locally_affine (n : ℕ) (i : Fin n) (a : Fin n → ℝ) (b : ℝ)
    (h : ∀ᶠ y in nhds (0 : Fin n → ℝ), kink n i y = (∑ j, a j * y j) + b) : False := by
  have hb : Filter.Tendsto (bump n i) (nhds (0 : ℝ)) (nhds (0 : Fin n → ℝ)) := by
    have := (bump_continuous n i).tendsto (0 : ℝ)
    rwa [bump_zero] at this
  have h2 : ∀ᶠ t in nhds (0 : ℝ), max 0 t = a i * t + b := by
    filter_upwards [hb.eventually h] with t ht
    have hsum : (∑ j, a j * bump n i t j) = a i * t := by
      rw [Finset.sum_eq_single i]
      · simp [bump]
      · intro j _ hj; simp [bump, hj]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    have hl : kink n i (bump n i t) = max 0 t := by simp [kink, bump]
    rw [hl, hsum] at ht
    exact ht
  rw [Metric.eventually_nhds_iff] at h2
  obtain ⟨ε, hε, hall⟩ := h2
  have hz := hall (show dist (0 : ℝ) 0 < ε by simpa using hε)
  have hp := hall (show dist (ε / 2 : ℝ) 0 < ε by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
  have hm := hall (show dist (-(ε / 2) : ℝ) 0 < ε by
    rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by linarith)]; linarith)
  rw [max_self, mul_zero, zero_add] at hz
  rw [max_eq_right (by linarith : (0:ℝ) ≤ ε / 2), ← hz, add_zero] at hp
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0:ℝ)), ← hz, add_zero, mul_neg] at hm
  linarith

/-- The kink is never in agent 047's neighbourhood-agreement `CPWL`. -/
private lemma kink_not_cpwl (n : ℕ) (i : Fin n) : kink n i ∉ Agent047.CPWL n := by
  intro hmem
  obtain ⟨-, m, g, hg, hloc⟩ := hmem
  obtain ⟨j, hj⟩ := hloc 0
  obtain ⟨a, b, hab⟩ := hg j
  refine kink_not_locally_affine n i a b ?_
  filter_upwards [hj] with y hy
  rw [hy, hab]

/-! ### The kink *is* CPWL in the reference sense (two halfspaces) -/

private def refP : Fin 2 → Set (Fin 1 → ℝ) :=
  fun i => if i = 0 then {x | x 0 ≤ 0} else {x | (0:ℝ) ≤ x 0}

private def refG : Fin 2 → ((Fin 1 → ℝ) → ℝ) :=
  fun i => if i = 0 then (fun _ => 0) else (fun x => x 0)

private lemma halfspace_isPolyhedron {n : ℕ} {S : Set (Fin n → ℝ)}
    (h : Ref.IsHalfspace n S) : Ref.IsPolyhedron n S :=
  ⟨1, fun _ => S, fun _ => h, by ext x; simp⟩

private lemma kink_mem_ref : kink 1 0 ∈ Ref.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply (0 : Fin 1)), 2, refP, refG, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases h : i = 0
    · simp only [refP, if_pos h]
      exact halfspace_isPolyhedron ⟨fun _ => 1, 0, by ext x; simp⟩
    · simp only [refP, if_neg h]
      exact halfspace_isPolyhedron ⟨fun _ => -1, 0, by ext x; simp⟩
  · intro i
    by_cases h : i = 0
    · exact ⟨0, 0, by intro x; simp [refG, h]⟩
    · exact ⟨fun _ => 1, 0, by intro x; simp [refG, h]⟩
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    rcases le_total (x 0) 0 with h | h
    · exact ⟨0, by simpa [refP] using h⟩
    · exact ⟨1, by simpa [refP] using h⟩
  · intro i x hx
    by_cases h : i = 0
    · simp only [refP, if_pos h, Set.mem_setOf_eq] at hx
      simp only [refG, if_pos h, kink]
      exact max_eq_left hx
    · simp only [refP, if_neg h, Set.mem_setOf_eq] at hx
      simp only [refG, if_neg h, kink]
      exact max_eq_right hx

/-! ### The obligations -/

/-- Agent 047's `CPWL` is strictly stronger than the reference's: `max 0 (x 0)` is
reference-CPWL on `ℝ¹` but has no affine agreement on any neighbourhood of `0`. -/
theorem cpwl_ne : ∃ n, Agent047.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  have hmem : kink 1 0 ∈ Agent047.CPWL 1 := by rw [h]; exact kink_mem_ref
  exact kink_not_cpwl 1 0 hmem

-- Both sides are "at most `k` hidden layers", but agent 047 recurses from the output
-- side (`NetComputes n p k g` then one ReLU and one affine map) while the reference
-- recurses from the input side.  Equating them is the network-reversal/padding
-- argument, a real theorem; not attempted here.
theorem relun (n k : ℕ) : Agent047.ReLUn n k = Ref.ReLUn n k := sorry

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent047.depthBound n = Ref.depthBound n := rfl

/-- `max 0 (x 0)` on `ℝ³` is a one-hidden-layer ReLU network. -/
private lemma kink_relu_computable : Agent047.ReluComputable 3 1 (kink 3 0) :=
  ⟨1, (fun x _ => x 0), 1, 0,
    ⟨Matrix.of (fun _ j => if j = 0 then (1:ℝ) else 0), 0, by
      intro x
      funext i
      show x 0 = (∑ j : Fin 3, (if j = 0 then (1:ℝ) else 0) * x j) + (0 : Fin 1 → ℝ) i
      rw [Fin.sum_univ_three]
      simp⟩,
    by
      intro x
      funext i
      simp [Agent047.affineApply, Agent047.reluVec, Agent047.relu, kink,
        Matrix.one_mulVec]⟩

/-- Agent 047's Theorem 2 is false on its own terms: at `n = 3` the ReLU class contains
`max 0 (x 0)`, which its neighbourhood-agreement `CPWL` does not. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent047.CPWL n = Agent047.ReLUn n (Agent047.depthBound n)) := by
  intro h
  have hmem : kink 3 0 ∈ Agent047.ReLUn 3 (Agent047.depthBound 3) :=
    ⟨1, by simp only [Agent047.depthBound]; omega, kink_relu_computable⟩
  rw [← h 3 le_rfl] at hmem
  exact kink_not_cpwl 3 0 hmem

/-- Since the agent side is provably false, the biconditional holds exactly when the
reference side fails. -/
theorem statement_reduces :
    ((∀ n, 3 ≤ n → Agent047.CPWL n = Agent047.ReLUn n (Agent047.depthBound n)) ↔
      (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n))) ↔
      ¬ (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) :=
  ⟨fun h hR => agent_side_false (h.mpr hR),
   fun hR => ⟨fun hA => absurd hA agent_side_false, fun hRf => absurd hRf hR⟩⟩

-- By `statement_reduces` this is equivalent to *refuting* the reference's Theorem 2,
-- which is the true (and hard) theorem of the paper; so it cannot be settled here
-- without proving Theorem 2 itself.
theorem statement :
    (∀ n, 3 ≤ n → Agent047.CPWL n = Agent047.ReLUn n (Agent047.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_047

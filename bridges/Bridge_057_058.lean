namespace Bridge_057_058

/-- Both agents use the syntactically identical formula `⌈log_3 (n - 1)⌉₊ + 1`. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) :
    Agent057.depthBound n = Agent058.depthBound n := rfl

/-- The ReLU kink at `0`, in dimension `1`. Witnesses the difference between the two
`CPWL` definitions: Agent057 uses a polyhedral subdivision (kinks allowed), Agent058
uses "agrees with a fixed affine map on an *open* neighborhood of every point", which
on the connected space `ℝ^1` forbids any genuine kink. -/
noncomputable def kink : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

theorem kink_continuous : Continuous kink :=
  continuous_const.max (continuous_apply 0)

noncomputable def A1 : (Fin 1 → ℝ) →ᵃ[ℝ] ℝ :=
  AffineMap.mk' (fun x : Fin 1 → ℝ => x 0) (LinearMap.proj (0 : Fin 1)) 0
    (fun p' => by simp)

noncomputable def A2 : (Fin 1 → ℝ) →ᵃ[ℝ] ℝ :=
  AffineMap.mk' (fun _ : Fin 1 → ℝ => (0 : ℝ)) 0 0 (fun p' => by simp)

theorem kink_mem_057 : kink ∈ Agent057.CPWL 1 := by
  refine ⟨kink_continuous, Bool, inferInstance,
    fun b => if b then {x : Fin 1 → ℝ | 0 ≤ x 0} else {x : Fin 1 → ℝ | x 0 ≤ 0},
    fun b => if b then A1 else A2, ?_, ?_, ?_⟩
  · intro b
    cases b with
    | false =>
        exact ⟨Unit, inferInstance, fun _ => LinearMap.proj (0 : Fin 1), fun _ => 0, by
          ext x; simp [Set.mem_iInter, Set.mem_setOf_eq, LinearMap.proj_apply]⟩
    | true =>
        exact ⟨Unit, inferInstance, fun _ => -(LinearMap.proj (0 : Fin 1)), fun _ => 0, by
          ext x; simp [Set.mem_iInter, Set.mem_setOf_eq, LinearMap.proj_apply, neg_nonpos]⟩
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    rcases le_total 0 (x 0) with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  · intro b x hx
    cases b with
    | false => simpa [kink, A2] using max_eq_left hx
    | true => simpa [kink, A1] using max_eq_right hx

theorem kink_not_mem_058 : kink ∉ Agent058.CPWL 1 := by
  rintro ⟨-, m, g, hg⟩
  obtain ⟨i, hi⟩ := hg 0
  have hφ : Continuous (fun t : ℝ => (fun _ : Fin 1 => t)) :=
    continuous_pi fun _ => continuous_id
  have hi' : ∀ᶠ t in nhds (0 : ℝ), kink (fun _ : Fin 1 => t) = (g i).eval (fun _ => t) 0 :=
    (hφ.tendsto 0).eventually hi
  rw [Metric.eventually_nhds_iff] at hi'
  obtain ⟨ε, hε, hball⟩ := hi'
  have h0 := hball (show dist (0 : ℝ) 0 < ε by rw [dist_self]; exact hε)
  have hp := hball (show dist (ε / 2) 0 < ε by
    rw [Real.dist_eq, sub_zero, abs_lt]; constructor <;> linarith)
  have hn := hball (show dist (-(ε / 2)) 0 < ε by
    rw [Real.dist_eq, sub_zero, abs_lt]; constructor <;> linarith)
  have heval : ∀ t : ℝ, (g i).eval (fun _ : Fin 1 => t) 0
      = (g i).A 0 0 * t + (g i).c 0 := by
    intro t
    simp [Agent058.AffineMapRn.eval, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_one,
      Pi.add_apply]
  simp only [kink] at h0 hp hn
  rw [heval] at h0 hp hn
  rw [max_self, mul_zero, zero_add] at h0
  rw [max_eq_right (show (0 : ℝ) ≤ ε / 2 by linarith)] at hp
  rw [max_eq_left (show -(ε / 2) ≤ (0 : ℝ) by linarith), mul_neg] at hn
  linarith

/-- Refutation: the ReLU kink lies in Agent057's `CPWL 1` (two half-space pieces) but
not in Agent058's `CPWL 1`, because Agent058's "affine on an open neighborhood of every
point" reading forces global affineness on the connected domain `ℝ^1`, excluding any
function with an actual kink. -/
theorem cpwl_ne : ∃ n, Agent057.CPWL n ≠ Agent058.CPWL n :=
  ⟨1, fun h => kink_not_mem_058 (h ▸ kink_mem_057)⟩

/-- SORRY: `ReLUn` is "at most k hidden layers" on both sides, but the encodings are
structurally incompatible (an inductive predicate recursing from the output vs. an
explicit `netApply` over a dependent width-indexed layer family recursing from the
input); bridging them needs a real induction/padding argument not attempted here. -/
theorem relun (n k : ℕ) : Agent057.ReLUn n k = Agent058.ReLUn n k := sorry

/-- SORRY: since `cpwl` is refuted (the two `CPWL` predicates are genuinely different
sets), the two instances of Theorem 2 are statements about different hypotheses, and
neither `theorem2` proof is available (both are `sorry`); deciding the `Iff` honestly
would require independently resolving both theorems, which is out of scope here. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent057.CPWL n = Agent057.ReLUn n (Agent057.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent058.CPWL n = Agent058.ReLUn n (Agent058.depthBound n)) := sorry

end Bridge_057_058

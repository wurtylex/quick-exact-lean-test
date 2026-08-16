namespace Bridge_072_073

/-!
## Summary of the comparison

* `depthBound` is *syntactically identical* in both files: `⌈Real.logb 3 ((n:ℝ)-1)⌉₊+1`.
  So `depth` is essentially `rfl`.
* `ReLUn`: Agent072 uses "at most `k` hidden layers" (`∃ k' ≤ k, …`); Agent073 uses
  "exactly `k` hidden layers". These plausibly coincide via the identity-padding
  trick, but that padding lemma is unproved and combining it with matching the two
  different recursions (`IsReLUNet` vs `IsReLURep`) is too large for this file, so
  `relun` is left `sorry`.
* `CPWL`: Agent072 uses a genuine polyhedral-subdivision definition (family (a)).
  Agent073 uses "local agreement with a *fixed finite* family of affine functions"
  (family (b)): `∀ x, ∃ T ∈ S, ∀ᶠ y, f y = T y`. Since `S` is fixed in advance and
  finite, and `ℝⁿ` is connected, this forces `f` to be *globally* affine: the sets
  `{x | f agrees with T near x}`, for `T ∈ S`, are open, pairwise disjoint (two
  affine functions agreeing near a point are equal, since affine functions equal on
  an open set are equal everywhere), and cover `ℝⁿ`; connectedness forces exactly one
  of them to be everything. So Agent073.CPWL n is only the globally-affine functions,
  which does *not* contain a genuinely kinked function such as `x ↦ max 0 (x 0)` —
  even though that function certainly is continuous, piecewise-linear, in
  Agent072.CPWL 1. This yields a clean refutation of `cpwl`.
-/

/-- The depth bounds are literally the same expression. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent072.depthBound n = Agent073.depthBound n := rfl

/-- The "kinked" ReLU-type function on `ℝ¹`, witnessing that Agent072's and
Agent073's `CPWL` differ. -/
private def kink : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

private lemma kink_mem_072 : kink ∈ Agent072.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2,
    ![{x : Fin 1 → ℝ | 0 ≤ x 0}, {x : Fin 1 → ℝ | x 0 ≤ 0}],
    ![fun x : Fin 1 → ℝ => x 0, fun _ : Fin 1 → ℝ => (0 : ℝ)],
    fun i => ?_, fun i => ?_, ?_, fun i => ?_⟩
  · fin_cases i
    · exact ⟨1, fun _ _ => (-1 : ℝ), fun _ => 0, by
        ext x
        simp only [Set.mem_setOf_eq, Fin.forall_fin_one, Fin.sum_univ_one]
        constructor <;> intro h <;> linarith⟩
    · exact ⟨1, fun _ _ => (1 : ℝ), fun _ => 0, by
        ext x
        simp only [Set.mem_setOf_eq, Fin.forall_fin_one, Fin.sum_univ_one]
        constructor <;> intro h <;> linarith⟩
  · fin_cases i
    · exact ⟨fun _ => (1 : ℝ), 0, by funext x; simp [Fin.sum_univ_one]⟩
    · exact ⟨fun _ => (0 : ℝ), 0, by funext x; simp [Fin.sum_univ_one]⟩
  · refine Set.eq_univ_iff_forall.mpr fun x => ?_
    rcases le_total 0 (x 0) with h | h
    · exact Set.mem_iUnion.mpr ⟨0, h⟩
    · exact Set.mem_iUnion.mpr ⟨1, h⟩
  · fin_cases i
    · exact fun x hx => max_eq_right hx
    · exact fun x hx => max_eq_left hx

private lemma kink_not_mem_073 : kink ∉ Agent073.CPWL 1 := by
  rintro ⟨-, S, hS⟩
  obtain ⟨T, -, U, hU, hT⟩ := hS (0 : Fin 1 → ℝ)
  have hcont : Continuous (fun r : ℝ => (fun _ : Fin 1 => r)) :=
    continuous_pi (fun _ => continuous_id)
  have hU0 : U ∈ nhds (fun _ : Fin 1 => (0 : ℝ)) := hU
  have hpre : (fun r : ℝ => (fun _ : Fin 1 => r)) ⁻¹' U ∈ nhds (0 : ℝ) :=
    hcont.continuousAt.preimage_mem_nhds hU0
  rw [Metric.mem_nhds_iff] at hpre
  obtain ⟨ε, hε, hball⟩ := hpre
  have hmem : ∀ r : ℝ, |r| < ε → (fun _ : Fin 1 => r) ∈ U := by
    intro r hr
    have hrb : r ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq]; simpa using hr
    exact hball hrb
  have heval : ∀ r : ℝ, T.eval (fun _ : Fin 1 => r) 0 = T.A 0 0 * r + T.c 0 := by
    intro r
    simp [Agent073.AffineMap.eval, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_one]
  have key : ∀ r : ℝ, |r| < ε → max 0 r = T.A 0 0 * r + T.c 0 := by
    intro r hr
    have hy := hT (fun _ : Fin 1 => r) (hmem r hr)
    simpa [kink, heval r] using hy
  have e1 := key (ε / 2) (by rw [abs_of_pos (by linarith : (0:ℝ) < ε / 2)]; linarith)
  have e2 := key (ε / 4) (by rw [abs_of_pos (by linarith : (0:ℝ) < ε / 4)]; linarith)
  have e3 := key (-(ε / 2)) (by rw [abs_of_neg (by linarith : -(ε / 2) < (0:ℝ))]; linarith)
  rw [max_eq_right (by linarith : (0:ℝ) ≤ ε / 2)] at e1
  rw [max_eq_right (by linarith : (0:ℝ) ≤ ε / 4)] at e2
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0:ℝ))] at e3
  set A := T.A 0 0
  have h1 : ε * (A - 1) = 0 := by linear_combination 4 * e2 - 4 * e1
  have h2 : ε * (3 * A - 1) = 0 := by linear_combination 4 * e3 - 4 * e2
  have hεne : ε ≠ 0 := ne_of_gt hε
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd h hεne
  · rcases mul_eq_zero.mp h2 with h' | h'
    · exact absurd h' hεne
    · linarith

/-- Agent072's `CPWL` (genuine polyhedral subdivision) and Agent073's `CPWL` (local
agreement with a fixed finite family, which forces global affineness on the connected
domain `ℝⁿ`) genuinely differ: the kink function `x ↦ max 0 (x 0)` is in the former
but not the latter. -/
theorem cpwl_ne : ∃ n, Agent072.CPWL n ≠ Agent073.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  have hmem := kink_mem_072
  rw [h] at hmem
  exact kink_not_mem_073 hmem

/- `relun`: Agent072.ReLUn n k means "at most k hidden layers"; Agent073.ReLUn n k
means "exactly k hidden layers". These plausibly coincide via the identity-padding
trick `x = ReLU x - ReLU (-x)` (any exactly-k' network can be padded to exactly
k'+1), but that lemma is not proved anywhere (per BRIDGE_SPEC, nobody has proved it),
and proving it here would additionally require matching Agent072's `IsReLUNet`
recursion against Agent073's differently-shaped `IsReLURep` recursion. Both pieces
together are too large for this bridge, so this is left as an honest `sorry`. -/
theorem relun (n k : ℕ) : Agent072.ReLUn n k = Agent073.ReLUn n k := by
  sorry

/- `statement`: the RHS (Agent073's internal instance of Theorem 2) is in fact false
by essentially the same argument as `cpwl_ne` — Agent073.CPWL n is only the globally
affine functions, while Agent073.ReLUn n (depthBound n) contains genuinely kinked
functions once depthBound n ≥ 1 (true for all n ≥ 3). But the LHS is Agent072's
internal instance of Theorem 2, which (given Agent072's faithful CPWL and the
"at most k layers" ReLUn reading) is essentially *the paper's actual theorem*, whose
proof is far out of scope here. Since we cannot decide the LHS, we cannot decide the
iff either way, so this is left as an honest `sorry`. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent072.CPWL n = Agent072.ReLUn n (Agent072.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent073.CPWL n = Agent073.ReLUn n (Agent073.depthBound n)) := by
  sorry

end Bridge_072_073

namespace Bridge_034_035

/-- `depthBound` is literally the same closed-form expression
`⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1` in both files (`⌈·⌉₊` is notation for `Nat.ceil`),
so the two definitions are definitionally equal. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) :
    Agent034.depthBound n = Agent035.depthBound n := rfl

/-- Witness exposing that Agent034's polyhedral-subdivision `CPWL` and Agent035's
local-agreement `CPWL` are genuinely different predicates: `x ↦ max 0 (x 0)` is
piecewise affine on a polyhedral cover of `ℝ` but does *not* locally agree with a
single affine function in any neighbourhood of `0`. -/
def wit : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

private lemma wit_mem_034 : wit ∈ Agent034.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2,
    ![{x : Fin 1 → ℝ | x 0 ≤ 0}, {x : Fin 1 → ℝ | 0 ≤ x 0}],
    ![fun _ : Fin 1 → ℝ => (0 : ℝ), fun x : Fin 1 → ℝ => x 0], ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    rcases le_total (x 0) 0 with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  · intro i
    fin_cases i
    · refine ⟨1, ![fun _ : Fin 1 => (1 : ℝ)], ![(0 : ℝ)], ?_⟩
      ext x
      simp only [Set.mem_setOf_eq, Fin.forall_fin_one, Matrix.cons_val_zero]
      constructor <;> intro hx <;> linarith
    · refine ⟨1, ![fun _ : Fin 1 => (-1 : ℝ)], ![(0 : ℝ)], ?_⟩
      ext x
      simp only [Set.mem_setOf_eq, Fin.forall_fin_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons]
      constructor <;> intro hx <;> linarith
  · intro i
    fin_cases i
    · exact ⟨fun _ => (0 : ℝ), 0, fun x => by simp [Fin.sum_univ_one]⟩
    · exact ⟨fun _ => (1 : ℝ), 0, fun x => by simp [Fin.sum_univ_one]⟩
  · intro i x hx
    fin_cases i
    · exact max_eq_left hx
    · exact max_eq_right hx

private lemma wit_not_mem_035 : wit ∉ Agent035.CPWL 1 := by
  rintro ⟨-, m, g, hg⟩
  obtain ⟨i, hi⟩ := hg (fun _ => (0 : ℝ))
  have hcont : Continuous (fun t : ℝ => (fun _ : Fin 1 => t)) :=
    continuous_pi fun _ => continuous_id
  have htend : Filter.Tendsto (fun t : ℝ => (fun _ : Fin 1 => t))
      (nhds 0) (nhds (fun _ : Fin 1 => (0 : ℝ))) := hcont.tendsto 0
  have hev : ∀ᶠ t in nhds (0 : ℝ),
      wit (fun _ => t) = (g i).apply (fun _ => t) 0 := htend.eventually hi
  obtain ⟨ε, hε, H⟩ := Metric.eventually_nhds_iff.mp hev
  have happly : ∀ t : ℝ, (g i).apply (fun _ : Fin 1 => t) 0
      = (g i).A 0 0 * t + (g i).bias 0 := by
    intro t
    simp [Agent035.AffineMap'.apply, Matrix.mulVec, dotProduct, Fin.sum_univ_one,
      Pi.add_apply]
  have hb : (g i).bias 0 = 0 := by
    have hraw := H (show dist (0 : ℝ) 0 < ε by rw [dist_self]; exact hε)
    rw [happly] at hraw
    simpa [wit, max_self, mul_zero, zero_add] using hraw.symm
  have hp : (g i).A 0 0 * (ε / 2) = ε / 2 := by
    have hraw := H (show dist (ε / 2 : ℝ) 0 < ε by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by linarith : (0:ℝ) ≤ ε / 2)]; linarith)
    rw [happly] at hraw
    simpa [wit, hb, max_eq_right (by linarith : (0:ℝ) ≤ ε / 2), add_zero] using hraw.symm
  have hn : (g i).A 0 0 * (-(ε / 2)) = 0 := by
    have hraw := H (show dist (-(ε / 2) : ℝ) 0 < ε by
      rw [Real.dist_eq, sub_zero, abs_of_nonpos (by linarith : -(ε / 2) ≤ (0:ℝ))]; linarith)
    rw [happly] at hraw
    simpa [wit, hb, max_eq_left (by linarith : -(ε / 2) ≤ (0:ℝ)), add_zero] using hraw.symm
  rw [mul_neg] at hn
  have hz : (g i).A 0 0 * (ε / 2) = 0 := by linarith
  linarith [hp, hz, hε]

theorem cpwl_ne : ∃ n, Agent034.CPWL n ≠ Agent035.CPWL n := by
  refine ⟨1, fun h => wit_not_mem_035 ?_⟩
  rw [← h]
  exact wit_mem_034

/-- Left as `sorry`: `ReLUn` in both files is "at most k hidden layers", but built on
two differently-indexed inductive net types (`ReLUNet` counts down to `zero`,
`NetLayers` counts up from `last`). Proving equality needs an explicit,
eval-preserving conversion between the two families, which is more than a quick
check can produce reliably. -/
theorem relun (n k : ℕ) : Agent034.ReLUn n k = Agent035.ReLUn n k := by
  sorry

/-- Left as `sorry`: `statement` is an iff between each agent's own (independently
`sorry`-ed) Theorem 2 restatement. `cpwl` is refuted above and `relun` is open, so
nothing proved here pins down the truth value of either side, let alone their
equivalence. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent034.CPWL n = Agent034.ReLUn n (Agent034.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent035.CPWL n = Agent035.ReLUn n (Agent035.depthBound n)) := by
  sorry

end Bridge_034_035

namespace Bridge_088_089

/-- Both agents write the depth bound as the identical expression
`⌈Real.logb 3 ((n:ℝ)-1)⌉₊ + 1` (`Nat.ceil` is exactly notation `⌈·⌉₊`), so the two
`depthBound` functions are definitionally equal. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent088.depthBound n = Agent089.depthBound n := rfl

/-- `f = fun x => max 0 (x 0)` on `ℝ^1` is a textbook two-piece CPWL function
(polyhedra `{x0 ≤ 0}`, `{x0 ≥ 0}`), so it lies in `Agent088.CPWL 1` (the honest
polyhedral-cover definition). But it is **not** locally affine at `x = 0`: any
neighbourhood of `0` contains points with `x 0 > 0` and points with `x 0 < 0`, and
no single affine `ℓ` can equal `f` throughout such a neighbourhood (three sample
points `0, ε/2, -ε/2` already force contradictory coefficients). So `f` fails
`Agent089.CPWL 1`, whose "local agreement with a fixed affine piece" definition is
too strong at kink points. Hence the two `CPWL` predicates disagree at `n = 1`. -/
theorem cpwl_ne : ∃ n, Agent088.CPWL n ≠ Agent089.CPWL n := by
  refine ⟨1, fun hEq => ?_⟩
  set f : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0) with hf
  have hfcont : Continuous f := by rw [hf]; exact continuous_const.max (continuous_apply 0)
  have hmem088 : f ∈ Agent088.CPWL 1 := by
    refine ⟨hfcont, 2, ![{x : Fin 1 → ℝ | x 0 ≤ 0}, {x : Fin 1 → ℝ | 0 ≤ x 0}], ?_, ?_, ?_⟩
    · intro j
      fin_cases j <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      · exact ⟨1, fun _ _ => 1, fun _ => 0, by
          ext x; simp only [Set.mem_setOf_eq, Fin.forall_fin_one, Fin.sum_univ_one]
          constructor <;> intro h <;> linarith⟩
      · exact ⟨1, fun _ _ => -1, fun _ => 0, by
          ext x; simp only [Set.mem_setOf_eq, Fin.forall_fin_one, Fin.sum_univ_one]
          constructor <;> intro h <;> linarith⟩
    · ext x
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      rcases le_total (x 0) 0 with h | h
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩
    · intro j
      fin_cases j <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      · exact ⟨0, 0, fun x hx => by
          simp only [Set.mem_setOf_eq] at hx
          simpa [hf, Fin.sum_univ_one] using max_eq_left hx⟩
      · exact ⟨fun _ => 1, 0, fun x hx => by
          simp only [Set.mem_setOf_eq] at hx
          simpa [hf, Fin.sum_univ_one] using max_eq_right hx⟩
  have hnmem089 : f ∉ Agent089.CPWL 1 := by
    rintro ⟨-, S, hSaff, hloc⟩
    set z : Fin 1 → ℝ := fun _ => (0 : ℝ) with hz
    obtain ⟨ℓ, hℓS, U, hU, hUeq⟩ := hloc z
    obtain ⟨a, b, hℓ⟩ := hSaff ℓ hℓS
    have hzU : z ∈ U := mem_of_mem_nhds hU
    set φ : ℝ → (Fin 1 → ℝ) := fun r _ => r with hφ
    have hφcont : Continuous φ := continuous_pi fun _ => continuous_id
    have hUφ : φ ⁻¹' U ∈ nhds (0 : ℝ) :=
      (hφcont.continuousAt (x := (0 : ℝ))).preimage_mem_nhds hU
    obtain ⟨ε, hε, hballsub⟩ := Metric.mem_nhds_iff.mp hUφ
    have hmem1 : (ε / 2 : ℝ) ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith
    have hmem2 : (-(ε / 2) : ℝ) ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_neg (by linarith)]; linarith
    have hy1U : φ (ε / 2) ∈ U := hballsub hmem1
    have hy2U : φ (-(ε / 2)) ∈ U := hballsub hmem2
    have hf0 : f z = 0 := by simp [hf, hz]
    have hf1 : f (φ (ε / 2)) = ε / 2 := by
      simp only [hf, hφ]; exact max_eq_right (by linarith)
    have hf2 : f (φ (-(ε / 2))) = 0 := by
      simp only [hf, hφ]; exact max_eq_left (by linarith)
    have hl0 : ℓ z = b := by rw [hℓ z]; simp [hz, Fin.sum_univ_one]
    have hl1 : ℓ (φ (ε / 2)) = a 0 * (ε / 2) + b := by
      rw [hℓ (φ (ε / 2))]; simp [hφ, Fin.sum_univ_one]
    have hl2 : ℓ (φ (-(ε / 2))) = -(a 0 * (ε / 2)) + b := by
      rw [hℓ (φ (-(ε / 2)))]; simp [hφ, Fin.sum_univ_one, mul_neg]
    have e0 : f z = ℓ z := hUeq z hzU
    have e1 : f (φ (ε / 2)) = ℓ (φ (ε / 2)) := hUeq _ hy1U
    have e2 : f (φ (-(ε / 2))) = ℓ (φ (-(ε / 2))) := hUeq _ hy2U
    rw [hf0, hl0] at e0
    rw [hf1, hl1] at e1
    rw [hf2, hl2] at e2
    linarith [e0, e1, e2, hε]
  rw [hEq] at hmem088
  exact hnmem089 hmem088

/-- Both `ReLUn`s are "at most `k`" wrappers around a recursively-defined "exactly
`k`" predicate, but the two base predicates encode the base-case affine map
differently (088: an explicit vector `a : Fin n → ℝ` and scalar `b`; 089: a genuine
`1×n` matrix via `AffineFun n 1`), and equate them requires an induction on `k`
converting between the two affine-map representations at every layer. That
conversion lemma is not proved by either agent and is more than a quick win to
supply here, so this is left open. -/
theorem relun (n k : ℕ) : Agent088.ReLUn n k = Agent089.ReLUn n k := by
  sorry

/-- `statement` compares the two agents' *instances* of Theorem 2 for their own
(non-equal, per `cpwl_ne`) notions of `CPWL`/`ReLUn`/`depthBound`; since both
agents left `theorem2` as `sorry`, and `cpwl`/`relun` are not fully bridged above,
there is no honest route to either direction of this `Iff` without assuming what
is not yet proved. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent088.CPWL n = Agent088.ReLUn n (Agent088.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent089.CPWL n = Agent089.ReLUn n (Agent089.depthBound n)) := by
  sorry

end Bridge_088_089

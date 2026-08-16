namespace Bridge_098_099

/-- Test function for the CPWL refutation: the 1-D ReLU kink. -/
private def relu1 : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

/-- Embeds ℝ into `Fin 1 → ℝ` as a constant vector, used to reduce the
`nhds`-in-`Fin 1 → ℝ` argument below to ordinary real analysis. -/
private def pt (t : ℝ) : Fin 1 → ℝ := fun _ => t

/-- Both files write `depthBound n` as `Nat.ceil (Real.logb 3 ((n:ℝ) - 1)) + 1`
(`⌈·⌉₊` is notation for `Nat.ceil`), so the two definitions are syntactically equal. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent098.depthBound n = Agent099.depthBound n := rfl

/-- Agent098's `CPWL` is the polyhedral-subdivision reading: `relu1` belongs to it via
the two half-spaces `{x₀ ≥ 0}`/`{x₀ ≤ 0}`. Agent099's `CPWL` is the local-agreement
reading: `f` must coincide with ONE fixed affine function on a full two-sided
neighbourhood of every point. At `x = 0`, `relu1` agrees with `id` for `x₀ > 0` and
with `0` for `x₀ < 0`, and no single affine function can match both sides on a
two-sided neighbourhood, so `relu1 ∉ Agent099.CPWL 1`. Hence the two `CPWL`s differ
already at `n = 1`. -/
theorem cpwl_ne : ∃ n, Agent098.CPWL n ≠ Agent099.CPWL n := by
  have hp0 : Agent098.IsPolyhedron 1 {x : Fin 1 → ℝ | 0 ≤ x 0} :=
    ⟨1, fun _ _ => -1, fun _ => 0, Set.ext fun x => by
      constructor
      · intro h i; simp only [Fin.sum_univ_one]; linarith
      · intro h; have h0 := h 0; simp only [Fin.sum_univ_one] at h0; linarith⟩
  have hp1 : Agent098.IsPolyhedron 1 {x : Fin 1 → ℝ | x 0 ≤ 0} :=
    ⟨1, fun _ _ => 1, fun _ => 0, Set.ext fun x => by
      constructor
      · intro h i; simp only [Fin.sum_univ_one]; linarith
      · intro h; have h0 := h 0; simp only [Fin.sum_univ_one] at h0; linarith⟩
  have hmem098 : relu1 ∈ Agent098.CPWL 1 := by
    refine ⟨?_, 2,
      fun i => if i = 0 then {x : Fin 1 → ℝ | 0 ≤ x 0} else {x : Fin 1 → ℝ | x 0 ≤ 0},
      fun i => if i = 0 then (⟨fun _ => 1, 0⟩ : Agent098.AffineFn 1) else ⟨fun _ => 0, 0⟩,
      ?_, ?_, ?_⟩
    · show Continuous fun x => max 0 (x 0)
      exact continuous_const.max (continuous_apply 0)
    · intro i; by_cases hi : i = 0
      · rw [if_pos hi]; exact hp0
      · rw [if_neg hi]; exact hp1
    · refine Set.ext fun x => ⟨fun _ => ?_, fun _ => Set.mem_univ x⟩
      rcases le_total 0 (x 0) with h0 | h0
      · exact Set.mem_iUnion.mpr ⟨0, by rw [if_pos rfl]; exact h0⟩
      · exact Set.mem_iUnion.mpr ⟨1, by rw [if_neg (by decide)]; exact h0⟩
    · intro i x hx; by_cases hi : i = 0
      · rw [if_pos hi] at hx ⊢
        have hx' : (0:ℝ) ≤ x 0 := hx
        have he : Agent098.AffineFn.eval (⟨fun _ => (1:ℝ), 0⟩ : Agent098.AffineFn 1) x = x 0 := by
          simp [Agent098.AffineFn.eval, Fin.sum_univ_one]
        rw [he]; show max 0 (x 0) = x 0; exact max_eq_right hx'
      · rw [if_neg hi] at hx ⊢
        have hx' : x 0 ≤ (0:ℝ) := hx
        have he : Agent098.AffineFn.eval (⟨fun _ => (0:ℝ), 0⟩ : Agent098.AffineFn 1) x = 0 := by
          simp [Agent098.AffineFn.eval, Fin.sum_univ_one]
        rw [he]; show max 0 (x 0) = 0; exact max_eq_left hx'
  have hmem099 : relu1 ∉ Agent099.CPWL 1 := by
    rintro ⟨-, m, g, hg, hloc⟩
    obtain ⟨i, hev⟩ := hloc (0 : Fin 1 → ℝ)
    obtain ⟨a, b, hgi⟩ := hg i
    have hφ : Continuous pt := continuous_pi fun _ => continuous_id
    have hten : Filter.Tendsto pt (nhds (0:ℝ)) (nhds (0 : Fin 1 → ℝ)) := by
      have hpt0 : pt 0 = (0 : Fin 1 → ℝ) := rfl
      rw [← hpt0]; exact hφ.tendsto 0
    have hev' : ∀ᶠ t in nhds (0:ℝ), relu1 (pt t) = g i (pt t) := hten.eventually hev
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev'
    have key : ∀ t : ℝ, dist t 0 < ε → max 0 t = a 0 * t + b := by
      intro t ht
      have h := hball ht
      have h1 : relu1 (pt t) = max 0 t := rfl
      have h2 : g i (pt t) = a 0 * t + b := by rw [hgi]; simp [pt, Fin.sum_univ_one]
      rw [h1, h2] at h; exact h
    have hε2 : (0:ℝ) < ε / 2 := by linarith
    have hε3 : (0:ℝ) < ε / 3 := by linarith
    have e1 := key (ε/2) (by rw [Real.dist_eq, sub_zero, abs_of_pos hε2]; linarith)
    have e2 := key (ε/3) (by rw [Real.dist_eq, sub_zero, abs_of_pos hε3]; linarith)
    have e3 := key (-(ε/2))
      (by rw [Real.dist_eq, sub_zero, abs_of_neg (show -(ε/2) < 0 by linarith)]; linarith)
    rw [max_eq_right hε2.le] at e1
    rw [max_eq_right hε3.le] at e2
    rw [max_eq_left (show -(ε/2) ≤ (0:ℝ) by linarith)] at e3
    have hb : b = 0 := by linear_combination 2*e1 - 3*e2
    rw [hb, add_zero] at e1
    have ha0 : (1:ℝ) = a 0 := by
      have e1' : (1:ℝ) * (ε/2) = a 0 * (ε/2) := by rw [one_mul]; exact e1
      exact mul_right_cancel₀ (ne_of_gt hε2) e1'
    rw [hb, add_zero, ← ha0, one_mul] at e3
    linarith [e3, hε]
  exact ⟨1, fun h => hmem099 (h ▸ hmem098)⟩

/-- Left as `sorry`: bridging "at most k, matrix-`mulVec`-based" (Agent098) with
"at most k, sum-based `AffMap`" (Agent099) representability needs an induction
translating `AffineTransform`/`ReLURepExact` into `AffMap`/`ReLUNet` layer-by-layer
(the underlying formulas agree, but the induction was not attempted within budget). -/
theorem relun (n k : ℕ) : Agent098.ReLUn n k = Agent099.ReLUn n k := by
  sorry

/-- Left as `sorry`: `statement` packages `theorem2` for both agents, which we are
instructed not to invoke; independently deriving it needs the `cpwl`/`relun` bridge for
all `n`, but `cpwl` genuinely differs (see `cpwl_ne`) and `relun` is unproved above, so
neither direction of the `Iff` is available from what was established here. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent098.CPWL n = Agent098.ReLUn n (Agent098.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent099.CPWL n = Agent099.ReLUn n (Agent099.depthBound n)) := by
  sorry

end Bridge_098_099

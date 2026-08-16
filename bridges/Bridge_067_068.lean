namespace Bridge_067_068

open Filter Topology

/-! ## Depth bound: identical formulas -/

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent067.depthBound n = Agent068.depthBound n := by
  unfold Agent067.depthBound Agent068.depthBound
  rfl

/-! ## CPWL: `Agent067` uses local affine agreement, `Agent068` uses a global convex
polyhedral subdivision. These are genuinely different predicates: `x ↦ max 0 (x 0)` is a
textbook piecewise-linear function under the polyhedral reading, but it is *not* locally
affine at `0` (no single affine function agrees with it on a whole neighbourhood of `0`,
since it bends there). We exhibit this witness explicitly. -/

/-- The one-dimensional ReLU function, used to separate the two `CPWL` encodings. -/
noncomputable def f0 : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

theorem f0_continuous : Continuous f0 :=
  continuous_const.max (continuous_apply 0)

/-- `f0` lies in `Agent068.CPWL 1`: two convex half-line pieces `{x0 ≤ 0}` (affine piece `0`)
and `{0 ≤ x0}` (affine piece `x0`) cover `ℝ` and match `f0` on each. -/
theorem f0_mem_068 : f0 ∈ Agent068.CPWL 1 := by
  refine ⟨f0_continuous, 2,
    fun i : Fin 2 => if i = 0 then (fun _ : Fin 1 → ℝ => (0 : ℝ)) else (fun x : Fin 1 → ℝ => x 0),
    fun i : Fin 2 => if i = 0 then {x : Fin 1 → ℝ | x 0 ≤ 0} else {x : Fin 1 → ℝ | 0 ≤ x 0},
    ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = 0
    · rw [if_pos hi]; exact ⟨fun _ => 0, 0, fun x => by simp⟩
    · rw [if_neg hi]
      refine ⟨fun _ => 1, 0, fun x => ?_⟩
      simp [Fin.sum_univ_one]
  · intro i
    by_cases hi : i = 0
    · rw [if_pos hi]
      intro x hx y hy a b ha hb hab
      simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
      nlinarith
    · rw [if_neg hi]
      intro x hx y hy a b ha hb hab
      simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
      nlinarith
  · apply Set.eq_univ_of_forall
    intro x
    rcases le_or_lt (x 0) 0 with h | h
    · exact Set.mem_iUnion.mpr ⟨0, by rw [if_pos rfl]; exact h⟩
    · have h1 : (1 : Fin 2) ≠ 0 := by decide
      exact Set.mem_iUnion.mpr ⟨1, by rw [if_neg h1]; exact h.le⟩
  · intro i x hx
    by_cases hi : i = 0
    · rw [if_pos hi] at hx ⊢
      show f0 x = 0
      exact max_eq_left hx
    · rw [if_neg hi] at hx ⊢
      show f0 x = x 0
      exact max_eq_right hx

/-- `f0` does **not** lie in `Agent067.CPWL 1`: if it did, some single affine function would
agree with `f0` on a whole neighbourhood of `0`, which is false since `f0` bends at `0`. -/
theorem f0_not_mem_067 : f0 ∉ Agent067.CPWL 1 := by
  rintro ⟨-, m, w, b, hloc⟩
  obtain ⟨i, hev⟩ := hloc (fun _ => 0)
  have hev' : ∀ᶠ y in nhds (fun _ : Fin 1 => (0 : ℝ)), f0 y = w i 0 * y 0 + b i := by
    refine hev.mono ?_
    intro y hy
    rwa [Fin.sum_univ_one] at hy
  have g_cont : Continuous (fun t : ℝ => (fun _ : Fin 1 => t)) :=
    continuous_pi (fun _ => continuous_id)
  have g_tendsto :
      Filter.Tendsto (fun t : ℝ => (fun _ : Fin 1 => t)) (nhds (0 : ℝ))
        (nhds (fun _ : Fin 1 => (0 : ℝ))) :=
    g_cont.tendsto 0
  have key : ∀ᶠ t in nhds (0 : ℝ), max 0 t = w i 0 * t + b i := by
    refine (g_tendsto.eventually hev').mono ?_
    intro t ht
    simpa [f0] using ht
  obtain ⟨ε, hε, hall⟩ := Metric.eventually_nhds_iff.mp key
  have hlt0 : dist (0 : ℝ) 0 < ε := by rw [dist_self]; exact hε
  have hltp : dist (ε / 2 : ℝ) 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by linarith)]; linarith
  have hltn : dist (-(ε / 2) : ℝ) 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_nonpos (by linarith)]; linarith
  have e0 : max (0 : ℝ) 0 = w i 0 * 0 + b i := hall hlt0
  have ep : max (0 : ℝ) (ε / 2) = w i 0 * (ε / 2) + b i := hall hltp
  have en : max (0 : ℝ) (-(ε / 2)) = w i 0 * (-(ε / 2)) + b i := hall hltn
  rw [max_self] at e0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ ε / 2)] at ep
  rw [max_eq_left (by linarith : (-(ε / 2) : ℝ) ≤ 0)] at en
  rw [mul_zero] at e0
  rw [mul_neg] at en
  linarith

theorem cpwl_ne : ∃ n, Agent067.CPWL n ≠ Agent068.CPWL n := by
  refine ⟨1, fun h => f0_not_mem_067 ?_⟩
  rw [h]
  exact f0_mem_068

/-! ## ReLUn: `Agent067` uses "exactly `k` hidden layers" while `Agent068` uses "at most `k`"
(a union over `k' ≤ k`). Proving these sets equal for all `n k` needs (a) a general padding
lemma that "exactly `k'`" networks embed into "exactly `k`" networks for `k' ≤ k`, via the
identity trick `relu x - relu (-x) = x` inserted as a dummy layer — stated as true but left
unproved in `Agent067`'s own docstring — and (b) bridging the two different affine-map
encodings (`Fin`-indexed matrices vs. `ℕ`-indexed matrices restricted to the first `inDim`
coordinates). Both are real, nontrivial constructions outside the scope of this bridge. -/
theorem relun (n k : ℕ) : Agent067.ReLUn n k = Agent068.ReLUn n k := by
  sorry

/-! ## Statement: an `Iff` between the two agents' own (still-`sorry`'d) renderings of
Theorem 2. Since `cpwl_ne` shows the `CPWL` predicates genuinely differ, this is not something
`cpwl`/`relun`/`depth` could bridge directly even if fully proved; each side would need Theorem
2 itself established in that agent's own encoding, which is the mathematical content of the
whole paper and out of scope here. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent067.CPWL n = Agent067.ReLUn n (Agent067.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent068.CPWL n = Agent068.ReLUn n (Agent068.depthBound n)) := by
  sorry

end Bridge_067_068

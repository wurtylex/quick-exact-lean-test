/-!
# Star comparison: `Agent080` vs `Ref`

`Agent080` belongs to the **local-agreement (`nhds`) `CPWL`** family: its `CPWL n`
asks for a *finite* family of affine functions such that every point has a whole
neighbourhood on which `f` coincides with one of them.  On connected `ℝⁿ` this
forces `f` to be globally affine, so it is strictly stronger than genuine
piecewise linearity.  Hence `cpwl` is **false** (`cpwl_ne`), and in fact the
agent's own Theorem 2 is false (`agent_side_false`).

`depthBound` is literally the reference definition (`rfl`).  `ReLUn` is "exactly
`k` hidden layers" against the reference's "at most `k`"; these denote the same
set, but only through the padding identity `x = relu x - relu (-x)`, which is a
real theorem — left as an honest `sorry`.
-/

namespace Star_080

/-- The curve `t ↦ t • eᵢ` in `ℝⁿ`, used to reduce a neighbourhood-agreement
statement in `ℝⁿ` to one in `ℝ`. -/
private def coordCurve (n : ℕ) (i : Fin n) : ℝ → (Fin n → ℝ) :=
  fun t j => if j = i then t else 0

private lemma coordCurve_continuous (n : ℕ) (i : Fin n) :
    Continuous (coordCurve n i) := by
  refine continuous_pi fun j => ?_
  by_cases hj : j = i
  · simp only [coordCurve, if_pos hj]; exact continuous_id
  · simp only [coordCurve, if_neg hj]; exact continuous_const

private lemma coordCurve_zero (n : ℕ) (i : Fin n) : coordCurve n i 0 = 0 := by
  funext j; simp [coordCurve]

/-- The kink argument: `x ↦ max 0 (xᵢ)` is not locally affine at the origin, so it
fails the agent's neighbourhood-agreement definition of `CPWL`. -/
private lemma relu_coord_not_mem (n : ℕ) (i : Fin n) :
    (fun x : Fin n → ℝ => max 0 (x i)) ∉ Agent080.CPWL n := by
  intro hmem
  obtain ⟨-, ι, -, g, hg, hloc⟩ := hmem
  obtain ⟨i₀, hev⟩ := hloc 0
  obtain ⟨T, hT⟩ := hg i₀
  have htend : Filter.Tendsto (coordCurve n i) (nhds 0) (nhds 0) := by
    have h := (coordCurve_continuous n i).tendsto 0
    rwa [coordCurve_zero] at h
  have key : ∀ᶠ t : ℝ in nhds 0, max 0 t = T.A 0 i * t + T.c 0 := by
    filter_upwards [hev.comp_tendsto htend] with t ht
    have h1 : coordCurve n i t i = t := by simp [coordCurve]
    have h2 : (∑ j, T.A 0 j * coordCurve n i t j) = T.A 0 i * t := by
      rw [Finset.sum_eq_single i]
      · rw [h1]
      · intro b _ hb; simp [coordCurve, hb]
      · intro hb; exact absurd (Finset.mem_univ i) hb
    simp only [Function.comp_apply, hT, Agent080.AffineMap.eval] at ht
    rw [h1, h2] at ht
    exact ht
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 key
  have hd : ∀ t : ℝ, |t| < ε → max 0 t = T.A 0 i * t + T.c 0 := fun t ht =>
    hball (by rwa [Real.dist_eq, sub_zero])
  have h0 := hd 0 (by simpa using hε)
  have hp := hd (ε / 2) (by rw [abs_of_pos (by linarith : (0:ℝ) < ε / 2)]; linarith)
  have hm := hd (-(ε / 2)) (by
    rw [abs_neg, abs_of_pos (by linarith : (0:ℝ) < ε / 2)]; linarith)
  rw [max_self, mul_zero, zero_add] at h0
  rw [max_eq_right (by linarith : (0:ℝ) ≤ ε / 2)] at hp
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0:ℝ))] at hm
  linarith

private lemma halfspace_poly {n : ℕ} {S : Set (Fin n → ℝ)} (h : Ref.IsHalfspace n S) :
    Ref.IsPolyhedron n S :=
  ⟨1, fun _ => S, fun _ => h,
    Set.ext fun x => ⟨fun hx => Set.mem_iInter.2 fun _ => hx, fun hx => Set.mem_iInter.1 hx 0⟩⟩

/-- The same function *is* in the reference `CPWL`, via the two halfspaces
`{x₀ ≤ 0}` and `{-x₀ ≤ 0}`. -/
private lemma relu_coord_mem_ref : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Ref.CPWL 1 := by
  refine ⟨Continuous.max continuous_const (continuous_apply 0), 2,
    ![{x : Fin 1 → ℝ | (∑ i, (1:ℝ) * x i) ≤ 0}, {x : Fin 1 → ℝ | (∑ i, (-1:ℝ) * x i) ≤ 0}],
    ![fun _ => (0:ℝ), fun x => x 0], ?_, ?_, ?_, ?_⟩
  · refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · simp only [Matrix.cons_val_zero]; exact halfspace_poly ⟨fun _ => 1, 0, rfl⟩
    · simp only [Matrix.cons_val_one, Matrix.head_cons]
      exact halfspace_poly ⟨fun _ => -1, 0, rfl⟩
  · refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · exact ⟨0, 0, by simp⟩
    · exact ⟨fun _ => 1, 0, by simp⟩
  · rw [Set.eq_univ_iff_forall]
    intro x
    rcases le_total (x 0) 0 with h | h
    · exact Set.mem_iUnion.2 ⟨0, by simpa using h⟩
    · exact Set.mem_iUnion.2 ⟨1, by simpa using h⟩
  · refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · intro x hx
      have h : x 0 ≤ 0 := by simpa using hx
      simp [max_eq_left h]
    · intro x hx
      have h : (0:ℝ) ≤ x 0 := by simpa using hx
      simp [max_eq_right h]

/-- `Agent080.CPWL` is not `Ref.CPWL`: `max 0 x₀` separates them at `n = 1`. -/
theorem cpwl_ne : ∃ n, Agent080.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => relu_coord_not_mem 1 0 ?_⟩
  rw [h]
  exact relu_coord_mem_ref

private lemma depthBound_three : Agent080.depthBound 3 = 2 := by
  have hb : (3:ℝ) = ((3:ℕ):ℝ) := by norm_num
  have h2 : (((3:ℕ):ℝ) - 1) = ((2:ℕ):ℝ) := by norm_num
  have hc : ⌈Real.logb 3 (((3:ℕ):ℝ) - 1)⌉₊ = 1 := by
    rw [h2, hb, Real.natCeil_logb_natCast]
    first | norm_num | decide | rfl
  unfold Agent080.depthBound
  omega

/-- `max 0 x₀` is computed by a network with **exactly** two hidden layers on `ℝ³`
(the second layer is a no-op because `relu` is idempotent). -/
private lemma relu_coord_mem_relun : (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent080.ReLUn 3 2 := by
  show Agent080.IsReLUComputable 3 2 (fun x : Fin 3 → ℝ => max 0 (x 0))
  have h0 : Agent080.IsReLUComputable 1 0 (fun z : Fin 1 → ℝ => z 0) := by
    refine ⟨⟨fun _ _ => 1, fun _ => 0⟩, ?_⟩
    funext z; simp [Agent080.AffineMap.eval]
  have h1 : Agent080.IsReLUComputable 1 1 (fun y : Fin 1 → ℝ => max 0 (y 0)) := by
    refine ⟨1, ⟨fun _ _ => 1, fun _ => 0⟩, (fun z : Fin 1 → ℝ => z 0), h0, ?_⟩
    funext y; simp [Agent080.reluVec, Agent080.relu, Agent080.AffineMap.eval]
  refine ⟨1, ⟨fun _ j => if j = 0 then 1 else 0, fun _ => 0⟩,
    (fun y : Fin 1 → ℝ => max 0 (y 0)), h1, ?_⟩
  funext x
  have hs : (∑ j : Fin 3, (if j = 0 then (1:ℝ) else 0) * x j) = x 0 := by
    simp [Fin.sum_univ_three]
  simp only [Agent080.reluVec, Agent080.relu, Agent080.AffineMap.eval, hs, add_zero]
  exact (max_eq_right (le_max_left 0 (x 0))).symm

/-- The agent's Theorem 2 is outright false: at `n = 3`, `max 0 x₀` lies in
`ReLUn 3 (depthBound 3)` but not in the agent's `CPWL 3`. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent080.CPWL n = Agent080.ReLUn n (Agent080.depthBound n)) := by
  intro h
  have h3 := h 3 le_rfl
  rw [depthBound_three] at h3
  refine relu_coord_not_mem 3 0 ?_
  rw [h3]
  exact relu_coord_mem_relun

/-- Agent: exactly `k` hidden layers; reference: at most `k`.  Equal as sets, but
only via the padding identity `x = relu x - relu (-x)`, which is a genuine
theorem and out of budget here. -/
theorem relun (n k : ℕ) : Agent080.ReLUn n k = Ref.ReLUn n k := sorry

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent080.depthBound n = Ref.depthBound n := rfl

/-- By `agent_side_false` the left side is `False`, so this iff is equivalent to the
negation of the reference Theorem 2 — presumably false, but refuting it would
require *proving* `Ref.theorem2`, which is itself `sorry`-ed. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent080.CPWL n = Agent080.ReLUn n (Agent080.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_080

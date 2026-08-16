/-!
# Star comparison: `Agent085` vs `Ref`

`Agent085` defines `CPWL` by *local (neighbourhood) agreement* with a finite family of
affine functions.  That condition is strictly stronger than piecewise linearity on the
connected space `ℝⁿ`, so `Agent085.CPWL ≠ Ref.CPWL` and moreover `Agent085`'s Theorem 2 is
outright false.  Both facts are proved below (`cpwl_ne`, `agent_side_false`).

`depthBound` agrees definitionally.  `ReLUn` is "exactly `k`" vs "at most `k`"; these denote
the same set but only via the padding identity, which is left as an honest `sorry`.
-/

namespace Star_085

/-! ### The kink obstruction -/

/-- `max 0 ·` is not affine on any neighbourhood of `0`. -/
private lemma no_affine_near_zero (a b : ℝ) :
    ¬ ∀ᶠ t in nhds (0 : ℝ), max 0 t = a * t + b := by
  intro hev
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, h⟩ := hev
  have h0 := h (y := (0 : ℝ)) (by simpa using hε)
  rw [max_self, mul_zero, zero_add] at h0
  have hp := h (y := ε / 2) (by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
  have hn := h (y := -(ε / 2)) (by
    rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by linarith)]; linarith)
  rw [max_eq_right (by linarith : (0:ℝ) ≤ ε / 2)] at hp
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0:ℝ))] at hn
  have hcancel : a * (ε / 2) + a * (-(ε / 2)) = 0 := by ring
  linarith

/-- Transport of the kink obstruction along a line through the origin: no function that
restricts to `max 0 ·` on such a line can lie in `Agent085.CPWL n`. -/
private lemma not_mem_agent_cpwl {n : ℕ} (φ : ℝ → (Fin n → ℝ)) (hφ : Continuous φ)
    (hφ0 : φ 0 = 0) (f : (Fin n → ℝ) → ℝ) (hf : ∀ t, f (φ t) = max 0 t)
    (hlin : ∀ w : Fin n → ℝ, ∃ a : ℝ, ∀ t, (∑ j, w j * (φ t) j) = a * t) :
    f ∉ Agent085.CPWL n := by
  intro hmem
  obtain ⟨-, m, w, c, h⟩ := hmem
  obtain ⟨i, hi⟩ := h 0
  obtain ⟨a, ha⟩ := hlin (w i)
  refine no_affine_near_zero a (c i) ?_
  have htend : Filter.Tendsto φ (nhds (0 : ℝ)) (nhds (0 : Fin n → ℝ)) := by
    rw [← hφ0]; exact hφ.tendsto 0
  filter_upwards [htend.eventually hi] with t ht
  rw [← hf t, ht, ha]

/-! ### `cpwl` is false -/

private lemma halfspace_poly {n : ℕ} {S : Set (Fin n → ℝ)} (hS : Ref.IsHalfspace n S) :
    Ref.IsPolyhedron n S :=
  ⟨1, fun _ => S, fun _ => hS, (Set.iInter_const _).symm⟩

private lemma sum_coeff (i : Fin 2) (x : Fin 1 → ℝ) :
    (∑ j, (if i = 0 then (1:ℝ) else -1) * x j) = if i = 0 then x 0 else -(x 0) := by
  by_cases hi : i = 0 <;> simp [hi]

/-- The witness `x ↦ max 0 (x 0)` is piecewise linear in the reference sense. -/
private lemma wit_mem_ref : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Ref.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2,
    fun i : Fin 2 => {x : Fin 1 → ℝ | (∑ j, (if i = 0 then (1:ℝ) else -1) * x j) ≤ 0},
    fun i : Fin 2 => if i = 0 then (fun _ : Fin 1 → ℝ => (0:ℝ)) else (fun x => x 0),
    fun i => halfspace_poly ⟨fun _ => (if i = 0 then (1:ℝ) else -1), 0, rfl⟩, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = 0
    · exact ⟨fun _ => 0, 0, fun x => by simp [hi]⟩
    · exact ⟨fun _ => 1, 0, fun x => by simp [hi]⟩
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true, Set.mem_setOf_eq, sum_coeff]
    rcases le_total (x 0) 0 with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  · intro i x hx
    by_cases hi : i = 0
    · have hx' : x 0 ≤ 0 := by simpa [hi] using hx
      simpa [hi] using max_eq_left hx'
    · have hx' : 0 ≤ x 0 := by simpa [hi] using hx
      simpa [hi] using max_eq_right hx'

private lemma wit_not_mem_agent : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∉ Agent085.CPWL 1 :=
  not_mem_agent_cpwl (fun t => fun _ => t) (continuous_pi fun _ => continuous_id)
    (by funext _; rfl) _ (fun _ => rfl) (fun w => ⟨w 0, fun t => by simp⟩)

/-- `Agent085.CPWL` (neighbourhood agreement) is strictly stronger than `Ref.CPWL`. -/
theorem cpwl_ne : ∃ n, Agent085.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun hEq => wit_not_mem_agent ?_⟩
  rw [hEq]; exact wit_mem_ref

/-! ### The agent's Theorem 2 is false -/

private lemma depthBound_three : Agent085.depthBound 3 = 2 := by
  have h0 : (0:ℝ) < Real.logb 3 2 := Real.logb_pos (by norm_num) (by norm_num)
  have hlog3 : (0:ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have h1 : Real.logb 3 2 ≤ 1 := by
    rw [Real.logb, div_le_one hlog3]
    gcongr <;> norm_num
  have hpos : 0 < ⌈Real.logb 3 2⌉₊ := Nat.lt_ceil.mpr (by simpa using h0)
  have hle : ⌈Real.logb 3 2⌉₊ ≤ 1 :=
    Nat.ceil_le.mpr (show Real.logb 3 2 ≤ ((1:ℕ) : ℝ) by simpa using h1)
  have hceil : ⌈Real.logb 3 2⌉₊ = 1 := by omega
  have hcast : Real.logb 3 (((3:ℕ) : ℝ) - 1) = Real.logb 3 2 := by norm_num
  simp only [Agent085.depthBound, hcast, hceil]

/-- `x ↦ max 0 (x 0)` is computed by a two-hidden-layer network on `ℝ³`. -/
private lemma computes_relu3 :
    Agent085.Computes 3 2 (fun x : Fin 3 → ℝ => max 0 (x 0)) := by
  refine ⟨1, ⟨Matrix.of fun _ j => if j = 0 then (1:ℝ) else 0, 0⟩,
    fun y : Fin 1 → ℝ => max 0 (y 0), ⟨1, ⟨Matrix.of fun _ _ => (1:ℝ), 0⟩,
      fun z : Fin 1 → ℝ => z 0, ⟨fun _ => 1, 0, fun z => by simp⟩, fun y => ?_⟩, fun x => ?_⟩
  · simp [Agent085.reluVec, Agent085.relu, Agent085.AffineMap.apply, Matrix.mulVec,
      dotProduct]
  · simp [Agent085.reluVec, Agent085.relu, Agent085.AffineMap.apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three, max_eq_right (le_max_left (0:ℝ) (x 0))]

private lemma wit3_not_mem_agent :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∉ Agent085.CPWL 3 :=
  not_mem_agent_cpwl (fun t => fun j => (if j = 0 then (1:ℝ) else 0) * t)
    (continuous_pi fun _ => continuous_const.mul continuous_id)
    (by funext j; simp) _ (fun t => by simp)
    (fun w => ⟨w 0, fun t => by simp [Fin.sum_univ_three]⟩)

/-- The statement the agent's file actually makes is false: at `n = 3` the one-sided
function `max 0 (x 0)` is a two-hidden-layer ReLU network but fails the agent's
neighbourhood-agreement `CPWL`. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent085.CPWL n = Agent085.ReLUn n (Agent085.depthBound n)) := by
  intro h
  have hmem : (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent085.ReLUn 3 (Agent085.depthBound 3) := by
    show Agent085.Computes 3 (Agent085.depthBound 3) _
    rw [depthBound_three]; exact computes_relu3
  rw [← h 3 le_rfl] at hmem
  exact wit3_not_mem_agent hmem

/-! ### The remaining obligations -/

-- `⌈·⌉₊` is notation for `Nat.ceil`, so the two depth bounds are the same term.
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent085.depthBound n = Ref.depthBound n := rfl

-- Agent says *exactly* `k` hidden layers, reference says *at most* `k`.  These sets coincide,
-- but only through the padding identity `x = relu x - relu (-x)`, which is a real theorem.
theorem relun (n k : ℕ) : Agent085.ReLUn n k = Ref.ReLUn n k := sorry

-- The left side is false (`agent_side_false`), so this iff holds iff the reference side is
-- false too — i.e. it is equivalent to refuting the genuine Theorem 2, which is out of reach
-- here (and `Ref.theorem2` is itself `sorry`-ed, so it may not be invoked).
theorem statement :
    (∀ n, 3 ≤ n → Agent085.CPWL n = Agent085.ReLUn n (Agent085.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_085

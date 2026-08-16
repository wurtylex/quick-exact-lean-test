namespace Star_038

/-!
# Comparison of `Agent038` against `Ref`

`Agent038.depthBound` is *literally* `Ref.depthBound`, so `depth` is `rfl`.

`Agent038.CPWL` is the **neighbourhood-agreement** family: a finite family of
affine functionals such that every point has an `ε`-ball on which `f` agrees
with one member.  On connected `ℝⁿ` that forces `f` to be globally affine, so it
is strictly stronger than continuous piecewise linearity: `cpwl` is **false**
(`cpwl_ne`), and the agent's Theorem 2 is false outright (`agent_side_false`).

`Agent038.ReLUn` is *exactly* `k` hidden layers versus the reference's *at most*
`k`; the two agree only through the padding identity, so `relun` is an honest
`sorry`.
-/

/-- The reference CPWL condition does hold for `x ↦ max 0 (x 0)` on `ℝ¹`:
the two halfspaces `{x 0 ≤ 0}` and `{-x 0 ≤ 0}` cover `ℝ`, and `f` is affine
on each. -/
private lemma ref_mem : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Ref.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2,
    fun i => {x : Fin 1 → ℝ | (∑ j, (if i = 0 then (1 : ℝ) else -1) * x j) ≤ 0},
    fun i => fun x => (if i = 0 then (0 : ℝ) else x 0), ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨1, fun _ => {x : Fin 1 → ℝ | (∑ j, (if i = 0 then (1 : ℝ) else -1) * x j) ≤ 0},
      fun _ => ⟨fun _ => if i = 0 then (1 : ℝ) else -1, 0, rfl⟩, (Set.iInter_const _).symm⟩
  · intro i
    refine ⟨fun _ => if i = 0 then (0 : ℝ) else 1, 0, fun x => ?_⟩
    by_cases h : i = 0 <;> simp [h, Fin.sum_univ_one]
  · refine Set.eq_univ_of_forall fun x => ?_
    rcases le_total (x 0) 0 with h | h
    · exact Set.mem_iUnion.2 ⟨0, by simpa [Fin.sum_univ_one] using h⟩
    · exact Set.mem_iUnion.2 ⟨1, by simpa [Fin.sum_univ_one] using h⟩
  · intro i x hx
    by_cases h : i = 0
    · subst h
      have hx0 : x 0 ≤ 0 := by simpa [Fin.sum_univ_one] using hx
      simp [max_eq_left hx0]
    · have hx0 : 0 ≤ x 0 := by simpa [h, Fin.sum_univ_one] using hx
      simp [h, max_eq_right hx0]

/-- The kink argument: a function that restricts to `t ↦ max 0 (C * t)` on the
diagonal (`C > 0`) cannot satisfy the agent's neighbourhood-agreement
condition, because agreement with a single affine map near `0` would force the
kink at `0` to disappear. -/
private lemma kink_not_cpwl {n : ℕ} (C : ℝ) (hC : 0 < C) (f : (Fin n → ℝ) → ℝ)
    (hf : ∀ t : ℝ, f (fun _ => t) = max 0 (C * t)) : f ∉ Agent038.CPWL n := by
  rintro ⟨-, r, a, haff, hloc⟩
  obtain ⟨i, ε, hε, hy⟩ := hloc 0
  obtain ⟨coef, b, hcoef⟩ := haff i
  have key : ∀ t : ℝ, |t| < ε → max 0 (C * t) = (∑ j, coef j) * t + b := by
    intro t ht
    have hd : dist (fun _ : Fin n => t) (0 : Fin n → ℝ) < ε :=
      (dist_pi_lt_iff hε).2 fun j => by simpa [Real.dist_eq] using ht
    have h := hy (fun _ => t) hd
    rw [hf t, hcoef] at h
    simpa [Finset.sum_mul] using h
  have hCe : (0 : ℝ) < C * (ε / 2) := mul_pos hC (by linarith)
  have h0 := key 0 (by simpa using hε)
  have h1 := key (ε / 2) (by rw [abs_of_pos (by linarith : (0 : ℝ) < ε / 2)]; linarith)
  have h2 := key (-(ε / 2)) (by
    rw [abs_neg, abs_of_pos (by linarith : (0 : ℝ) < ε / 2)]; linarith)
  rw [mul_zero, max_self] at h0
  rw [max_eq_right hCe.le] at h1
  rw [max_eq_left (by linarith : C * -(ε / 2) ≤ (0 : ℝ))] at h2
  nlinarith [h0, h1, h2, hCe]

/-- The agent's `CPWL` is **not** the reference's: `x ↦ max 0 (x 0)` on `ℝ¹`
belongs to `Ref.CPWL 1` but not to `Agent038.CPWL 1`. -/
theorem cpwl_ne : ∃ n, Agent038.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  have hf : ∀ t : ℝ, (fun x : Fin 1 → ℝ => max 0 (x 0)) (fun _ => t) = max 0 (1 * t) := by
    intro t
    simp
  have hnot : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∉ Agent038.CPWL 1 :=
    kink_not_cpwl 1 one_pos (fun x : Fin 1 → ℝ => max 0 (x 0)) hf
  have hmem : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent038.CPWL 1 :=
    (Set.ext_iff.mp h (fun x : Fin 1 → ℝ => max 0 (x 0))).mpr ref_mem
  exact hnot hmem

/-- `⌈log₃ 2⌉₊ + 1 = 2`. -/
private lemma depthBound_three : Agent038.depthBound 3 = 2 := by
  have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hle : Real.log 2 ≤ Real.log 3 := (Real.log_lt_log (by norm_num) (by norm_num)).le
  have hlogb : Real.logb 3 (((3 : ℕ) : ℝ) - 1) = Real.log 2 / Real.log 3 := by
    rw [show (((3 : ℕ) : ℝ) - 1) = 2 by norm_num]
    exact Real.log_div_log.symm
  have hpos : 0 < Real.logb 3 (((3 : ℕ) : ℝ) - 1) := by rw [hlogb]; exact div_pos h2 h3
  have hle1 : Real.logb 3 (((3 : ℕ) : ℝ) - 1) ≤ 1 := by
    rw [hlogb]; exact (div_le_one h3).2 hle
  have hceil : ⌈Real.logb 3 (((3 : ℕ) : ℝ) - 1)⌉₊ = 1 :=
    le_antisymm (Nat.ceil_le.2 (by exact_mod_cast hle1)) (Nat.ceil_pos.2 hpos)
  show ⌈Real.logb 3 (((3 : ℕ) : ℝ) - 1)⌉₊ + 1 = 2
  rw [hceil]

/-- `x ↦ max 0 (∑ j, x j)` on `ℝ³` is computed by a network with *exactly* two
hidden layers: send `x` to `∑ j, x j`, then relu twice (relu is idempotent). -/
private lemma relu_mem :
    (fun x : Fin 3 → ℝ => max 0 (∑ j, x j)) ∈ Agent038.ReLUn 3 2 := by
  show Agent038.ComputesHidden 2 3 (fun x : Fin 3 → ℝ => max 0 (∑ j, x j))
  refine ⟨1, ⟨fun _ _ => 1, fun _ => 0⟩, (fun u : Fin 1 → ℝ => max 0 (u 0)), ?_, ?_⟩
  · refine ⟨1, ⟨fun _ _ => 1, fun _ => 0⟩, (fun v : Fin 1 → ℝ => v 0),
      ⟨⟨fun _ _ => 1, fun _ => 0⟩, ?_⟩, ?_⟩
    · funext v
      show v 0 = (∑ j : Fin 1, (1 : ℝ) * v j) + 0
      simp [Fin.sum_univ_one]
    · funext u
      show max 0 (u 0) = max 0 ((∑ j : Fin 1, (1 : ℝ) * u j) + 0)
      rw [show (∑ j : Fin 1, (1 : ℝ) * u j) + 0 = u 0 by simp [Fin.sum_univ_one]]
  · funext x
    show max 0 (∑ j, x j) = max 0 (max 0 ((∑ j : Fin 3, (1 : ℝ) * x j) + 0))
    rw [show (∑ j : Fin 3, (1 : ℝ) * x j) + 0 = ∑ j, x j by simp]
    exact (max_eq_right (le_max_left 0 _)).symm

/-- The agent's own Theorem 2 is **false**: at `n = 3` the function
`x ↦ max 0 (∑ j, x j)` lies in `ReLUn 3 (depthBound 3) = ReLUn 3 2` but not in
the (too strong) `CPWL 3`. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent038.CPWL n = Agent038.ReLUn n (Agent038.depthBound n)) := by
  intro h
  refine kink_not_cpwl 3 (by norm_num) (fun x : Fin 3 → ℝ => max 0 (∑ j, x j)) (fun t => ?_) ?_
  · show max 0 (∑ _j : Fin 3, t) = max 0 (3 * t)
    rw [show (∑ _j : Fin 3, t) = 3 * t by rw [Fin.sum_univ_three]; ring]
  · rw [h 3 le_rfl, depthBound_three]
    exact relu_mem

/-- `Agent038.ReLUn` asks for *exactly* `k` hidden layers, `Ref.ReLUn` for *at
most* `k`.  The sets coincide, but only via the padding identity
`x = relu x - relu (-x)`, which is a genuine theorem; not attempted here. -/
theorem relun (n k : ℕ) : Agent038.ReLUn n k = Ref.ReLUn n k := sorry

/-- Both files define the depth bound by the same expression. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent038.depthBound n = Ref.depthBound n := rfl

/-- The left-hand side is false (`agent_side_false`), so the iff reduces to the
negation of the reference Theorem 2, which is `sorry`-ed in `Ref` and not
provable here; left honest. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent038.CPWL n = Agent038.ReLUn n (Agent038.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_038

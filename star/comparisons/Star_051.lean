namespace Star_051

/-!
# Star comparison: `Agent051` vs `Ref`

* `CPWL` does **not** agree.  `Agent051.CPWL` asks for a finite family of affine maps such
  that `f` agrees with one of them on a *neighbourhood* (`∃ ε > 0, ∀ y, dist y x < ε → …`)
  of every point.  On connected `ℝⁿ` that forces `f` to be globally affine, so it is
  strictly stronger than the reference polyhedral-cover condition: we refute `cpwl` and
  additionally prove the `Agent051` reading of Theorem 2 outright false.
* `ReLUn` : `Agent051` says **exactly** `k` hidden layers, `Ref` says **at most** `k`.
  These denote the same set, but only through the padding identity `x = relu x - relu (-x)`;
  that is a real theorem and is left as an honest `sorry`.
* `depthBound` agrees; the only difference is `((n-1 : ℕ) : ℝ)` versus `((n : ℝ) - 1)`.
-/

/-- The two spellings of `⌈log₃(n−1)⌉ + 1` agree once `1 ≤ n` makes the truncated
subtraction harmless. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent051.depthBound n = Ref.depthBound n := by
  have h1 : (1 : ℕ) ≤ n := le_trans (by norm_num) hn
  have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub h1, Nat.cast_one]
  show ⌈Real.logb 3 ((n - 1 : ℕ) : ℝ)⌉₊ + 1 = ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1
  rw [hc]

/-- `ReLUn` : "exactly `k`" versus "at most `k`".  Honest `sorry`: the two sets coincide
only via the padding identity `x = relu x - relu (−x)`, i.e. `ComputedBy n j f → ComputedBy
n (j+1) f`, which is a genuine theorem and not in budget here. -/
theorem relun (n k : ℕ) : Agent051.ReLUn n k = Ref.ReLUn n k := sorry

/-- Every halfspace is a polyhedron (intersection of the one-element family). -/
private lemma poly_of_half {n : ℕ} {S : Set (Fin n → ℝ)} (h : Ref.IsHalfspace n S) :
    Ref.IsPolyhedron n S :=
  ⟨1, fun _ => S, fun _ => h, by rw [Set.iInter_const]⟩

/-- `x ↦ max 0 (x 0)` is CPWL in the reference sense: the two halflines cover `ℝ`. -/
private lemma max_mem_ref : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Ref.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2,
    ![{x : Fin 1 → ℝ | ∑ j, (1 : ℝ) * x j ≤ 0}, {x : Fin 1 → ℝ | ∑ j, (-1 : ℝ) * x j ≤ 0}],
    ![fun _ => 0, fun x => x 0], ?_, ?_, ?_, ?_⟩
  · exact Fin.forall_fin_two.2 ⟨poly_of_half ⟨fun _ => 1, 0, rfl⟩,
      poly_of_half ⟨fun _ => -1, 0, rfl⟩⟩
  · exact Fin.forall_fin_two.2 ⟨⟨0, 0, by simp⟩, ⟨fun _ => 1, 0, by simp⟩⟩
  · refine Set.eq_univ_of_forall fun x => ?_
    rcases le_or_gt (x 0) 0 with hx | hx
    · refine Set.mem_iUnion.2 ⟨0, ?_⟩
      simp only [Matrix.cons_val_zero, Set.mem_setOf_eq, Fin.sum_univ_one, one_mul]
      linarith
    · refine Set.mem_iUnion.2 ⟨1, ?_⟩
      simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, Set.mem_setOf_eq,
        Fin.sum_univ_one, neg_mul, one_mul]
      linarith
  · refine Fin.forall_fin_two.2 ⟨fun x hx => ?_, fun x hx => ?_⟩
    · simp only [Matrix.cons_val_zero, Set.mem_setOf_eq, Fin.sum_univ_one, one_mul] at hx ⊢
      exact max_eq_left (by linarith)
    · simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, Set.mem_setOf_eq,
        Fin.sum_univ_one, neg_mul, one_mul] at hx ⊢
      exact max_eq_right (by linarith)

/-- `x ↦ max 0 (x 0)` is *not* in `Agent051.CPWL`: neighbourhood agreement with a single
affine map at the origin forces `max 0 t = a * t + b` for all small `t`, which is absurd. -/
private lemma max_not_mem (n : ℕ) :
    (fun x : Fin (n + 1) → ℝ => max 0 (x 0)) ∉ Agent051.CPWL (n + 1) := by
  rintro ⟨-, m, g, hg, h⟩
  obtain ⟨j, ε, hε, hj⟩ := h 0
  obtain ⟨a, b, hab⟩ := hg j
  have key : ∀ t : ℝ, |t| < ε → max 0 t = (∑ i, a i) * t + b := by
    intro t ht
    have hd : dist (fun _ => t : Fin (n + 1) → ℝ) 0 < ε := by
      rw [dist_pi_lt_iff hε]
      intro i
      simpa [Real.dist_eq] using ht
    have hy := hj (fun _ => t) hd
    rw [hab] at hy
    simpa [Finset.sum_mul] using hy
  have h0 := key 0 (by simpa using hε)
  have h1 := key (ε / 2) (by rw [abs_of_pos] <;> linarith)
  have h2 := key (-(ε / 2)) (by rw [abs_of_neg] <;> linarith)
  rw [max_self] at h0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ ε / 2)] at h1
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0 : ℝ))] at h2
  nlinarith [h0, h1, h2]

/-- `Agent051.CPWL` is strictly stronger than `Ref.CPWL`, so the two differ. -/
theorem cpwl_ne : ∃ n, Agent051.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  have hmem : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent051.CPWL 1 := by
    rw [h]; exact max_mem_ref
  exact max_not_mem 0 hmem

/-- Prepending one hidden layer, in the shape `Agent051.IsReLUComputable` unfolds to. -/
private lemma comp_succ {n m k : ℕ} (T : Agent051.AffMap n m) {g : (Fin m → ℝ) → ℝ}
    (hg : Agent051.IsReLUComputable m k g) {f : (Fin n → ℝ) → ℝ}
    (hf : ∀ x, f x = g fun i => Agent051.relu (T.eval x i)) :
    Agent051.IsReLUComputable n (k + 1) f :=
  ⟨m, T, g, hg, hf⟩

/-- ReLU is idempotent, which is what lets a one-layer function be padded to two layers. -/
private lemma relu_relu (t : ℝ) : max 0 (max 0 t) = max 0 t := by
  rw [← max_assoc, max_self]

/-- `⌈log₃ 2⌉₊ + 1 = 2`, so `Agent051` demands *exactly two* hidden layers at `n = 3`. -/
private lemma depthBound3 : Agent051.depthBound 3 = 2 := by
  have hp : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hlt : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have hlog : Real.logb 3 (2 : ℝ) = Real.log 2 / Real.log 3 := rfl
  have hc : ⌈Real.logb 3 (2 : ℝ)⌉₊ = 1 := by
    rw [Nat.ceil_eq_iff one_ne_zero]
    refine ⟨?_, ?_⟩
    · simpa [hlog] using div_pos (Real.log_pos (by norm_num)) hp
    · rw [Nat.cast_one, hlog, div_le_one hp]; linarith
  show ⌈Real.logb 3 ((3 - 1 : ℕ) : ℝ)⌉₊ + 1 = 2
  norm_num [hc]

/-- `max 0 (x 0)` on `ℝ³` is computed by exactly two hidden layers (the second one merely
re-applies `relu` to an already nonnegative value), hence lies in `Agent051.ReLUn`. -/
private lemma relu3_mem :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent051.ReLUn 3 (Agent051.depthBound 3) := by
  have hid : Agent051.IsReLUComputable 1 0 (fun v : Fin 1 → ℝ => v 0) :=
    ⟨⟨Matrix.of fun _ _ => (1 : ℝ), 0⟩, by
      intro v
      simp [Agent051.AffMap.eval, Matrix.mulVec, dotProduct, Fin.sum_univ_one]⟩
  have h1 : Agent051.IsReLUComputable 1 1 (fun u : Fin 1 → ℝ => max 0 (u 0)) :=
    comp_succ ⟨Matrix.of fun _ _ => (1 : ℝ), 0⟩ hid (by
      intro u
      simp [Agent051.AffMap.eval, Agent051.relu, Matrix.mulVec, dotProduct, Fin.sum_univ_one])
  have h2 : Agent051.IsReLUComputable 3 2 (fun x : Fin 3 → ℝ => max 0 (x 0)) :=
    comp_succ ⟨Matrix.of fun _ j => if j = 0 then (1 : ℝ) else 0, 0⟩ h1 (by
      intro x
      simp [Agent051.AffMap.eval, Agent051.relu, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, relu_relu])
  rw [depthBound3]
  exact h2

/-- The `Agent051` reading of Theorem 2 is outright false: its neighbourhood-agreement
`CPWL` misses `relu`, which its own `ReLUn` contains. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent051.CPWL n = Agent051.ReLUn n (Agent051.depthBound n)) := by
  intro h
  have hmem : (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent051.CPWL 3 := by
    rw [h 3 (by norm_num)]; exact relu3_mem
  exact max_not_mem 2 hmem

/-- The two readings of Theorem 2 are *not* equivalent: the left side is false
(`agent_side_false`) while the right side is the real Theorem 2, which is true.
Honest `sorry`: the right-hand side is exactly `Ref.theorem2`, which is `sorry`-ed, and
routing through it is forbidden. -/
theorem statement_ne :
    ¬ ((∀ n, 3 ≤ n → Agent051.CPWL n = Agent051.ReLUn n (Agent051.depthBound n)) ↔
      (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n))) := by
  intro hiff
  exact agent_side_false (hiff.2 (by sorry))

end Star_051

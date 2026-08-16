namespace Star_092

/-!
# Star comparison: `Agent092` vs `Ref`

* `depthBound` is *literally* the same term (`⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1`), so `depth`
  is `rfl`.
* `ReLUn` differs in reading: `Agent092` asks for **exactly** `k` hidden layers, `Ref` for
  **at most** `k`.  These denote the same set, but only through the padding identity
  `x = relu x - relu (-x)`; that is a real theorem, so `relun` is an honest `sorry`.
* `CPWL` does **not** agree: `Agent092.CPWL` asks for agreement with an affine function on
  a *neighbourhood* (`∀ᶠ y in nhds x`) of every point, which on connected `ℝⁿ` forces
  global affineness.  So `cpwl` is false and we prove `cpwl_ne`; moreover the agent's own
  reading of Theorem 2 is outright false (`agent_side_false`).
-/

/-- The `1 × 1` affine map `v ↦ v`. -/
private noncomputable def idAff : Agent092.AffineMap 1 1 :=
  (Matrix.of fun _ _ => (1 : ℝ), (0 : Fin 1 → ℝ))

/-- The affine map `ℝ³ → ℝ¹` reading off the first coordinate. -/
private noncomputable def inAff : Agent092.AffineMap 3 1 :=
  (Matrix.of fun _ j => if j = 0 then (1 : ℝ) else 0, (0 : Fin 1 → ℝ))

/-- A chain of `k` hidden layers on `ℝ¹`, each of them the identity followed by `relu`. -/
private noncomputable def idChain : (k : ℕ) → Agent092.NetworkChain 1 k
  | 0 => Agent092.NetworkChain.last idAff
  | (k + 1) => Agent092.NetworkChain.cons idAff (idChain k)

/-- On nonnegative inputs the identity chain is the identity, however deep it is:
`relu` is idempotent on `[0, ∞)`. -/
private lemma idChain_eval :
    ∀ (k : ℕ) (v : Fin 1 → ℝ), 0 ≤ v 0 → (idChain k).eval v = v 0 := by
  intro k
  induction k with
  | zero =>
    intro v _
    simp [idChain, idAff, Agent092.NetworkChain.eval, Agent092.affineEval, Matrix.mulVec,
      Matrix.of_apply, dotProduct, Fin.sum_univ_one]
  | succ k ih =>
    intro v hv
    have h1 : Agent092.reluVec (Agent092.affineEval idAff v) = fun _ => v 0 := by
      funext j
      simp [idAff, Agent092.reluVec, Agent092.relu, Agent092.affineEval, Matrix.mulVec,
        Matrix.of_apply, dotProduct, Fin.sum_univ_one, max_eq_right hv]
    show (idChain k).eval (Agent092.reluVec (Agent092.affineEval idAff v)) = v 0
    rw [h1]
    exact ih (fun _ => v 0) hv

/-- A network on `ℝ³` with `k + 1` hidden layers computing `x ↦ max 0 (x 0)`. -/
private noncomputable def reluChain (k : ℕ) : Agent092.NetworkChain 3 (k + 1) :=
  Agent092.NetworkChain.cons inAff (idChain k)

private lemma reluChain_eval (k : ℕ) (x : Fin 3 → ℝ) :
    (reluChain k).eval x = max 0 (x 0) := by
  have h1 : Agent092.reluVec (Agent092.affineEval inAff x) = fun _ => max 0 (x 0) := by
    funext j
    simp [inAff, Agent092.reluVec, Agent092.relu, Agent092.affineEval, Matrix.mulVec,
      Matrix.of_apply, dotProduct, Fin.sum_univ_three]
  show (idChain k).eval (Agent092.reluVec (Agent092.affineEval inAff x)) = max 0 (x 0)
  rw [h1]
  exact idChain_eval k (fun _ => max 0 (x 0)) (le_max_left 0 (x 0))

/-- `relu` of a coordinate lies in `Agent092.ReLUn 3 (depthBound 3)`: the depth bound is
`_ + 1`, so one genuine `relu` layer plus identity padding hits it exactly. -/
private lemma relu_mem_relun :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent092.ReLUn 3 (Agent092.depthBound 3) := by
  obtain ⟨k, hk⟩ : ∃ k, Agent092.depthBound 3 = k + 1 := ⟨_, rfl⟩
  rw [hk]
  exact ⟨reluChain k, funext fun x => (reluChain_eval k x).symm⟩

/-- `x ↦ max 0 (x 0)` is *not* in `Agent092.CPWL`: neighbourhood agreement with a single
affine function at the origin forces `max 0 t = a * t + b` for all small `t`, and testing
at `t = 0, ε/2, -ε/2` gives `b = 0`, `a = 1`, `0 = -ε/2`. -/
private lemma max_not_mem (n : ℕ) :
    (fun x : Fin (n + 1) → ℝ => max 0 (x 0)) ∉ Agent092.CPWL (n + 1) := by
  rintro ⟨-, m, g, h⟩
  obtain ⟨i, hi⟩ := h 0
  obtain ⟨ε, hε, H⟩ := Metric.eventually_nhds_iff.1 hi
  have key : ∀ t : ℝ, |t| < ε → max 0 t = (∑ j, (g i).1 0 j) * t + (g i).2 0 := by
    intro t ht
    have hd : dist (fun _ => t : Fin (n + 1) → ℝ) 0 < ε := by
      rw [dist_pi_lt_iff hε]
      intro j
      simpa [Real.dist_eq] using ht
    have hy := H hd
    simpa [Agent092.AffineFunc.eval, Agent092.affineEval, Matrix.mulVec, dotProduct,
      Finset.sum_mul] using hy
  have h0 := key 0 (by simpa using hε)
  have h1 := key (ε / 2) (by rw [abs_of_pos] <;> linarith)
  have h2 := key (-(ε / 2)) (by rw [abs_of_neg] <;> linarith)
  rw [max_self] at h0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ ε / 2)] at h1
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0 : ℝ))] at h2
  nlinarith [h0, h1, h2]

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

/-- `Agent092.CPWL` is strictly stronger than `Ref.CPWL`, so the two differ. -/
theorem cpwl_ne : ∃ n, Agent092.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  have hmem : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent092.CPWL 1 := by
    rw [h]; exact max_mem_ref
  exact max_not_mem 0 hmem

/-- Honest `sorry`: the two sets are equal, but only via the padding identity
`x = relu x - relu (-x)` turning "at most `k`" into "exactly `k`", which is a real theorem
and not a definitional unfolding. -/
theorem relun (n k : ℕ) : Agent092.ReLUn n k = Ref.ReLUn n k := by
  sorry

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent092.depthBound n = Ref.depthBound n := rfl

/-- The `Agent092` reading of Theorem 2 is outright false: its `CPWL` misses `relu`. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent092.CPWL n = Agent092.ReLUn n (Agent092.depthBound n)) := by
  intro h
  have hmem : (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent092.CPWL 3 := by
    rw [h 3 (by norm_num)]; exact relu_mem_relun
  exact max_not_mem 2 hmem

/-- The two readings are *not* equivalent: the left side is false (`agent_side_false`),
the right side is the real Theorem 2, which is true.  Honest `sorry`: discharging it needs
the true `Ref.theorem2`, which is itself `sorry`-ed, and routing through it is forbidden. -/
theorem statement_ne :
    ¬ ((∀ n, 3 ≤ n → Agent092.CPWL n = Agent092.ReLUn n (Agent092.depthBound n)) ↔
      (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n))) := by
  intro hiff
  exact agent_side_false (hiff.2 (by sorry))

end Star_092

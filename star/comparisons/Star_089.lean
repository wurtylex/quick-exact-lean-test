namespace Star_089

/-! # Comparison of `Agent089` with the reference `Ref`

* `depthBound` is literally the reference definition — `rfl`.
* `ReLUn` agrees: both take "at most `k`" hidden layers, and the two network
  predicates differ only by `AffineFun = Matrix × vector` versus the structure
  `Ref.Aff`.  Proved by induction on the depth.
* `CPWL` does **not** agree: `Agent089.CPWL` asks that `f` agree with one of
  finitely many affine maps on a *neighbourhood* of every point, which on
  connected `ℝⁿ` forces `f` to be globally affine.  Refuted (`cpwl_ne`), and the
  agent-side statement is outright false (`agent_side_false`).
-/

/-! ### The two network predicates agree -/

private lemma computed_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent089.NNComputesExact n k f ↔ Ref.ComputedBy n k f := by
  intro k
  induction k with
  | zero =>
      intro n f
      constructor
      · rintro ⟨T, hT⟩; exact ⟨⟨T.1, T.2⟩, hT⟩
      · rintro ⟨T, hT⟩; exact ⟨(T.M, T.c), hT⟩
  | succ k ih =>
      intro n f
      constructor
      · rintro ⟨m, T, g, hg, hf⟩; exact ⟨m, ⟨T.1, T.2⟩, g, (ih m g).1 hg, hf⟩
      · rintro ⟨m, T, g, hg, hf⟩; exact ⟨m, (T.M, T.c), g, (ih m g).2 hg, hf⟩

theorem relun (n k : ℕ) : Agent089.ReLUn n k = Ref.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨j, hj, h⟩; exact ⟨j, hj, (computed_iff j n f).1 h⟩
  · rintro ⟨j, hj, h⟩; exact ⟨j, hj, (computed_iff j n f).2 h⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent089.depthBound n = Ref.depthBound n := rfl

/-! ### The neighbourhood-agreement `CPWL` rejects a kink -/

/-- `x ↦ max 0 (x 0)` is not in `Agent089.CPWL`: agreement with a single affine
map on a whole neighbourhood of the origin is contradicted by the kink. -/
private lemma not_agent_cpwl (n : ℕ) [NeZero n] :
    (fun x : Fin n → ℝ => max 0 (x 0)) ∉ Agent089.CPWL n := by
  intro h
  obtain ⟨-, S, hS, hcov⟩ := h
  obtain ⟨ℓ, hℓ, U, hU, hUeq⟩ := hcov 0
  obtain ⟨a, b, hab⟩ := hS ℓ hℓ
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  have key : ∀ t : ℝ, |t| < ε → max 0 t = (∑ i, a i) * t + b := by
    intro t ht
    have hd : dist (fun _ => t : Fin n → ℝ) (0 : Fin n → ℝ) < ε := by
      rw [dist_pi_lt_iff hε]
      intro i
      simpa [Real.dist_eq] using ht
    have h := hUeq _ (hball hd)
    rw [hab] at h
    simpa [Finset.sum_mul] using h
  have h0 := key 0 (by simpa using hε)
  have h2 := key (ε / 2) (by rw [abs_of_pos (by linarith : (0:ℝ) < ε / 2)]; linarith)
  have h3 := key (-(ε / 2)) (by
    rw [abs_of_neg (by linarith : -(ε / 2) < (0:ℝ))]; linarith)
  have hmul : (∑ i, a i) * (-(ε / 2)) = -((∑ i, a i) * (ε / 2)) := by ring
  rw [max_eq_right (by linarith : (0:ℝ) ≤ ε / 2)] at h2
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0:ℝ)), hmul] at h3
  simp at h0
  linarith

/-! ### The same function *is* in the reference `CPWL` -/

private def P0 : Set (Fin 1 → ℝ) := {x | ∑ i, (1 : Fin 1 → ℝ) i * x i ≤ 0}
private def P1 : Set (Fin 1 → ℝ) := {x | ∑ i, (-1 : Fin 1 → ℝ) i * x i ≤ 0}

/-- `x ↦ max 0 (x 0)` is a reference CPWL function on `ℝ¹`: the two halflines
form a polyhedral cover on which it is affine. -/
private lemma ref_mem : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Ref.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2, ![P0, P1],
    ![fun _ => 0, fun x => x 0], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact ⟨1, fun _ => P0, fun _ => ⟨1, 0, rfl⟩, by rw [Set.iInter_const]; rfl⟩
    · exact ⟨1, fun _ => P1, fun _ => ⟨-1, 0, rfl⟩, by rw [Set.iInter_const]; rfl⟩
  · intro i
    fin_cases i
    · exact ⟨0, 0, by simp⟩
    · exact ⟨1, 0, by simp [Fin.sum_univ_one]⟩
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    rcases le_total (x 0) 0 with hx | hx
    · exact ⟨0, by simpa [P0, Fin.sum_univ_one] using hx⟩
    · exact ⟨1, by simpa [P1, Fin.sum_univ_one] using hx⟩
  · intro i x hx
    fin_cases i
    · exact max_eq_left (by simpa [P0, Fin.sum_univ_one] using hx)
    · exact max_eq_right (by simpa [P1, Fin.sum_univ_one] using hx)

/-- The two `CPWL` definitions differ: at `n = 1`, `max 0 (x 0)` lies in the
reference space but not in the agent's neighbourhood-agreement space. -/
theorem cpwl_ne : ∃ n, Agent089.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => not_agent_cpwl 1 ?_⟩
  rw [h]
  exact ref_mem

/-! ### The agent-side statement is false outright -/

private def rowE : Matrix (Fin 1) (Fin 3) ℝ := Matrix.of fun _ j => if j = 0 then (1:ℝ) else 0

/-- `x ↦ max 0 (x 0)` on `ℝ³` is a one-hidden-layer ReLU network. -/
private lemma relu3_mem :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent089.ReLUn 3 (Agent089.depthBound 3) := by
  refine ⟨1, Nat.le_add_left 1 _, 1, (rowE, (0 : Fin 1 → ℝ)), (fun y => y 0),
    ⟨(1, (0 : Fin 1 → ℝ)), ?_⟩, ?_⟩
  · intro x
    simp [Agent089.AffineFun.eval, Matrix.one_mulVec]
  · intro x
    have h : (Agent089.AffineFun.eval (rowE, (0 : Fin 1 → ℝ)) x) 0 = x 0 := by
      have h2 : (Agent089.AffineFun.eval (rowE, (0 : Fin 1 → ℝ)) x) 0
          = (∑ j, rowE 0 j * x j) + 0 := rfl
      rw [h2, Fin.sum_univ_three]
      simp [rowE]
    show max 0 (x 0) = Agent089.relu ((Agent089.AffineFun.eval (rowE, (0 : Fin 1 → ℝ)) x) 0)
    rw [h]
    rfl

/-- The agent's Theorem 2 is false: at `n = 3` the ReLU side contains
`x ↦ max 0 (x 0)` while the agent's `CPWL` does not. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent089.CPWL n = Agent089.ReLUn n (Agent089.depthBound n)) := by
  intro h
  refine not_agent_cpwl 3 ?_
  rw [h 3 le_rfl]
  exact relu3_mem

/-- The two statements are *not* equivalent: the agent side is false
(`agent_side_false`) while the reference side is the true Theorem 2.  Turning
this into a proof needs the reference direction `Ref.CPWL n ⊆ Ref.ReLUn n _`,
i.e. the actual content of the paper (`Ref.theorem2`, itself `sorry`-ed);
routing through it would prove nothing, so this stays an honest `sorry`. -/
theorem statement_ne :
    ¬ ((∀ n, 3 ≤ n → Agent089.CPWL n = Agent089.ReLUn n (Agent089.depthBound n)) ↔
      (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n))) := by
  sorry

end Star_089

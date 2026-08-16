namespace Star_035

/-!
# Comparison of `Agent035` with the reference formalization

* `depthBound` and `ReLUn` agree with the reference (both read "at most `k`
  hidden layers"), and both are proved below.
* `CPWL` does **not** agree: `Agent035.IsCPWL` asks for agreement with one
  affine map on a whole *neighbourhood* of every point, which forces global
  affineness on connected `ℝⁿ`.  So `cpwl` is false (`cpwl_ne`) and, more
  strongly, the agent's own Theorem 2 is false (`agent_side_false`).
-/

/-! ### Elementary computations with the agent's affine maps -/

private lemma apply_eq {n : ℕ} (T : Agent035.AffineMap' n 1) (x : Fin n → ℝ) :
    T.apply x 0 = (∑ j, T.A 0 j * x j) + T.bias 0 := rfl

/-- Value of an affine functional on a constant vector. -/
private lemma affVal {n : ℕ} (T : Agent035.AffineMap' n 1) (t : ℝ) :
    T.apply (fun _ => t) 0 = (∑ j, T.A 0 j) * t + T.bias 0 := by
  have h : T.apply (fun _ => t) 0 = (∑ j, T.A 0 j * t) + T.bias 0 := rfl
  rw [h, Finset.sum_mul]

/-! ### The kink argument: `Agent035.CPWL` rejects `relu` of a coordinate -/

/-- Neighbourhood-agreement with a single affine map fails at a kink. -/
private lemma relu_coord_not_cpwl {n : ℕ} (i₀ : Fin n) :
    (fun x : Fin n → ℝ => max 0 (x i₀)) ∉ Agent035.CPWL n := by
  rintro ⟨-, m, g, hg⟩
  obtain ⟨i, hi⟩ := hg 0
  rw [Metric.eventually_nhds_iff] at hi
  obtain ⟨ε, hε, h⟩ := hi
  have key : ∀ t : ℝ, |t| < ε → max 0 t = (∑ j, (g i).A 0 j) * t + (g i).bias 0 := by
    intro t ht
    have hd : dist (fun _ => t : Fin n → ℝ) (0 : Fin n → ℝ) < ε := by
      rw [dist_pi_lt_iff hε]
      intro b
      simpa [Real.dist_eq] using ht
    have h0 := h hd
    rw [affVal] at h0
    exact h0
  have e0 := key 0 (by simpa using hε)
  have e1 := key (ε / 2) (by rw [abs_of_pos (by linarith : (0:ℝ) < ε / 2)]; linarith)
  have e2 := key (-(ε / 2)) (by
    rw [abs_neg, abs_of_pos (by linarith : (0:ℝ) < ε / 2)]; linarith)
  rw [max_self] at e0
  rw [max_eq_right (by linarith : (0:ℝ) ≤ ε / 2)] at e1
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0:ℝ))] at e2
  linarith

/-! ### The same function *is* in the reference `CPWL` -/

private def Hle : Set (Fin 1 → ℝ) := {x | ∑ i, (1:ℝ) * x i ≤ 0}
private def Hge : Set (Fin 1 → ℝ) := {x | ∑ i, (-1:ℝ) * x i ≤ 0}

private lemma Hle_poly : Ref.IsPolyhedron 1 Hle :=
  ⟨1, fun _ => Hle, fun _ => ⟨fun _ => 1, 0, rfl⟩, (Set.iInter_const _).symm⟩

private lemma Hge_poly : Ref.IsPolyhedron 1 Hge :=
  ⟨1, fun _ => Hge, fun _ => ⟨fun _ => -1, 0, rfl⟩, (Set.iInter_const _).symm⟩

private lemma relu_mem_ref : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Ref.CPWL 1 := by
  show Ref.IsCPWL 1 (fun x : Fin 1 → ℝ => max 0 (x 0))
  refine ⟨continuous_const.max (continuous_apply 0), 2, ![Hle, Hge],
    ![fun _ => 0, fun x => x 0], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact Hle_poly
    · exact Hge_poly
  · intro i
    fin_cases i
    · show Ref.IsAffine (fun _ : Fin 1 → ℝ => (0:ℝ))
      exact ⟨fun _ => 0, 0, fun x => by simp⟩
    · show Ref.IsAffine (fun x : Fin 1 → ℝ => x 0)
      exact ⟨fun _ => 1, 0, fun x => by simp⟩
  · refine Set.eq_univ_of_forall fun x => ?_
    rcases le_or_gt (x 0) 0 with hx | hx
    · exact Set.mem_iUnion.2 ⟨0, show x ∈ Hle by simpa [Hle] using hx⟩
    · exact Set.mem_iUnion.2 ⟨1, show x ∈ Hge by simpa [Hge] using hx.le⟩
  · intro i
    fin_cases i
    · show ∀ x ∈ Hle, max 0 (x 0) = (0:ℝ)
      intro x hx
      exact max_eq_left (by simpa [Hle] using hx)
    · show ∀ x ∈ Hge, max 0 (x 0) = x 0
      intro x hx
      exact max_eq_right (by simpa [Hge] using hx)

/-- The agent's `CPWL` is strictly smaller than the reference one. -/
theorem cpwl_ne : ∃ n, Agent035.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => relu_coord_not_cpwl (0 : Fin 1) ?_⟩
  rw [h]
  exact relu_mem_ref

/-! ### The bonus obligation: the agent's own Theorem 2 is false -/

private lemma relu_mem_relun :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent035.ReLUn 3 (Agent035.depthBound 3) := by
  refine ⟨1, Nat.le_add_left 1 _,
    ⟨(Agent035.NetLayers.cons (b := 1) ⟨fun _ j => if j = 0 then 1 else 0, fun _ => 0⟩
      (Agent035.NetLayers.last (a := 1) ⟨fun _ _ => 1, fun _ => 0⟩) :
        Agent035.NetLayers 1 3 1), fun x => ?_⟩⟩
  simp [Agent035.NetLayers.eval, apply_eq, Agent035.reluVec, Agent035.relu,
    Fin.sum_univ_three]

/-- `fun x => relu (x 0)` is a one-hidden-layer network but is not in the agent's
`CPWL 3`, so the agent's statement of Theorem 2 is false. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent035.CPWL n = Agent035.ReLUn n (Agent035.depthBound n)) := by
  intro h
  have hm : (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent035.CPWL 3 := by
    rw [h 3 le_rfl]
    exact relu_mem_relun
  exact relu_coord_not_cpwl (0 : Fin 3) hm

/-! ### `ReLUn` and `depthBound` do agree -/

/-- The agent's inductive network type computes exactly the reference's
alternating compositions. -/
private lemma computes_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent035.NetworkComputes n k f ↔ Ref.ComputedBy n k f := by
  intro k
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨net, hnet⟩
      cases net with
      | last T => exact ⟨⟨T.A, T.bias⟩, hnet⟩
    · rintro ⟨T, hT⟩
      exact ⟨.last ⟨T.M, T.c⟩, hT⟩
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨net, hnet⟩
      cases net with
      | cons T rest =>
        exact ⟨_, ⟨T.A, T.bias⟩, fun y => rest.eval y 0,
          (ih _ _).1 ⟨rest, fun _ => rfl⟩, hnet⟩
    · rintro ⟨m, T, g, hg, hf⟩
      obtain ⟨rest, hrest⟩ := (ih m g).2 hg
      exact ⟨.cons ⟨T.M, T.c⟩ rest, fun x => (hf x).trans (hrest _)⟩

theorem relun (n k : ℕ) : Agent035.ReLUn n k = Ref.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (computes_iff j n f).1 hf⟩
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (computes_iff j n f).2 hf⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent035.depthBound n = Ref.depthBound n := rfl

/-- Honest `sorry`: `agent_side_false` shows the left-hand side is `False`, so
this iff is equivalent to the *negation* of the reference Theorem 2.  Deciding
it therefore needs a proof (or refutation) of Theorem 2 itself, which is
`sorry`-ed on both sides and may not be routed through. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent035.CPWL n = Agent035.ReLUn n (Agent035.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_035

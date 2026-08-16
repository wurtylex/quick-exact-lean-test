namespace Star_033

/-! ### Networks

`Agent033.ComputesReLU` and `Ref.ComputedBy` are the same recursion; the only
difference is that the affine-map structures `AffineMapRn`/`Aff` are two copies
of the same pair of fields. -/

private theorem computes_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent033.ComputesReLU n k f ↔ Ref.ComputedBy n k f := by
  intro k
  induction k with
  | zero =>
      intro n f
      constructor
      · intro h
        obtain ⟨T, hT⟩ : ∃ T : Agent033.AffineMapRn n 1, ∀ x, f x = T.eval x 0 := h
        show ∃ T : Ref.Aff n 1, ∀ x, f x = T.eval x 0
        exact ⟨⟨T.A, T.c⟩, hT⟩
      · intro h
        obtain ⟨T, hT⟩ : ∃ T : Ref.Aff n 1, ∀ x, f x = T.eval x 0 := h
        show ∃ T : Agent033.AffineMapRn n 1, ∀ x, f x = T.eval x 0
        exact ⟨⟨T.M, T.c⟩, hT⟩
  | succ k ih =>
      intro n f
      constructor
      · intro h
        obtain ⟨m, T, g, hg, hf⟩ :
            ∃ (m : ℕ) (T : Agent033.AffineMapRn n m) (g : (Fin m → ℝ) → ℝ),
              Agent033.ComputesReLU m k g ∧
                ∀ x, f x = g (Agent033.reluVec (T.eval x)) := h
        show ∃ (m : ℕ) (T : Ref.Aff n m) (g : (Fin m → ℝ) → ℝ),
            Ref.ComputedBy m k g ∧ ∀ x, f x = g (Ref.reluVec (T.eval x))
        exact ⟨m, ⟨T.A, T.c⟩, g, (ih m g).mp hg, hf⟩
      · intro h
        obtain ⟨m, T, g, hg, hf⟩ :
            ∃ (m : ℕ) (T : Ref.Aff n m) (g : (Fin m → ℝ) → ℝ),
              Ref.ComputedBy m k g ∧ ∀ x, f x = g (Ref.reluVec (T.eval x)) := h
        show ∃ (m : ℕ) (T : Agent033.AffineMapRn n m) (g : (Fin m → ℝ) → ℝ),
            Agent033.ComputesReLU m k g ∧
              ∀ x, f x = g (Agent033.reluVec (T.eval x))
        exact ⟨m, ⟨T.M, T.c⟩, g, (ih m g).mpr hg, hf⟩

theorem relun (n k : ℕ) : Agent033.ReLUn n k = Ref.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨j, hj, h⟩; exact ⟨j, hj, (computes_iff j n f).mp h⟩
  · rintro ⟨j, hj, h⟩; exact ⟨j, hj, (computes_iff j n f).mpr h⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent033.depthBound n = Ref.depthBound n := rfl

/-! ### CPWL

Agent 033 requires a *finite* family of affine maps such that `f` agrees with one
of them on a **neighbourhood** of each point.  On connected `ℝⁿ` that forces `f`
to be globally affine, so it is strictly stronger than the reference notion. -/

private lemma halfspace_isPolyhedron {n : ℕ} {S : Set (Fin n → ℝ)}
    (h : Ref.IsHalfspace n S) : Ref.IsPolyhedron n S := by
  refine ⟨1, fun _ => S, fun _ => h, ?_⟩
  ext x; simp

/-- `relu` of a coordinate is *not* in the agent's `CPWL`: the kink at the origin
defeats neighbourhood agreement with a single affine map. -/
private lemma relu0_not_mem (n : ℕ) :
    (fun x : Fin (n + 1) → ℝ => max 0 (x 0)) ∉ Agent033.CPWL (n + 1) := by
  rintro ⟨-, m, a, b, h⟩
  obtain ⟨i, U, hU, h0U, hfU⟩ := h 0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU 0 h0U
  have key : ∀ t : ℝ, |t| < ε → max 0 t = (∑ j, a i j) * t + b i := by
    intro t ht
    have hy : (fun _ : Fin (n + 1) => t) ∈ Metric.ball (0 : Fin (n + 1) → ℝ) ε :=
      Metric.mem_ball.2 ((dist_pi_lt_iff hε).2 fun j => by simpa [Real.dist_eq] using ht)
    have h2 := hfU _ (hball hy)
    rw [Finset.sum_mul]
    exact h2
  have h0 := key 0 (by simpa using hε)
  have hp := key (ε / 2) (by rw [abs_of_pos (by linarith : (0:ℝ) < ε / 2)]; linarith)
  have hm := key (-(ε / 2)) (by
    rw [abs_neg, abs_of_pos (by linarith : (0:ℝ) < ε / 2)]; linarith)
  rw [max_self] at h0
  rw [max_eq_right (by linarith : (0:ℝ) ≤ ε / 2)] at hp
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0:ℝ))] at hm
  linarith

/-- The same function *is* in the reference `CPWL`: two halfspaces cover `ℝ`. -/
private lemma relu0_mem_ref : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Ref.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2,
    ![{x : Fin 1 → ℝ | x 0 ≤ 0}, {x : Fin 1 → ℝ | -x 0 ≤ 0}],
    ![fun _ => 0, fun x => x 0], ?_, ?_, ?_, ?_⟩
  · rw [Fin.forall_fin_two]
    exact ⟨halfspace_isPolyhedron ⟨fun _ => 1, 0, by ext x; simp⟩,
           halfspace_isPolyhedron ⟨fun _ => -1, 0, by ext x; simp⟩⟩
  · rw [Fin.forall_fin_two]
    exact ⟨⟨fun _ => 0, 0, fun x => by simp⟩, ⟨fun _ => 1, 0, fun x => by simp⟩⟩
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    rcases le_or_gt (x 0) 0 with hx | hx
    · exact ⟨0, hx⟩
    · exact ⟨1, show -x 0 ≤ 0 by linarith⟩
  · rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · intro x hx
      have hx' : x 0 ≤ 0 := hx
      show max 0 (x 0) = 0
      exact max_eq_left hx'
    · intro x hx
      have hx' : -x 0 ≤ 0 := hx
      show max 0 (x 0) = x 0
      exact max_eq_right (by linarith)

/-- `cpwl` is **false**: the agent's neighbourhood-agreement condition is
strictly stronger than the reference polyhedral-cover condition. -/
theorem cpwl_ne : ∃ n, Agent033.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun hEq => relu0_not_mem 0 ?_⟩
  rw [hEq]
  exact relu0_mem_ref

/-- Stronger than `cpwl_ne`: the agent's own Theorem 2 is false, with no
appeal to the reference file.  At `n = 3`, `x ↦ relu (x 0)` is a one-hidden-layer
network but is rejected by the agent's `CPWL`. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent033.CPWL n = Agent033.ReLUn n (Agent033.depthBound n)) := by
  intro h
  have hmem : (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈
      Agent033.ReLUn 3 (Agent033.depthBound 3) := by
    refine ⟨1, ?_, ?_⟩
    · simp only [Agent033.depthBound]; exact Nat.le_add_left 1 _
    · show ∃ (m : ℕ) (T : Agent033.AffineMapRn 3 m) (g : (Fin m → ℝ) → ℝ),
          Agent033.ComputesReLU m 0 g ∧
            ∀ x, max 0 (x 0) = g (Agent033.reluVec (T.eval x))
      refine ⟨1, ⟨Matrix.of fun _ j => if j = 0 then (1:ℝ) else 0, 0⟩, fun v => v 0, ?_, ?_⟩
      · show ∃ T : Agent033.AffineMapRn 1 1, ∀ x, x 0 = T.eval x 0
        exact ⟨⟨1, 0⟩, fun x => by simp [Agent033.AffineMapRn.eval, Matrix.one_mulVec]⟩
      · intro x
        simp [Agent033.AffineMapRn.eval, Agent033.reluVec, Agent033.relu, Matrix.mulVec,
          dotProduct, Matrix.of_apply, ite_mul, Finset.sum_ite_eq']
  rw [← h 3 (le_refl 3)] at hmem
  exact relu0_not_mem 2 hmem

/-- Honest `sorry`.  Since `agent_side_false` shows the left side is `False`, the
forward implication is vacuous and the iff is equivalent to the *negation* of the
reference Theorem 2 — which is true but unproved (`Ref.theorem2` is `sorry`), so
neither `statement` nor `statement_ne` is provable here. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent033.CPWL n = Agent033.ReLUn n (Agent033.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_033

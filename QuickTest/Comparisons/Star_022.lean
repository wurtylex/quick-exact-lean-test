import QuickTest.Formalizations.Thm2_022
import QuickTest.Reference

namespace Star_022

/-! ## Bridging lemma for the matrix/vector encodings of an affine functional -/

/-- A `1 × n` matrix applied to a vector, read off at the unique output
coordinate, is the obvious linear combination. -/
private lemma mulVec_zero_apply {n : ℕ} (M : Matrix (Fin 1) (Fin n) ℝ) (x : Fin n → ℝ) :
    M.mulVec x 0 = ∑ j, M 0 j * x j := rfl

/-! ## `depthBound` -/

/-- Both files write `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`, character for character. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent022.depthBound n = Ref.depthBound n := rfl

/-! ## `ReLUn`

Both files take **at most** `k` hidden layers, so the only gap is the encoding of
the base case (explicit weights/bias versus a `1 × n` matrix) and `f = g ∘ …`
versus `∀ x, f x = …`. -/

private lemma computable_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent022.ExactReLUComputable k n f ↔ Ref.ComputedBy n k f := by
  intro k
  induction k with
  | zero =>
      intro n f
      constructor
      · rintro ⟨w, b, hb⟩
        exact ⟨⟨Matrix.of fun _ j => w j, fun _ => b⟩, fun x => by rw [hb x]; rfl⟩
      · rintro ⟨T, hT⟩
        exact ⟨fun j => T.M 0 j, T.c 0, fun x => by rw [hT x]; rfl⟩
  | succ k ih =>
      intro n f
      constructor
      · rintro ⟨m, T, g, hg, hf⟩
        exact ⟨m, ⟨T.A, T.c⟩, g, (ih m g).mp hg, fun x => by rw [hf]; rfl⟩
      · rintro ⟨m, T, g, hg, hf⟩
        exact ⟨m, ⟨T.M, T.c⟩, g, (ih m g).mpr hg, funext fun x => by rw [hf x]; rfl⟩

theorem relun (n k : ℕ) : Agent022.ReLUn n k = Ref.ReLUn n k := by
  ext f
  exact exists_congr fun j => and_congr_right fun _ => computable_iff j n f

/-! ## `CPWL` — the agent's version is the neighbourhood-agreement family

`Agent022.CPWL n` asks for finitely many affine functions such that *every point
has a neighbourhood* on which `f` equals one of them.  On connected `ℝⁿ` that
forces `f` to be globally affine, so it is strictly stronger than piecewise
linearity and the comparison with `Ref.CPWL` is false. -/

/-- `x ↦ max 0 (x 0)` is not locally-affine-with-finitely-many-pieces: at the
origin, agreement on a whole neighbourhood contradicts the kink. -/
private lemma not_mem_agent (n : ℕ) [NeZero n] :
    (fun x : Fin n → ℝ => max 0 (x 0)) ∉ Agent022.CPWL n := by
  rintro ⟨-, m, w, b, h⟩
  obtain ⟨i, U, hU, hUeq⟩ := h 0
  have hU' : U ∈ nhds (fun _ : Fin n => (0 : ℝ)) := hU
  have hc : Continuous (fun t : ℝ => (fun _ : Fin n => t)) :=
    continuous_pi fun _ => continuous_id
  have hV : (fun t : ℝ => (fun _ : Fin n => t)) ⁻¹' U ∈ nhds (0 : ℝ) :=
    hc.continuousAt.preimage_mem_nhds hU'
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hV
  have key : ∀ t : ℝ, |t| < ε → max 0 t = (∑ j, w i j) * t + b i := by
    intro t ht
    have hmem : (fun _ : Fin n => t) ∈ U :=
      hsub (show t ∈ Metric.ball (0 : ℝ) ε by simpa [Real.dist_eq] using ht)
    have h2 := hUeq _ hmem
    rw [Finset.sum_mul]
    exact h2
  have h0 := key 0 (by simpa using hε)
  have hp := key (ε / 2) (by rw [abs_of_pos (by linarith : (0:ℝ) < ε / 2)]; linarith)
  have hm := key (-(ε / 2)) (by rw [abs_of_neg (by linarith : -(ε / 2) < (0:ℝ))]; linarith)
  rw [max_self] at h0
  rw [max_eq_right (by linarith : (0:ℝ) ≤ ε / 2)] at hp
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0:ℝ))] at hm
  linarith

private lemma polyOf {S : Set (Fin 1 → ℝ)} (h : Ref.IsHalfspace 1 S) : Ref.IsPolyhedron 1 S :=
  ⟨1, fun _ => S, fun _ => h, (Set.iInter_const _).symm⟩

/-- The same function *is* CPWL in the reference sense: the two halflines cover
`ℝ`, and on each one `f` agrees with an affine functional. -/
private lemma mem_ref : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Ref.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2,
    ![{x : Fin 1 → ℝ | ∑ i, (1:ℝ) * x i ≤ 0}, {x : Fin 1 → ℝ | ∑ i, (-1:ℝ) * x i ≤ 0}],
    ![fun _ => (0:ℝ), fun x => x 0], ?_, ?_, ?_, ?_⟩
  · rw [Fin.forall_fin_two]
    exact ⟨polyOf ⟨fun _ => 1, 0, rfl⟩, polyOf ⟨fun _ => -1, 0, rfl⟩⟩
  · rw [Fin.forall_fin_two]
    exact ⟨⟨fun _ => 0, 0, by simp⟩, ⟨fun _ => 1, 0, by simp⟩⟩
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    rcases le_or_gt (x 0) 0 with hx | hx
    · refine ⟨0, ?_⟩
      show x ∈ {x : Fin 1 → ℝ | ∑ i, (1:ℝ) * x i ≤ 0}
      simp only [Set.mem_setOf_eq, Fin.sum_univ_one]
      linarith
    · refine ⟨1, ?_⟩
      show x ∈ {x : Fin 1 → ℝ | ∑ i, (-1:ℝ) * x i ≤ 0}
      simp only [Set.mem_setOf_eq, Fin.sum_univ_one]
      linarith
  · rw [Fin.forall_fin_two]
    constructor
    · intro x hx
      simp only [Matrix.cons_val_zero, Set.mem_setOf_eq, Fin.sum_univ_one, one_mul] at hx
      simp only [Matrix.cons_val_zero]
      exact max_eq_left hx
    · intro x hx
      simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, Set.mem_setOf_eq,
        Fin.sum_univ_one] at hx
      simp only [Matrix.cons_val_one, Matrix.head_cons]
      exact max_eq_right (by linarith)

/-- The agent's `CPWL` is **not** the reference `CPWL`. -/
theorem cpwl_ne : ∃ n, Agent022.CPWL n ≠ Ref.CPWL n :=
  ⟨1, fun h => not_mem_agent 1 (by rw [h]; exact mem_ref)⟩

/-! ## The bonus obligation: the agent's own Theorem 2 is false -/

/-- `x ↦ max 0 (x 0)` on `ℝ³` is a one-hidden-layer ReLU network. -/
private lemma relu_coord_mem :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent022.ReLUn 3 (Agent022.depthBound 3) := by
  refine ⟨1, Nat.le_add_left 1 _, 1,
    ⟨Matrix.of fun _ j => if j = 0 then (1:ℝ) else 0, 0⟩, fun v => v 0,
    ⟨fun _ => 1, 0, ?_⟩, ?_⟩
  · intro v; simp [Fin.sum_univ_one]
  · funext x
    simp [Function.comp_apply, Agent022.reluVec, Agent022.relu, Agent022.AffineMap'.apply,
      mulVec_zero_apply, Fin.sum_univ_three]

/-- No reference theorem needed: the agent's statement fails already at `n = 3`,
because `relu` of a coordinate is a depth-1 network yet is rejected by the
neighbourhood-agreement `CPWL`. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent022.CPWL n = Agent022.ReLUn n (Agent022.depthBound n)) := by
  intro h
  exact not_mem_agent 3 (by rw [h 3 le_rfl]; exact relu_coord_mem)

/-- Consequently the two statements are equivalent exactly when the *reference*
statement is false — and deciding that is Theorem 2 itself. -/
theorem statement_iff_ref_false :
    ((∀ n, 3 ≤ n → Agent022.CPWL n = Agent022.ReLUn n (Agent022.depthBound n)) ↔
      (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n))) ↔
    ¬ (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) :=
  iff_false_left agent_side_false

/-- The agent side is false (`agent_side_false`), so this iff holds iff the
reference side is false too — i.e. it is equivalent to refuting the real
Theorem 2.  Both `Ref.theorem2` and `Agent022.theorem2` are `sorry`, and routing
through them would prove nothing, so this is an honest `sorry`. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent022.CPWL n = Agent022.ReLUn n (Agent022.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_022

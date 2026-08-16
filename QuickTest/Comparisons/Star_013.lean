import QuickTest.Formalizations.Thm2_013
import QuickTest.Reference

namespace Star_013

/-! `depthBound` and `ReLUn` agree (the latter up to `funext`).  `CPWL` does **not**:
`Agent013.IsPWL` demands agreement with one affine map on a whole *neighbourhood* of each
point, which rejects every kink.  `x ↦ max 0 (x 0)` separates the two definitions and also
makes the agent's `theorem2` outright false. -/

/-- The defining equation of `Agent013.AffineMap.eval` in coordinates. -/
private lemma eval_apply {a : ℕ} (T : Agent013.AffineMap a 1) (x : Fin a → ℝ) :
    T.eval x 0 = (∑ j, T.A 0 j * x j) + T.c 0 := rfl

/-- An affine functional takes the same average value at `±y` as at the origin. -/
private lemma eval_symm {a : ℕ} (T : Agent013.AffineMap a 1) (y : Fin a → ℝ) :
    T.eval y 0 + T.eval (-y) 0 = 2 * T.eval 0 0 := by
  have h : (∑ j, T.A 0 j * (-y) j) + (∑ j, T.A 0 j * y j) = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun j _ => by simp
  have h4 : ∑ j, T.A 0 j * (0 : Fin a → ℝ) j = 0 := by simp
  rw [eval_apply T y, eval_apply T (-y), eval_apply T 0, h4]
  linarith

/-- The neighbourhood-agreement condition rejects the kink of `x ↦ max 0 (x i₀)`. -/
private lemma not_isPWL {n : ℕ} (i0 : Fin n) :
    ¬ Agent013.IsPWL (fun x : Fin n → ℝ => max 0 (x i0)) := by
  rintro ⟨r, g, h⟩
  obtain ⟨i, ε, hε, hy⟩ := h 0
  set v : Fin n → ℝ := fun j => if j = i0 then ε / 2 else 0 with hv
  have hvi : v i0 = ε / 2 := by simp [hv]
  have hvabs : ∀ j, |v j| ≤ ε / 2 := by
    intro j
    by_cases hj : j = i0 <;> simp [hv, hj, abs_of_pos (half_pos hε)] <;> linarith
  have hdist : ∀ w : Fin n → ℝ, (∀ j, |w j| ≤ ε / 2) → dist w (0 : Fin n → ℝ) < ε := by
    intro w hw
    rw [dist_pi_lt_iff hε]
    intro j
    simp only [Pi.zero_apply, Real.dist_eq, sub_zero]
    linarith [half_lt_self hε, hw j]
  have h1 : max 0 (v i0) = (g i).eval v 0 := hy v (hdist v hvabs)
  have h2 : max 0 ((-v) i0) = (g i).eval (-v) 0 :=
    hy (-v) (hdist (-v) fun j => by rw [Pi.neg_apply, abs_neg]; exact hvabs j)
  have h3 : max 0 ((0 : Fin n → ℝ) i0) = (g i).eval 0 0 := hy 0 (by simpa using hε)
  rw [hvi, max_eq_right (le_of_lt (half_pos hε))] at h1
  rw [Pi.neg_apply, hvi, max_eq_left (by linarith [half_pos hε] : -(ε / 2) ≤ 0)] at h2
  rw [Pi.zero_apply, max_self] at h3
  have hs := eval_symm (g i) v
  rw [← h1, ← h2, ← h3] at hs
  linarith

private lemma half_poly {n : ℕ} {S : Set (Fin n → ℝ)} (h : Ref.IsHalfspace n S) :
    Ref.IsPolyhedron n S := ⟨1, fun _ => S, fun _ => h, (Set.iInter_const _).symm⟩

/-- `x ↦ max 0 (x 0)` *is* a reference CPWL function: two halflines cover `ℝ`. -/
private lemma ref_mem : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Ref.CPWL 1 := by
  have hne : ¬((1 : Fin 2) = 0) := by decide
  refine ⟨continuous_const.max (continuous_apply 0), 2,
    fun i : Fin 2 => {x : Fin 1 → ℝ | (∑ j, (if i = 0 then (1 : ℝ) else -1) * x j) ≤ 0},
    fun (i : Fin 2) (x : Fin 1 → ℝ) => if i = 0 then (0 : ℝ) else x 0, ?_, ?_, ?_, ?_⟩
  · exact fun i => half_poly ⟨fun _ => (if i = 0 then (1 : ℝ) else -1), 0, rfl⟩
  · intro i
    by_cases hi : i = 0
    · refine ⟨0, 0, fun x => ?_⟩
      show (if i = 0 then (0 : ℝ) else x 0) = (∑ j, (0 : Fin 1 → ℝ) j * x j) + 0
      rw [if_pos hi]; simp
    · refine ⟨fun _ => 1, 0, fun x => ?_⟩
      show (if i = 0 then (0 : ℝ) else x 0) = (∑ j, (1 : ℝ) * x j) + 0
      rw [if_neg hi, Fin.sum_univ_one, one_mul, add_zero]
  · refine Set.eq_univ_of_forall fun x => ?_
    rcases le_or_gt (x 0) 0 with hx | hx
    · refine Set.mem_iUnion.2 ⟨0, ?_⟩
      show (∑ j, (if (0 : Fin 2) = 0 then (1 : ℝ) else -1) * x j) ≤ 0
      rw [if_pos rfl, Fin.sum_univ_one, one_mul]; exact hx
    · refine Set.mem_iUnion.2 ⟨1, ?_⟩
      show (∑ j, (if (1 : Fin 2) = 0 then (1 : ℝ) else -1) * x j) ≤ 0
      rw [if_neg hne, Fin.sum_univ_one]; linarith
  · intro i x hx
    have hx' : (if i = 0 then (1 : ℝ) else -1) * x 0 ≤ 0 := by
      simpa [Fin.sum_univ_one] using hx
    show max 0 (x 0) = if i = 0 then (0 : ℝ) else x 0
    by_cases hi : i = 0
    · rw [if_pos hi] at hx' ⊢; rw [one_mul] at hx'; exact max_eq_left hx'
    · rw [if_neg hi] at hx' ⊢; exact max_eq_right (by linarith)

/-- `Agent013.CPWL` is strictly stronger than `Ref.CPWL`: it excludes `x ↦ max 0 (x 0)`. -/
theorem cpwl_ne : ∃ n, Agent013.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  have hmem := ref_mem
  rw [← h] at hmem
  exact not_isPWL (0 : Fin 1) hmem.2

private def pick : Agent013.AffineMap 3 1 :=
  ⟨Matrix.of fun _ j => if j = 0 then (1 : ℝ) else 0, 0⟩

private lemma pick_eval (x : Fin 3 → ℝ) : pick.eval x 0 = x 0 := by
  rw [eval_apply]; simp [pick, Matrix.of_apply, Fin.sum_univ_three]

/-- `x ↦ max 0 (x 0)` is a one-hidden-layer network on `ℝ³`. -/
private lemma relu_coord_mem :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent013.ReLUn 3 (Agent013.depthBound 3) := by
  have h0 : Agent013.IsReLURep 1 0 (fun v : Fin 1 → ℝ => v 0) :=
    ⟨⟨1, 0⟩, funext fun v => by simp [Agent013.AffineMap.eval, Matrix.one_mulVec]⟩
  refine ⟨1, Nat.le_add_left 1 _, 1, pick, fun v : Fin 1 → ℝ => v 0, h0, ?_⟩
  funext x
  show max 0 (x 0) = Agent013.relu (pick.eval x 0)
  simp only [Agent013.relu, pick_eval]

/-- The agent's Theorem 2 is false as stated: at `n = 3` its `CPWL` misses a
one-hidden-layer ReLU network. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent013.CPWL n = Agent013.ReLUn n (Agent013.depthBound n)) := by
  intro h
  have hmem := relu_coord_mem
  rw [← h 3 le_rfl] at hmem; exact not_isPWL (0 : Fin 3) hmem.2

private lemma relurep_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent013.IsReLURep n k f ↔ Ref.ComputedBy n k f := by
  intro k
  induction k with
  | zero =>
    intro n f; constructor
    · rintro ⟨T, rfl⟩; exact ⟨⟨T.A, T.c⟩, fun x => rfl⟩
    · rintro ⟨T, hT⟩; exact ⟨⟨T.M, T.c⟩, funext hT⟩
  | succ k ih =>
    intro n f; constructor
    · rintro ⟨m, T, g, hg, rfl⟩; exact ⟨m, ⟨T.A, T.c⟩, g, (ih m g).mp hg, fun x => rfl⟩
    · rintro ⟨m, T, g, hg, hf⟩; exact ⟨m, ⟨T.M, T.c⟩, g, (ih m g).mpr hg, funext hf⟩

theorem relun (n k : ℕ) : Agent013.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent013.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, h⟩; exact ⟨j, hj, (relurep_iff j n f).mp h⟩
  · rintro ⟨j, hj, h⟩; exact ⟨j, hj, (relurep_iff j n f).mpr h⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent013.depthBound n = Ref.depthBound n := rfl

/-- Since the agent side is provably false, `statement` is exactly `¬ Ref.theorem2`. -/
theorem statement_iff :
    ((∀ n, 3 ≤ n → Agent013.CPWL n = Agent013.ReLUn n (Agent013.depthBound n)) ↔
      (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n))) ↔
    ¬ (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) :=
  ⟨fun h hr => agent_side_false (h.mpr hr),
   fun h => ⟨fun hl => absurd hl agent_side_false, fun hr => absurd hr h⟩⟩

-- Honest `sorry`: by `statement_iff` this is `¬ Ref.theorem2`, whose refutation needs the
-- (true, but `sorry`-ed in `Reference.lean`) reference theorem.
theorem statement :
    (∀ n, 3 ≤ n → Agent013.CPWL n = Agent013.ReLUn n (Agent013.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_013

namespace Bridge_053_054

/-!
`ReLUn`/`depthBound` agree (their definitions are the same modulo the pointwise-vs-
funext presentation of the network recursion). `CPWL` genuinely differs: 053 requires
`f` to agree with a *single* affine piece on a whole metric-ball neighborhood of every
point (definition (b) of the spec), which on the connected domain `ℝ^n` forces any
member to be globally affine near every point — so `x ↦ max 0 (x 0)` (a genuine crease
at `0`) is excluded from `Agent053.CPWL`. 054 uses a genuine polyhedral-subdivision
definition (a) that does admit such creases. We exhibit that witness explicitly.
-/

private def toJ {a b : ℕ} (T : Agent053.AffineMap a b) : Agent054.AffineMap a b := ⟨T.A, T.c⟩
private def toI {a b : ℕ} (T : Agent054.AffineMap a b) : Agent053.AffineMap a b := ⟨T.A, T.c⟩

private lemma apply_eq_eval {a b : ℕ} (T : Agent053.AffineMap a b) (x : Fin a → ℝ) :
    T.apply x = (toJ T).eval x := by
  simp [Agent053.AffineMap.apply, Agent054.AffineMap.eval, toJ]

private lemma eval_eq_apply {a b : ℕ} (T : Agent054.AffineMap a b) (x : Fin a → ℝ) :
    T.eval x = (toI T).apply x := by
  simp [Agent053.AffineMap.apply, Agent054.AffineMap.eval, toI]

private lemma reluVec_eq {m : ℕ} (v : Fin m → ℝ) :
    Agent053.reluVec v = Agent054.reluVec v := by
  funext i; simp [Agent053.reluVec, Agent054.reluVec, Agent053.relu, Agent054.relu]

private lemma computes_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent053.computesReLUExact k n f ↔ Agent054.NetComputes k n f := by
  intro k
  induction k with
  | zero =>
      intro n f
      constructor
      · rintro ⟨T, hT⟩
        exact ⟨toJ T, funext fun x => by rw [hT x, apply_eq_eval]⟩
      · rintro ⟨T, hT⟩
        exact ⟨toI T, fun x => by rw [hT, eval_eq_apply]⟩
  | succ k ih =>
      intro n f
      constructor
      · rintro ⟨m, T, g, hg, hf⟩
        exact ⟨m, toJ T, g, (ih m g).mp hg,
          funext fun x => by rw [hf x, apply_eq_eval, reluVec_eq]⟩
      · rintro ⟨m, T, g, hg, hf⟩
        exact ⟨m, toI T, g, (ih m g).mpr hg,
          fun x => by rw [hf, eval_eq_apply, ← reluVec_eq]⟩

theorem relun (n k : ℕ) : Agent053.ReLUn n k = Agent054.ReLUn n k := by
  ext f
  simp only [Agent053.ReLUn, Agent054.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, hf⟩; exact ⟨j, hj, (computes_iff j n f).mp hf⟩
  · rintro ⟨j, hj, hf⟩; exact ⟨j, hj, (computes_iff j n f).mpr hf⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent053.depthBound n = Agent054.depthBound n := by
  unfold Agent053.depthBound Agent054.depthBound
  rfl

/-- The witness `x ↦ max 0 (x 0)` on `ℝ^1`: a genuine crease at the origin. -/
private def wit : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

private lemma mem054 : wit ∈ Agent054.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2,
    ![{x : Fin 1 → ℝ | x 0 ≤ 0}, {x : Fin 1 → ℝ | 0 ≤ x 0}],
    ![(fun _ : Fin 1 → ℝ => (0 : ℝ)), (fun x : Fin 1 → ℝ => x 0)],
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · intro x hx y hy a b ha hb _
      simp only [Matrix.cons_val_zero, Set.mem_setOf_eq] at hx hy ⊢
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have h1 := mul_nonpos_of_nonneg_of_nonpos ha hx
      have h2 := mul_nonpos_of_nonneg_of_nonpos hb hy
      linarith
    · intro x hx y hy a b ha hb _
      simp only [Matrix.cons_val_one, Matrix.head_cons, Set.mem_setOf_eq] at hx hy ⊢
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have h1 := mul_nonneg ha hx
      have h2 := mul_nonneg hb hy
      linarith
  · intro i
    fin_cases i
    · simpa using isClosed_le (continuous_apply (0 : Fin 1)) continuous_const
    · simpa using isClosed_le continuous_const (continuous_apply (0 : Fin 1))
  · apply Set.eq_univ_of_forall
    intro x
    rcases le_total (x 0) 0 with h | h
    · exact Set.mem_iUnion.mpr ⟨0, by simpa using h⟩
    · exact Set.mem_iUnion.mpr ⟨1, by simpa using h⟩
  · intro i
    fin_cases i
    · exact ⟨fun _ => 0, 0, by intro x; simp⟩
    · exact ⟨fun _ => 1, 0, by intro x; simp [Fin.sum_univ_one]⟩
  · intro i x hx
    fin_cases i
    · simp only [Matrix.cons_val_zero, Set.mem_setOf_eq] at hx
      simpa [wit] using max_eq_left hx
    · simp only [Matrix.cons_val_one, Matrix.head_cons, Set.mem_setOf_eq] at hx
      simpa [wit] using max_eq_right hx

private lemma not_mem053 : wit ∉ Agent053.CPWL 1 := by
  rintro ⟨-, N, pieces, haff, hloc⟩
  obtain ⟨i, ε, hεpos, hε⟩ := hloc (0 : Fin 1 → ℝ)
  obtain ⟨w, b, hw⟩ := haff i
  have hcont : Continuous (fun t : ℝ => (fun _ : Fin 1 => t)) :=
    continuous_pi (fun _ => continuous_id)
  have hcAt : ContinuousAt (fun t : ℝ => (fun _ : Fin 1 => t)) (0 : ℝ) := hcont.continuousAt
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcAt ε hεpos
  have key : ∀ t : ℝ, |t| < δ → max 0 t = w 0 * t + b := by
    intro t ht
    have hdt : dist t (0 : ℝ) < δ := by rwa [Real.dist_eq, sub_zero]
    have hy : dist (fun _ : Fin 1 => t) (0 : Fin 1 → ℝ) < ε := by simpa using hδ hdt
    have heq := hε (fun _ : Fin 1 => t) hy
    have hp := hw (fun _ : Fin 1 => t)
    simpa [wit, Fin.sum_univ_one] using heq.trans hp
  have h0 := key 0 (by simpa using hδpos)
  have hδ2 : (0 : ℝ) < δ / 2 := by linarith
  have hp := key (δ / 2) (by rw [abs_of_pos hδ2]; linarith)
  have hn := key (-(δ / 2)) (by rw [abs_of_neg (show (-(δ / 2) : ℝ) < 0 by linarith)]; linarith)
  simp only [max_self, mul_zero, zero_add] at h0
  rw [max_eq_right hδ2.le] at hp
  rw [max_eq_left (by linarith : -(δ / 2) ≤ (0 : ℝ)), mul_neg] at hn
  linarith [hp, hn, h0]

theorem cpwl_ne : ∃ n, Agent053.CPWL n ≠ Agent054.CPWL n := by
  refine ⟨1, fun h => not_mem053 ?_⟩
  rw [h]; exact mem054

-- `statement` compares "Agent053's own theorem2 holds" with "Agent054's own theorem2
-- holds". We've shown Agent053's CPWL is too restrictive (misses `wit`, computable in
-- 1 hidden layer, well within `depthBound n` for any `n ≥ 3`), so its `theorem2` is
-- provably *false*. But resolving the ↔ also requires knowing the truth value of
-- Agent054's `theorem2`, whose CPWL is the faithful polyhedral definition and whose
-- truth is exactly the (unproved, open-in-this-repo) mathematical Theorem 2 itself —
-- out of scope for a bridge between two definitional frameworks.
theorem statement :
    (∀ n, 3 ≤ n → Agent053.CPWL n = Agent053.ReLUn n (Agent053.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent054.CPWL n = Agent054.ReLUn n (Agent054.depthBound n)) := sorry

end Bridge_053_054

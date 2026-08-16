namespace Bridge_048_049

/-! ## `cpwl` : refuted

`Agent048.CPWL` requires a *single* affine function to equal `f` on a whole
open neighbourhood of every point (local agreement). `Agent049.CPWL` only
requires a finite *polyhedral subdivision* on whose (closed) pieces `f`
agrees with some affine function; pieces may share boundary points. The
witness `f x = max 0 (x 0)` on `ℝ^1` lies in `Agent049.CPWL 1` (two
half-line pieces) but not in `Agent048.CPWL 1`: no single affine function
can equal `f` on a full two-sided neighbourhood of `0`, since such a
neighbourhood contains points with `x 0 > 0` (forcing slope `1`, intercept
`0`) and points with `x 0 < 0` (forcing the zero function) simultaneously. -/

noncomputable def wf : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

lemma wf_mem049 : wf ∈ Agent049.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2,
    ![{x : Fin 1 → ℝ | 0 ≤ x 0}, {x : Fin 1 → ℝ | x 0 ≤ 0}], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · refine ⟨1, fun _ _ => (-1 : ℝ), fun _ => 0, ?_⟩
      ext x
      simp only [Set.mem_setOf_eq, Matrix.cons_val_zero]
      constructor
      · intro h j
        have : (fun _ _ => (-1:ℝ)).mulVec x j = -x 0 := by
          simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_one]
        rw [this]; simpa using h
      · intro h
        have h0 := h 0
        have : (fun _ _ => (-1:ℝ)).mulVec x 0 = -x 0 := by
          simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_one]
        rw [this] at h0; linarith
    · refine ⟨1, fun _ _ => (1 : ℝ), fun _ => 0, ?_⟩
      ext x
      simp only [Set.mem_setOf_eq, Matrix.cons_val_one, Matrix.head_cons]
      constructor
      · intro h j
        have : (fun _ _ => (1:ℝ)).mulVec x j = x 0 := by
          simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_one]
        rw [this]; linarith
      · intro h
        have h0 := h 0
        have : (fun _ _ => (1:ℝ)).mulVec x 0 = x 0 := by
          simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_one]
        rw [this] at h0; linarith
  · apply Set.eq_univ_of_forall
    intro x
    simp only [Set.mem_iUnion]
    rcases le_total 0 (x 0) with h | h
    · exact ⟨0, by simp only [Matrix.cons_val_zero, Set.mem_setOf_eq]; linarith⟩
    · exact ⟨1, by simp only [Matrix.cons_val_one, Matrix.head_cons, Set.mem_setOf_eq]; linarith⟩
  · intro i
    fin_cases i
    · refine ⟨fun x => x 0, ⟨fun _ => 1, 0, by funext x; simp [Fin.sum_univ_one]⟩, ?_⟩
      intro x hx
      simp only [Matrix.cons_val_zero, Set.mem_setOf_eq] at hx
      exact max_eq_right hx
    · refine ⟨fun _ => 0, ⟨fun _ => 0, 0, by funext x; simp⟩, ?_⟩
      intro x hx
      simp only [Matrix.cons_val_one, Matrix.head_cons, Set.mem_setOf_eq] at hx
      exact max_eq_left hx

lemma wf_not_mem048 : wf ∉ Agent048.CPWL 1 := by
  rintro ⟨-, m, g, hg, hloc⟩
  obtain ⟨i, hi⟩ := hloc (0 : Fin 1 → ℝ)
  obtain ⟨a, b, hab⟩ := hg i
  have hcont : Continuous (fun t : ℝ => (fun _ : Fin 1 => t)) :=
    continuous_pi fun _ => continuous_id
  have htend : Filter.Tendsto (fun t : ℝ => (fun _ : Fin 1 => t)) (nhds 0)
      (nhds (0 : Fin 1 → ℝ)) := by simpa using hcont.tendsto 0
  have hpull : ∀ᶠ t in nhds (0 : ℝ), wf (fun _ => t) = g i (fun _ => t) :=
    htend.eventually hi
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hpull
  have hb : (0 : ℝ) = a 0 * 0 + b := by
    have h0 : wf (fun _ : Fin 1 => (0:ℝ)) = g i (fun _ : Fin 1 => (0:ℝ)) :=
      hball (by rw [dist_self]; exact hε)
    simpa [wf, hab, Fin.sum_univ_one, max_self] using h0
  have hpos : ε / 2 = a 0 * (ε / 2) + b := by
    have h1 : wf (fun _ : Fin 1 => ε / 2) = g i (fun _ : Fin 1 => ε / 2) :=
      hball (by rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith : (0:ℝ) < ε / 2)]; linarith)
    have heq : max (0:ℝ) (ε / 2) = a 0 * (ε / 2) + b := by
      simpa [wf, hab, Fin.sum_univ_one] using h1
    rwa [max_eq_right (by linarith : (0:ℝ) ≤ ε / 2)] at heq
  have hneg : (0 : ℝ) = a 0 * (-(ε / 2)) + b := by
    have h2 : wf (fun _ : Fin 1 => -(ε / 2)) = g i (fun _ : Fin 1 => -(ε / 2)) :=
      hball (by
        rw [Real.dist_eq, sub_zero, abs_of_neg (by linarith : -(ε / 2) < (0:ℝ))]; linarith)
    have heq : max (0:ℝ) (-(ε / 2)) = a 0 * (-(ε / 2)) + b := by
      simpa [wf, hab, Fin.sum_univ_one] using h2
    rwa [max_eq_left (by linarith : -(ε / 2) ≤ (0:ℝ))] at heq
  rw [mul_neg] at hneg
  linarith [hb, hpos, hneg]

theorem cpwl_ne : ∃ n, Agent048.CPWL n ≠ Agent049.CPWL n := by
  refine ⟨1, fun h => wf_not_mem048 (by rw [h]; exact wf_mem049)⟩

/-! ## `relun` : proved

Both `ReLUn n k` are "at most `k` hidden layers". `Agent048.Computes` and
`Agent049.ComputesK` are the same recursion, just packaged differently
(`AffineMap` bundle vs. raw matrix/vector pair). -/

lemma eval_eq {a b : ℕ} (T : Agent048.AffineMap a b) (x : Fin a → ℝ) :
    T.eval x = T.A.mulVec x + T.c := by
  funext i
  simp [Agent048.AffineMap.eval, Matrix.mulVec, Matrix.dotProduct, Pi.add_apply]

lemma relu_eq {m : ℕ} (v : Fin m → ℝ) : Agent048.reluVec v = Agent049.reluVec v := by
  funext i
  simp [Agent048.reluVec, Agent049.reluVec, Agent049.relu]

lemma computes_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent048.Computes k n f ↔ Agent049.ComputesK n k f := by
  intro k
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨T, hT⟩
      refine ⟨T.A 0, T.c 0, ?_⟩
      funext x
      rw [hT x, eval_eq]
      simp [Matrix.mulVec, Matrix.dotProduct, Pi.add_apply]
    · rintro ⟨a, b, hab⟩
      exact ⟨⟨fun _ j => a j, fun _ => b⟩, fun x => by simp [hab, Agent048.AffineMap.eval]⟩
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, T, g, hg, hfx⟩
      refine ⟨m, T.A, T.c, g, (ih m g).mp hg, ?_⟩
      funext x
      rw [Function.comp_apply, ← eval_eq, ← relu_eq]
      exact hfx x
    · rintro ⟨m, A, c, g, hg, hfx⟩
      refine ⟨m, ⟨A, c⟩, g, (ih m g).mpr hg, ?_⟩
      intro x
      have hx := congrFun hfx x
      rw [Function.comp_apply] at hx
      rw [eval_eq, relu_eq]
      exact hx

theorem relun (n k : ℕ) : Agent048.ReLUn n k = Agent049.ReLUn n k := by
  ext f
  simp only [Agent048.ReLUn, Agent049.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k', hk', hc⟩; exact ⟨k', hk', (computes_iff k' n f).mp hc⟩
  · rintro ⟨k', hk', hc⟩; exact ⟨k', hk', (computes_iff k' n f).mpr hc⟩

/-! ## `depth` : proved

The two `depthBound` definitions are syntactically identical
(`⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1`). -/

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent048.depthBound n = Agent049.depthBound n := by
  simp [Agent048.depthBound, Agent049.depthBound]

/-! ## `statement` : sorry

`ReLUn`/`depthBound` agree between the two agents (`relun`, `depth` above),
so the right-hand sides of both `theorem2` statements denote the *same*
set `X n := Agent048.ReLUn n (depthBound n)`. One can show the `Agent048`
side of the iff, `∀ n ≥ 3, Agent048.CPWL n = X n`, is *false* outright:
`Agent048.ReLUn n 1 ⊆ X n` contains the network `x ↦ max 0 (x 0)` (a single
ReLU layer, extended to `Fin n → ℝ`), but by the `wf_not_mem048` argument
above this function is never in `Agent048.CPWL n`. That refutes the left
disjunct but does not by itself resolve the `Iff`: `False ↔ Agent049`'s
side collapses to `¬ (∀ n ≥ 3, Agent049.CPWL n = X n)`, and deciding that
is exactly the (unformalized, genuinely hard) content of Theorem 2 for
Agent049's polyhedral-subdivision `CPWL`, which is outside the scope of a
single bridge file. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent048.CPWL n = Agent048.ReLUn n (Agent048.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent049.CPWL n = Agent049.ReLUn n (Agent049.depthBound n)) := by
  sorry

end Bridge_048_049

namespace Bridge_061_062

/-!
Bridge between `Agent061` and `Agent062`.

* `depthBound` is literally the same formula (`⌈Real.logb 3 ((n:ℝ)-1)⌉₊ + 1`) in both
  files, so `depth` is `rfl`.
* `NetComputes`/`ReLUn` differ only in how an affine map is packaged: `Agent061.IsAffineMap`
  is an anonymous `∃ A c, …` while `Agent062.Affine` is the same data as a `structure`.
  We build the translation and prove `relun` by induction on the layer count.
* `CPWL` differs in *kind*: `Agent061.CPWL` requires `f` to agree with a single affine
  function on a full neighbourhood of every point ("local agreement"), while
  `Agent062.CPWL` uses a genuine finite polyhedral subdivision. The witness
  `wf x := max 0 (x 0)` (one ReLU unit) is polyhedrally piecewise-affine, hence in
  `Agent062.CPWL 1`, but it is *not* locally equal to any single affine function near
  `0` (its kink runs through every neighbourhood of `0`), so it is not in
  `Agent061.CPWL 1`. This shows the two `CPWL` predicates are not the same set, i.e.
  `Agent061`'s "local agreement" reading is too restrictive to match the paper's
  piecewise-affine functions.
-/

/-- The ReLU witness used to separate the two `CPWL` predicates. -/
private def wf : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

/-- `Agent061.IsAffineMap` and `Agent062.Affine` package exactly the same data. -/
private lemma affineMap_iff {a b : ℕ} (T : (Fin a → ℝ) → (Fin b → ℝ)) :
    Agent061.IsAffineMap T ↔ ∃ S : Agent062.Affine a b, ∀ x, T x = S.eval x := by
  constructor
  · rintro ⟨A, c, h⟩
    exact ⟨⟨A, c⟩, h⟩
  · rintro ⟨S, h⟩
    exact ⟨S.A, S.bias, h⟩

/-- `Agent061.IsAffineFn` (a scalar affine function via coefficients) matches
`Agent062`'s base-case network (an `Affine n 1` evaluated at its single output). -/
private lemma affineFn_iff {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    Agent061.IsAffineFn f ↔ ∃ T : Agent062.Affine n 1, f = fun x => T.eval x 0 := by
  constructor
  · rintro ⟨a, c, h⟩
    refine ⟨⟨Matrix.of fun _ i => a i, fun _ => c⟩, ?_⟩
    funext x
    simp only [h x, Agent062.Affine.eval, Pi.add_apply, Matrix.mulVec, Matrix.dotProduct,
      Matrix.of_apply]
  · rintro ⟨T, rfl⟩
    refine ⟨fun i => T.A 0 i, T.bias 0, fun x => ?_⟩
    simp [Agent062.Affine.eval, Pi.add_apply, Matrix.mulVec, Matrix.dotProduct]

/-- `NetComputes` agrees between the two files at every fixed layer count. -/
private lemma netComputes_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent061.NetComputes k n f ↔ Agent062.NetComputes n k f := by
  intro k
  induction k with
  | zero =>
    intro n f
    constructor
    · intro h
      obtain ⟨T, hT⟩ := (affineFn_iff f).mp h
      rw [hT]; exact Agent062.NetComputes.zero T
    · intro h
      cases h with
      | zero T => exact (affineFn_iff _).mpr ⟨T, rfl⟩
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, T, g, hT, hg, hfx⟩
      obtain ⟨S, hS⟩ := (affineMap_iff T).mp hT
      have hfeq : f = fun x => g (Agent062.reluVec (S.eval x)) := by
        funext x; rw [hfx x, hS x]
      rw [hfeq]
      exact Agent062.NetComputes.succ S g ((ih m g).mp hg)
    · intro h
      cases h with
      | succ T g hg =>
        exact ⟨_, T.eval, g, (affineMap_iff T.eval).mpr ⟨T, fun _ => rfl⟩,
          (ih _ g).mpr hg, fun _ => rfl⟩

theorem relun (n k : ℕ) : Agent061.ReLUn n k = Agent062.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨k', hk', hf⟩
    exact ⟨k', hk', (netComputes_iff k' n f).mp hf⟩
  · rintro ⟨k', hk', hf⟩
    exact ⟨k', hk', (netComputes_iff k' n f).mpr hf⟩

/-- Both files write the depth bound as the literal same expression. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent061.depthBound n = Agent062.depthBound n := rfl

theorem cpwl_ne : ∃ n, Agent061.CPWL n ≠ Agent062.CPWL n := by
  have hmem062 : wf ∈ Agent062.CPWL 1 := by
    have hS0 : Agent062.IsPolyhedron ({x : Fin 1 → ℝ | 0 ≤ x 0}) :=
      ⟨1, fun _ _ => -1, fun _ => 0, by
        ext x
        simp only [Set.mem_setOf_eq, Fin.forall_fin_one, Fin.sum_univ_one]
        constructor <;> intro h <;> linarith⟩
    have hS1 : Agent062.IsPolyhedron ({x : Fin 1 → ℝ | x 0 ≤ 0}) :=
      ⟨1, fun _ _ => 1, fun _ => 0, by
        ext x
        simp only [Set.mem_setOf_eq, Fin.forall_fin_one, Fin.sum_univ_one]
        constructor <;> intro h <;> linarith⟩
    have hg0 : Agent062.IsAffineFun (fun x : Fin 1 → ℝ => x 0) :=
      ⟨fun _ => 1, 0, fun x => by simp [Fin.sum_univ_one]⟩
    have hg1 : Agent062.IsAffineFun (fun _ : Fin 1 → ℝ => (0 : ℝ)) :=
      ⟨fun _ => 0, 0, fun x => by simp [Fin.sum_univ_one]⟩
    refine ⟨continuous_const.max (continuous_apply 0), 2,
      ![{x : Fin 1 → ℝ | 0 ≤ x 0}, {x : Fin 1 → ℝ | x 0 ≤ 0}],
      ![fun x : Fin 1 → ℝ => x 0, fun _ : Fin 1 → ℝ => (0 : ℝ)], ?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i
      · simpa using hS0
      · simpa using hS1
    · intro i; fin_cases i
      · simpa using hg0
      · simpa using hg1
    · rw [Set.eq_univ_iff_forall]
      intro x
      rcases le_total (x 0) 0 with h | h
      · exact Set.mem_iUnion.mpr ⟨1, by simpa using h⟩
      · exact Set.mem_iUnion.mpr ⟨0, by simpa using h⟩
    · intro i x hx
      fin_cases i
      · simp only [Matrix.cons_val_zero, Set.mem_setOf_eq] at hx
        simp only [wf, Matrix.cons_val_zero]
        exact max_eq_right_iff.mpr hx
      · simp only [Matrix.cons_val_one, Matrix.head_cons, Set.mem_setOf_eq] at hx
        simp only [wf, Matrix.cons_val_one, Matrix.head_cons]
        exact max_eq_left_iff.mpr hx
  have hnotmem061 : wf ∉ Agent061.CPWL 1 := by
    rintro ⟨-, S, hSaff, hSloc⟩
    obtain ⟨h0, h0mem, h0event⟩ := hSloc (fun _ => (0 : ℝ))
    obtain ⟨a, c, hac⟩ := hSaff h0mem
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp h0event
    have hac0 : ∀ t : ℝ, h0 (fun _ : Fin 1 => t) = a 0 * t + c := by
      intro t; rw [hac]; simp [Fin.sum_univ_one]
    have hmem : ∀ t : ℝ, |t| < ε → wf (fun _ : Fin 1 => t) = h0 (fun _ : Fin 1 => t) := by
      intro t ht
      refine hball ?_
      simp only [dist_pi_lt_iff hε, Fin.forall_fin_one]
      show dist t (0 : ℝ) < ε
      rwa [Real.dist_eq, sub_zero]
    have hmax1 : wf (fun _ : Fin 1 => (ε / 2 : ℝ)) = ε / 2 :=
      max_eq_right_iff.mpr (by linarith)
    have hmax2 : wf (fun _ : Fin 1 => (ε / 4 : ℝ)) = ε / 4 :=
      max_eq_right_iff.mpr (by linarith)
    have hmax3 : wf (fun _ : Fin 1 => (-(ε / 2) : ℝ)) = 0 :=
      max_eq_left_iff.mpr (by linarith)
    have heq1 := hmem (ε / 2) (by rw [abs_of_pos (show (0:ℝ) < ε / 2 by linarith)]; linarith)
    have heq2 := hmem (ε / 4) (by rw [abs_of_pos (show (0:ℝ) < ε / 4 by linarith)]; linarith)
    have heq3 := hmem (-(ε / 2))
      (by rw [abs_neg, abs_of_pos (show (0:ℝ) < ε / 2 by linarith)]; linarith)
    have eq1 : (ε / 2 : ℝ) = a 0 * (ε / 2) + c := by rw [← hac0, ← hmax1]; exact heq1
    have eq2 : (ε / 4 : ℝ) = a 0 * (ε / 4) + c := by rw [← hac0, ← hmax2]; exact heq2
    have eq3 : (0 : ℝ) = a 0 * (-(ε / 2)) + c := by rw [← hac0, ← hmax3]; exact heq3
    have hp1 : a 0 * (ε / 2) = a 0 * ε / 2 := by ring
    have hp2 : a 0 * (ε / 4) = a 0 * ε / 4 := by ring
    have hp3 : a 0 * (-(ε / 2)) = -(a 0 * ε) / 2 := by ring
    rw [hp1] at eq1; rw [hp2] at eq2; rw [hp3] at eq3
    linarith
  refine ⟨1, fun hEq => hnotmem061 ?_⟩
  rw [hEq]; exact hmem062

/- `statement`: the LHS (`Agent061`'s own claim) is in fact *false* for every `n ≥ 3` by
the same argument as `cpwl_ne` (the witness `x ↦ max 0 (x 0)` on `ℝ^n` is a one-layer
ReLU network, hence in `Agent061.ReLUn n (depthBound n)` since `depthBound n ≥ 1`, but
is not in `Agent061.CPWL n` by the neighbourhood argument above). Resolving the iff
would then require deciding the truth of the RHS, i.e. of Theorem 2 itself for
`Agent062`'s (faithful) polyhedral encoding — the actual hard theorem of the paper,
which is out of scope for a bridge proof. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent061.CPWL n = Agent061.ReLUn n (Agent061.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent062.CPWL n = Agent062.ReLUn n (Agent062.depthBound n)) := by
  sorry

end Bridge_061_062

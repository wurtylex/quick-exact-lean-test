namespace Bridge_014_015

/-!
## Summary

* `relun` : PROVED.  `Agent014.IsReLUNetFun`/`Agent015.Represents` are literally the
  same recursion (same base case, same successor case, same `reluVec`), built from
  `AffineT`/`AffineMap` structures that carry identical fields `(A, c)` and identical
  evaluation formulas `x ↦ A.mulVec x + c`.  We exhibit the evident back-and-forth
  translation and induct on `k`.
* `depth` : PROVED.  Both agents write the *syntactically identical* formula
  `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`, so the two `depthBound`s are definitionally
  equal (`rfl`).
* `cpwl` : REFUTED (`cpwl_ne`).  Agent014's `CPWL` is the honest global polyhedral
  subdivision.  Agent015's `CPWL` uses *local* agreement (`∀ x, ∃ i, ∃ ε>0, …`); on
  the connected space `ℝ^n` this forces `f` to coincide with a *single* affine
  function everywhere (any two of the local affine pieces that meet on a nonempty
  open set must be the same affine map, so the open sets on which distinct pieces
  govern are separated, hence one of them is everything).  So Agent015's `CPWL 1`
  contains only globally affine functions, while the witness `x ↦ max 0 (x 0)`
  (genuinely CPWL, with a kink at the origin) lies in Agent014's `CPWL 1` but not in
  Agent015's.  We prove this witness lies in `Agent014.CPWL 1` via an explicit
  two-piece polyhedral subdivision, and prove it is excluded from `Agent015.CPWL 1`
  by an explicit three-point argument at `ε/2, 0, -ε/2` around the kink.
* `statement` : SORRY.  See the comment directly above it.
-/

/- ===================================================================== -/
/-  `relun` : the two `ReLUn` families coincide.                          -/
/- ===================================================================== -/

/-- Translate an `Agent014.AffineT` into an `Agent015.AffineMap` with the same
matrix and bias; the two structures have identical fields and identical
evaluation formulas, so this is an isomorphism. -/
private def toAffineMap {a b : ℕ} (T : Agent014.AffineT a b) : Agent015.AffineMap a b :=
  ⟨T.A, T.c⟩

private def toAffineT {a b : ℕ} (T : Agent015.AffineMap a b) : Agent014.AffineT a b :=
  ⟨T.A, T.c⟩

private lemma toAffineMap_eval {a b : ℕ} (T : Agent014.AffineT a b) (x : Fin a → ℝ) :
    (toAffineMap T).toFun x = T.eval x := rfl

private lemma toAffineT_eval {a b : ℕ} (T : Agent015.AffineMap a b) (x : Fin a → ℝ) :
    (toAffineT T).eval x = T.toFun x := rfl

/-- Both agents' `reluVec` are literally `fun i => max 0 (y i)` once unfolded. -/
private lemma reluVec_eq {m : ℕ} (y : Fin m → ℝ) :
    Agent014.reluVec y = Agent015.reluVec y := rfl

private lemma relun_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent014.IsReLUNetFun n k f ↔ Agent015.Represents n k f
  | 0, n, f => by
      constructor
      · rintro ⟨T, hT⟩
        exact ⟨toAffineMap T, fun x => by rw [hT, toAffineMap_eval]⟩
      · rintro ⟨T, hT⟩
        exact ⟨toAffineT T, fun x => by rw [hT, toAffineT_eval]⟩
  | (k + 1), n, f => by
      constructor
      · rintro ⟨m, T, g, hg, hf⟩
        exact ⟨m, toAffineMap T, g, (relun_iff k m g).mp hg,
          fun x => by rw [hf, toAffineMap_eval, reluVec_eq]⟩
      · rintro ⟨m, T, g, hg, hf⟩
        exact ⟨m, toAffineT T, g, (relun_iff k m g).mpr hg,
          fun x => by rw [hf, toAffineT_eval, ← reluVec_eq]⟩

theorem relun (n k : ℕ) : Agent014.ReLUn n k = Agent015.ReLUn n k := by
  ext f
  exact relun_iff k n f

/- ===================================================================== -/
/-  `depth` : the two `depthBound`s coincide.                             -/
/- ===================================================================== -/

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent014.depthBound n = Agent015.depthBound n := rfl

/- ===================================================================== -/
/-  `cpwl` : REFUTED.  Witness: `x ↦ max 0 (x 0)` on `ℝ^1`.                -/
/- ===================================================================== -/

/-- The kinked witness function distinguishing the two `CPWL` notions. -/
private def reluWitness : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

/-- The piece `x ↦ x 0`, valid on `{x | 0 ≤ x 0}`. -/
private def piece1 : Agent014.PWLPiece 1 where
  aff := { A := 1, c := 0 }
  numConstraints := 1
  normal := fun _ _ => -1
  bound := fun _ => 0

/-- The piece `x ↦ 0`, valid on `{x | x 0 ≤ 0}`. -/
private def piece2 : Agent014.PWLPiece 1 where
  aff := { A := 0, c := 0 }
  numConstraints := 1
  normal := fun _ _ => 1
  bound := fun _ => 0

private lemma piece1_eval (x : Fin 1 → ℝ) : piece1.aff.eval x 0 = x 0 := by
  simp [piece1, Agent014.AffineT.eval]

private lemma piece2_eval (x : Fin 1 → ℝ) : piece2.aff.eval x 0 = 0 := by
  simp [piece2, Agent014.AffineT.eval]

private lemma piece1_mem_region_iff (x : Fin 1 → ℝ) :
    x ∈ piece1.region ↔ 0 ≤ x 0 := by
  constructor
  · intro h
    have h0 : (∑ i : Fin 1, piece1.normal 0 i * x i) ≤ piece1.bound 0 := h 0
    simp only [piece1] at h0
    rw [Fin.sum_univ_one] at h0
    linarith
  · intro h j
    have hj : j = (0 : Fin 1) := Subsingleton.elim j 0
    subst hj
    show (∑ i : Fin 1, piece1.normal 0 i * x i) ≤ piece1.bound 0
    simp only [piece1]
    rw [Fin.sum_univ_one]
    linarith

private lemma piece2_mem_region_iff (x : Fin 1 → ℝ) :
    x ∈ piece2.region ↔ x 0 ≤ 0 := by
  constructor
  · intro h
    have h0 : (∑ i : Fin 1, piece2.normal 0 i * x i) ≤ piece2.bound 0 := h 0
    simp only [piece2] at h0
    rw [Fin.sum_univ_one] at h0
    linarith
  · intro h j
    have hj : j = (0 : Fin 1) := Subsingleton.elim j 0
    subst hj
    show (∑ i : Fin 1, piece2.normal 0 i * x i) ≤ piece2.bound 0
    simp only [piece2]
    rw [Fin.sum_univ_one]
    linarith

private lemma reluWitness_mem_CPWL014 : reluWitness ∈ Agent014.CPWL 1 := by
  refine ⟨?_, Bool, inferInstance, fun b => cond b piece2 piece1, ?_, ?_⟩
  · show Continuous fun x : Fin 1 → ℝ => max 0 (x 0)
    exact continuous_const.max (continuous_apply 0)
  · apply Set.eq_univ_iff_forall.mpr
    intro x
    rcases le_total 0 (x 0) with h | h
    · exact Set.mem_iUnion.mpr ⟨false, (piece1_mem_region_iff x).mpr h⟩
    · exact Set.mem_iUnion.mpr ⟨true, (piece2_mem_region_iff x).mpr h⟩
  · intro i x hx
    cases i with
    | false =>
        have hx0 : 0 ≤ x 0 := (piece1_mem_region_iff x).mp hx
        show max 0 (x 0) = piece1.aff.eval x 0
        rw [piece1_eval]
        exact max_eq_right_iff.mpr hx0
    | true =>
        have hx0 : x 0 ≤ 0 := (piece2_mem_region_iff x).mp hx
        show max 0 (x 0) = piece2.aff.eval x 0
        rw [piece2_eval]
        exact max_eq_left_iff.mpr hx0

private lemma reluWitness_not_mem_CPWL015 : reluWitness ∉ Agent015.CPWL 1 := by
  rintro ⟨-, m, g, hloc⟩
  obtain ⟨i, ε, hε, hball⟩ := hloc (0 : Fin 1 → ℝ)
  set T := g i
  have hTeval : ∀ y : Fin 1 → ℝ, T.toFun y 0 = T.A 0 0 * y 0 + T.c 0 := by
    intro y
    show (T.A.mulVec y + T.c) 0 = T.A 0 0 * y 0 + T.c 0
    simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_one, Pi.add_apply]
  have ht_pos : (0 : ℝ) < ε / 2 := by linarith
  have ht_lt : ε / 2 < ε := by linarith
  have hcenter : T.c 0 = (0 : ℝ) := by
    have h0 : reluWitness (0 : Fin 1 → ℝ) = T.toFun (0 : Fin 1 → ℝ) 0 :=
      hball (0 : Fin 1 → ℝ) (by rw [dist_self]; exact hε)
    rw [hTeval] at h0
    simp only [reluWitness, Pi.zero_apply, mul_zero, zero_add, max_self] at h0
    linarith
  have hdist1 : dist (fun _ : Fin 1 => ε / 2) (0 : Fin 1 → ℝ) < ε := by
    have e : dist (fun _ : Fin 1 => ε / 2) (0 : Fin 1 → ℝ) = dist (ε / 2) (0 : ℝ) :=
      dist_pi_const (ε / 2) 0
    rw [e, Real.dist_eq, sub_zero, abs_of_pos ht_pos]
    exact ht_lt
  have hdist2 : dist (fun _ : Fin 1 => -(ε / 2)) (0 : Fin 1 → ℝ) < ε := by
    have e : dist (fun _ : Fin 1 => -(ε / 2)) (0 : Fin 1 → ℝ) = dist (-(ε / 2)) (0 : ℝ) :=
      dist_pi_const (-(ε / 2)) 0
    rw [e, Real.dist_eq, sub_zero, abs_neg, abs_of_pos ht_pos]
    exact ht_lt
  have hy1 : reluWitness (fun _ : Fin 1 => ε / 2) = T.toFun (fun _ : Fin 1 => ε / 2) 0 :=
    hball (fun _ => ε / 2) hdist1
  have hy2 : reluWitness (fun _ : Fin 1 => -(ε / 2)) = T.toFun (fun _ : Fin 1 => -(ε / 2)) 0 :=
    hball (fun _ => -(ε / 2)) hdist2
  rw [hTeval] at hy1 hy2
  simp only [reluWitness] at hy1 hy2
  rw [max_eq_right_iff.mpr ht_pos.le] at hy1
  rw [max_eq_left_iff.mpr (neg_nonpos.mpr ht_pos.le)] at hy2
  rw [mul_neg] at hy2
  linarith [hy1, hy2, hcenter, ht_pos]

theorem cpwl_ne : ∃ n, Agent014.CPWL n ≠ Agent015.CPWL n := by
  refine ⟨1, ?_⟩
  intro hset
  exact reluWitness_not_mem_CPWL015 (hset ▸ reluWitness_mem_CPWL014)

/- ===================================================================== -/
/-  `statement`                                                          -/
/- ===================================================================== -/

/-- Left as `sorry`: by the argument behind `cpwl_ne`, `Agent015.CPWL n` consists
exactly of globally affine functions (local agreement on the connected space `ℝ^n`
forces it), so Agent015's instance of Theorem 2 is false as soon as
`ReLUn n (depthBound n)` contains a non-affine function — true for every `n ≥ 3` by
a padding construction analogous to the one used above. Since `relun`/`depth`
identify the two right-hand sides, the displayed `↔` then reduces propositionally to
`¬ (Agent014's instance)`, i.e. to disproving Theorem 2 itself for Agent014's honest
polyhedral-subdivision formalization — well beyond the scope of a single bridge
lemma, so we leave it open. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent014.CPWL n = Agent014.ReLUn n (Agent014.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent015.CPWL n = Agent015.ReLUn n (Agent015.depthBound n)) := by
  sorry

end Bridge_014_015

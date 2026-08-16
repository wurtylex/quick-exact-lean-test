namespace Bridge_008_009

/-!
## Comparing `Agent008` and `Agent009`

Both agents represent affine maps `ℝ^a → ℝ^b` explicitly by a matrix and bias vector
(`Agent008.AffineMap'` vs. `Agent009.IsAffineMap`), both take `ReLUn n k` to mean "at
most `k` hidden layers", and both write `depthBound` via `Real.logb 3` and `Nat.ceil`
(one applies the cast before subtracting, the other after). These three pieces turn out
to be genuinely the same mathematical objects, just packaged differently, and we prove
`relun` and `depth` below.

`CPWL`, however, differs in kind: `Agent008.CPWL` is the standard *polyhedral
subdivision* reading (finitely many polyhedral pieces covering `ℝ^n`, `f` affine on
each), while `Agent009.CPWL` uses the *local agreement* reading
`∀ x, ∃ i, ∀ᶠ y in nhds x, f y = g i y` for a single finite family of *globally defined*
affine functionals `g`. On the connected space `ℝ^n`, this local-agreement condition is
far more restrictive than it looks: at a genuine kink (e.g. `x ↦ max 0 (x 0)` at the
origin), *no* single affine functional can agree with `f` on a whole neighbourhood, since
the two sides of the kink are governed by different affine formulas. So
`Agent009.CPWL n` cannot contain any function with an actual crease — concretely,
`fun x => max 0 (x 0)` lies in `Agent008.CPWL 1` (it is honestly piecewise affine) but not
in `Agent009.CPWL 1`. This is the refutation `cpwl_ne` below.
-/

/-! ### `relun`: the two `ReLUn` families coincide -/

/-- `Agent008`'s affine map `T.apply` unfolds to the same explicit weighted-sum-plus-bias
formula used by `Agent009.IsAffineMap` / `Agent009.IsAffineFunctional`. -/
private lemma affineMap'_apply_eq {a b : ℕ} (T : Agent008.AffineMap' a b) (x : Fin a → ℝ)
    (i : Fin b) : T.apply x i = (∑ j, T.A i j * x j) + T.c i := by
  simp only [Agent008.AffineMap'.apply, Pi.add_apply, Matrix.mulVec, Matrix.dotProduct]

/-- Every `Agent008.AffineMap'` gives an `Agent009.IsAffineMap`. -/
private lemma affineMap_isAffineMap {a b : ℕ} (T : Agent008.AffineMap' a b) :
    Agent009.IsAffineMap a b T.apply :=
  ⟨T.A, T.c, fun x i => affineMap'_apply_eq T x i⟩

/-- Conversely every `Agent009.IsAffineMap` function is (extensionally) an
`Agent008.AffineMap'`. -/
private lemma isAffineMap_to_affineMap' {a b : ℕ} {T : (Fin a → ℝ) → (Fin b → ℝ)}
    (h : Agent009.IsAffineMap a b T) : ∃ S : Agent008.AffineMap' a b, ∀ x, T x = S.apply x := by
  obtain ⟨A, c, hT⟩ := h
  refine ⟨⟨A, c⟩, fun x => funext fun i => ?_⟩
  exact (hT x i).trans (affineMap'_apply_eq ⟨A, c⟩ x i).symm

/-- The `b = 1` (affine *functional*) special case of the previous two lemmas. -/
private lemma affineFunctional_iff (n : ℕ) (f : (Fin n → ℝ) → ℝ) :
    Agent009.IsAffineFunctional n f ↔ ∃ T : Agent008.AffineMap' n 1, ∀ x, f x = T.apply x 0 := by
  constructor
  · rintro ⟨a, c, hf⟩
    refine ⟨⟨Matrix.of (fun (_ : Fin 1) j => a j), fun _ => c⟩, fun x => ?_⟩
    have h := affineMap'_apply_eq
      (⟨Matrix.of (fun (_ : Fin 1) j => a j), fun _ => c⟩ : Agent008.AffineMap' n 1) x 0
    simp only [Matrix.of_apply] at h
    rw [hf x, h]
  · rintro ⟨T, hf⟩
    refine ⟨fun j => T.A 0 j, T.c 0, fun x => ?_⟩
    rw [hf x, affineMap'_apply_eq T x 0]

/-- Both `x ↦ reluVec x` definitions ("componentwise `max 0 (x i)`") are literally the
same function, so no lemma is even needed to swap between the two agents' networks — this
is recorded only for documentation, the equality below holds by `rfl`. -/
private lemma reluVec_eq {m : ℕ} (x : Fin m → ℝ) : Agent008.reluVec x = Agent009.reluVec x :=
  rfl

/-- `Agent008.NetworkComputes n k f` (exactly `k` hidden layers, via an inductive
relation unwinding the alternating composition) and `Agent009.ComputesWithHiddenLayers k n f`
(the same thing, defined by recursion on `k`) pick out the same functions. -/
private lemma networkComputes_iff :
    ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
      Agent008.NetworkComputes n k f ↔ Agent009.ComputesWithHiddenLayers k n f := by
  intro k
  induction k with
  | zero =>
    intro n f
    constructor
    · intro h
      cases h with
      | base T => exact (affineFunctional_iff n (fun x => T.apply x 0)).mpr ⟨T, fun x => rfl⟩
    · intro h
      obtain ⟨T, hT⟩ := (affineFunctional_iff n f).mp h
      have hfe : f = fun x => T.apply x 0 := funext hT
      rw [hfe]
      exact Agent008.NetworkComputes.base T
  | succ k ih =>
    intro n f
    constructor
    · intro h
      cases h with
      | step T hg => exact ⟨_, T.apply, _, affineMap_isAffineMap T, (ih _ _).mp hg, fun x => rfl⟩
    · intro h
      obtain ⟨m, Tf, g, hAff, hg, hf⟩ := h
      obtain ⟨S, hS⟩ := isAffineMap_to_affineMap' hAff
      have hfe : f = fun x => g (Agent008.reluVec (S.apply x)) := by
        funext x
        rw [hf x, hS x]
      rw [hfe]
      exact Agent008.NetworkComputes.step S ((ih _ _).mpr hg)

theorem relun (n k : ℕ) : Agent008.ReLUn n k = Agent009.ReLUn n k := by
  ext f
  simp only [Agent008.ReLUn, Agent009.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hjk, hj⟩
    exact ⟨j, hjk, (networkComputes_iff j n f).mp hj⟩
  · rintro ⟨j, hjk, hj⟩
    exact ⟨j, hjk, (networkComputes_iff j n f).mpr hj⟩

/-! ### `depth`: the two depth bounds agree for `n ≥ 3` -/

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent008.depthBound n = Agent009.depthBound n := by
  have h1 : (1 : ℕ) ≤ n := by omega
  simp only [Agent008.depthBound, Agent009.depthBound, Nat.cast_sub h1, Nat.cast_one]

/-! ### `cpwl_ne`: the two `CPWL` definitions genuinely differ -/

/-- Our witness: the one-dimensional ReLU, as a function of `Fin 1 → ℝ`. It is honestly
piecewise affine (`Agent008.CPWL`) but has a genuine kink at `0`, so it fails Agent009's
"agrees with a single affine functional on a whole neighbourhood of every point" reading. -/
private def wf : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

private lemma wf_continuous : Continuous wf :=
  continuous_const.max (continuous_apply 0)

private def P0 : Set (Fin 1 → ℝ) := {x | x 0 ≤ 0}
private def P1 : Set (Fin 1 → ℝ) := {x | 0 ≤ x 0}

private lemma pi_fin_one_le_iff {y z : Fin 1 → ℝ} : y ≤ z ↔ y 0 ≤ z 0 := by
  rw [Pi.le_def]
  exact ⟨fun h => h 0, fun h i => by rw [Fin.eq_zero i]; exact h⟩

private lemma P0_isPolyhedron : Agent008.IsPolyhedron P0 := by
  refine ⟨1, Matrix.of (fun (_ _ : Fin 1) => (1 : ℝ)), fun _ => 0, ?_⟩
  ext x
  simp only [P0, Set.mem_setOf_eq, pi_fin_one_le_iff, Matrix.mulVec, Matrix.dotProduct,
    Matrix.of_apply, Fin.sum_univ_one, one_mul]

private lemma P1_isPolyhedron : Agent008.IsPolyhedron P1 := by
  refine ⟨1, Matrix.of (fun (_ _ : Fin 1) => (-1 : ℝ)), fun _ => 0, ?_⟩
  ext x
  simp only [P1, Set.mem_setOf_eq, pi_fin_one_le_iff, Matrix.mulVec, Matrix.dotProduct,
    Matrix.of_apply, Fin.sum_univ_one]
  constructor <;> intro h <;> linarith

private lemma P_cover : (⋃ i, (![P0, P1] : Fin 2 → Set (Fin 1 → ℝ)) i) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  rcases le_or_lt (x 0) 0 with h | h
  · exact ⟨0, by simpa [P0] using h⟩
  · exact ⟨1, by simpa [P1] using h.le⟩

private def T0 : Agent008.AffineMap' 1 1 := ⟨Matrix.of (fun (_ _ : Fin 1) => (0 : ℝ)), fun _ => 0⟩
private def T1 : Agent008.AffineMap' 1 1 := ⟨Matrix.of (fun (_ _ : Fin 1) => (1 : ℝ)), fun _ => 0⟩

private lemma T0_apply (x : Fin 1 → ℝ) : T0.apply x 0 = 0 := by
  rw [affineMap'_apply_eq]
  simp [T0, Matrix.of_apply, Fin.sum_univ_one]

private lemma T1_apply (x : Fin 1 → ℝ) : T1.apply x 0 = x 0 := by
  rw [affineMap'_apply_eq]
  simp [T1, Matrix.of_apply, Fin.sum_univ_one]

private lemma wf_mem_008 : wf ∈ Agent008.CPWL 1 := by
  refine ⟨wf_continuous, 2, (![P0, P1] : Fin 2 → Set (Fin 1 → ℝ)), ![T0, T1], ?_, P_cover, ?_⟩
  · intro i
    fin_cases i
    · exact P0_isPolyhedron
    · exact P1_isPolyhedron
  · intro i x hx
    fin_cases i
    · have hx0 : x 0 ≤ 0 := by simpa [P0] using hx
      simp only [wf, Matrix.cons_val_zero]
      rw [max_eq_left_iff.mpr hx0, T0_apply]
    · have hx0 : 0 ≤ x 0 := by simpa [P1] using hx
      simp only [wf, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [max_eq_right_iff.mpr hx0, T1_apply]

/-- At the origin, no single globally-affine `g i` can agree with `wf` on a whole
neighbourhood: three points inside any candidate ball (`ε/3`, `2ε/3`, `-ε/3`) force
`a 0 = 1/2` from one pair of equations and `a 0 = 2/3` from another. -/
private lemma wf_not_mem_009 : wf ∉ Agent009.CPWL 1 := by
  rintro ⟨-, m, g, hg, hloc⟩
  obtain ⟨i, hi⟩ := hloc (fun _ => (0 : ℝ))
  obtain ⟨a, c, hgi⟩ := hg i
  have hcont : Continuous (fun (t : ℝ) (_ : Fin 1) => t) := continuous_pi (fun _ => continuous_id)
  have hev : ∀ᶠ t in nhds (0 : ℝ), wf (fun _ => t) = g i (fun _ => t) :=
    (hcont.tendsto 0).eventually hi
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hη : (0 : ℝ) < ε / 3 := by linarith
  have d1 : dist (ε / 3) (0 : ℝ) < ε := by
    rw [Real.dist_0_eq_abs, abs_of_pos hη]; linarith
  have d2 : dist (2 * (ε / 3)) (0 : ℝ) < ε := by
    rw [Real.dist_0_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < 2 * (ε / 3))]; linarith
  have d3 : dist (-(ε / 3)) (0 : ℝ) < ε := by
    rw [Real.dist_0_eq_abs, abs_of_neg (by linarith : -(ε / 3) < (0 : ℝ))]; linarith
  have e1 := hball d1
  have e2 := hball d2
  have e3 := hball d3
  simp only [wf, hgi, Fin.sum_univ_one] at e1 e2 e3
  rw [max_eq_right_iff.mpr hη.le] at e1
  rw [max_eq_right_iff.mpr (by linarith : (0 : ℝ) ≤ 2 * (ε / 3))] at e2
  rw [max_eq_left_iff.mpr (by linarith : -(ε / 3) ≤ (0 : ℝ))] at e3
  have hcontra : ε / 3 = 0 := by linear_combination -3 * e1 + 2 * e2 + e3
  linarith

theorem cpwl_ne : ∃ n, Agent008.CPWL n ≠ Agent009.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  apply wf_not_mem_009
  rw [← h]
  exact wf_mem_008

/-! ### `statement` -/

/-
We can settle the RHS alone: by the same argument as `cpwl_ne` (transported from `n = 1`
to `n = 3`, using the coordinate slice `t ↦ fun i => if i = 0 then t else 0`), `wf`-like
functions witness `Agent009.CPWL 3 ≠ Agent009.ReLUn 3 (Agent009.depthBound 3)`, so the RHS
`∀ n, 3 ≤ n → Agent009.CPWL n = Agent009.ReLUn n (Agent009.depthBound n)` is false.

But `Agent008.CPWL`/`Agent008.ReLUn` are the standard, faithful renderings of the paper's
definitions (matching family (a) and the natural "at most k" reading), so the LHS is
essentially a restatement of the paper's actual Theorem 2 — a genuine, hard theorem that
is not proved anywhere in `Thm2_008.lean` (its own `theorem2` is `sorry`) and whose proof
or disproof is far outside the scope of a bridge file. Since the RHS is false, resolving
the `↔` requires deciding the LHS outright (true ↔ `False` is `¬LHS`, i.e. we would need
to *refute* Agent008's Theorem 2, which we have no reason to believe is actually false —
only that we cannot prove it true here). So neither `PROVED` nor `REFUTED` is honest.
-/
theorem statement :
    (∀ n, 3 ≤ n → Agent008.CPWL n = Agent008.ReLUn n (Agent008.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent009.CPWL n = Agent009.ReLUn n (Agent009.depthBound n)) := by
  sorry

end Bridge_008_009

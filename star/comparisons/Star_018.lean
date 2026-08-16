namespace Star_018

/-!
# Star comparison: `Agent018` vs `Ref`

* `depthBound` : *identical* term (`⌈·⌉₊` is notation for `Nat.ceil`), so `depth` is `rfl`.
* `ReLUn`      : both files mean **at most `k`** hidden layers.  `Ref` uses a structural
  recursion `ComputedBy`, `Agent018` an inductive *type* `ReLUNet` of networks; the two
  are equivalent by a routine induction, so `relun` is proved outright — no padding
  identity is needed.
* `CPWL`       : `Agent018` asks that `f` agree with one of finitely many affine maps on a
  *neighbourhood* of every point.  On connected `ℝⁿ` that forces `f` to be globally affine,
  so it is strictly stronger than the reference's polyhedral-cover definition.  Hence
  `cpwl` is false (`cpwl_ne`) and, better, the `Agent018` reading of Theorem 2 is itself
  false (`agent_side_false`): `relu` of a coordinate is a one-hidden-layer network.
-/

/-! ### `ReLUn` -/

/-- Every `Agent018` network computes a function that `Ref.ComputedBy` recognises. -/
private lemma computedBy_of_net : ∀ {n k : ℕ} (N : Agent018.ReLUNet n k),
    Ref.ComputedBy n k N.eval := by
  intro n k N
  induction N with
  | output T => exact ⟨⟨T.A, T.c⟩, fun _ => rfl⟩
  | @layer n m k T rest ih => exact ⟨m, ⟨T.A, T.c⟩, rest.eval, ih, fun _ => rfl⟩

/-- Conversely, every `Ref.ComputedBy` function is computed by an `Agent018` network. -/
private lemma net_of_computedBy : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Ref.ComputedBy n k f → ∃ N : Agent018.ReLUNet n k, f = N.eval := by
  intro k
  induction k with
  | zero =>
    intro n f hf
    obtain ⟨T, hT⟩ : ∃ T : Ref.Aff n 1, ∀ x, f x = T.eval x 0 := hf
    exact ⟨Agent018.ReLUNet.output ⟨T.M, T.c⟩, funext fun x => hT x⟩
  | succ k ih =>
    intro n f hf
    obtain ⟨m, T, g, hg, hfx⟩ : ∃ (m : ℕ) (T : Ref.Aff n m) (g : (Fin m → ℝ) → ℝ),
        Ref.ComputedBy m k g ∧ ∀ x, f x = g (Ref.reluVec (T.eval x)) := hf
    obtain ⟨N, hN⟩ := ih m g hg
    refine ⟨Agent018.ReLUNet.layer ⟨T.M, T.c⟩ N, funext fun x => ?_⟩
    rw [hfx x, hN]
    rfl

/-- The two `ReLUn`s agree: both mean "at most `k` hidden layers". -/
theorem relun (n k : ℕ) : Agent018.ReLUn n k = Ref.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨j, hj, N, rfl⟩
    exact ⟨j, hj, computedBy_of_net N⟩
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, net_of_computedBy j n f h⟩

/-! ### `depthBound` -/

/-- Both files write `⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1`, character for character. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent018.depthBound n = Ref.depthBound n := rfl

/-! ### `CPWL` : neighbourhood agreement is strictly stronger -/

/-- `relu` is not affine on any neighbourhood of `0`. -/
private lemma no_affine_relu {A B ε : ℝ} (hε : 0 < ε)
    (h : ∀ t : ℝ, |t| < ε → max 0 t = A * t + B) : False := by
  have h0 := h 0 (by simpa using hε)
  have h1 := h (ε / 2) (by rw [abs_of_pos] <;> linarith)
  have h2 := h (-(ε / 2)) (by rw [abs_of_neg] <;> linarith)
  rw [max_self] at h0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ ε / 2)] at h1
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0 : ℝ))] at h2
  nlinarith [h0, h1, h2]

/-- `x ↦ max 0 (x 0)` is *not* in `Agent018.CPWL`: agreement with a single affine map on a
neighbourhood of the origin makes `max 0 t` affine for all small `t`, which is absurd. -/
private lemma max_not_mem (n : ℕ) :
    (fun x : Fin (n + 1) → ℝ => max 0 (x 0)) ∉ Agent018.CPWL (n + 1) := by
  rintro ⟨-, m, g, h⟩
  obtain ⟨i, hi⟩ := h 0
  have hc : Continuous (fun t : ℝ => (fun _ => t : Fin (n + 1) → ℝ)) :=
    continuous_pi fun _ => continuous_id
  have key : ∀ᶠ t : ℝ in nhds (0 : ℝ),
      max 0 t = (∑ j, (g i).a j) * t + (g i).b := by
    filter_upwards [(hc.tendsto' 0 0 rfl).eventually hi] with t ht
    simpa [Agent018.ScalarAffine.eval, Finset.sum_mul] using ht
  rw [Metric.eventually_nhds_iff] at key
  obtain ⟨ε, hε, hkey⟩ := key
  exact no_affine_relu hε fun t ht => hkey (by simpa [Real.dist_eq] using ht)

/-- Every halfspace is a polyhedron (the intersection of the one-element family). -/
private lemma poly_of_half {n : ℕ} {S : Set (Fin n → ℝ)} (h : Ref.IsHalfspace n S) :
    Ref.IsPolyhedron n S :=
  ⟨1, fun _ => S, fun _ => h, by rw [Set.iInter_const]⟩

/-- `x ↦ max 0 (x 0)` *is* CPWL in the reference sense: two halflines cover `ℝ`. -/
private lemma max_mem_ref : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Ref.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2,
    ![{x : Fin 1 → ℝ | ∑ j, (1 : ℝ) * x j ≤ 0}, {x : Fin 1 → ℝ | ∑ j, (-1 : ℝ) * x j ≤ 0}],
    ![fun _ => 0, fun x => x 0], ?_, ?_, ?_, ?_⟩
  · exact Fin.forall_fin_two.2 ⟨poly_of_half ⟨fun _ => 1, 0, rfl⟩,
      poly_of_half ⟨fun _ => -1, 0, rfl⟩⟩
  · exact Fin.forall_fin_two.2 ⟨⟨0, 0, by simp⟩, ⟨fun _ => 1, 0, by simp⟩⟩
  · refine Set.eq_univ_of_forall fun x => ?_
    rcases le_or_gt (x 0) 0 with hx | hx
    · refine Set.mem_iUnion.2 ⟨0, ?_⟩
      simp only [Matrix.cons_val_zero, Set.mem_setOf_eq, Fin.sum_univ_one, one_mul]
      linarith
    · refine Set.mem_iUnion.2 ⟨1, ?_⟩
      simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, Set.mem_setOf_eq,
        Fin.sum_univ_one, neg_mul, one_mul]
      linarith
  · refine Fin.forall_fin_two.2 ⟨fun x hx => ?_, fun x hx => ?_⟩
    · simp only [Matrix.cons_val_zero, Set.mem_setOf_eq, Fin.sum_univ_one, one_mul] at hx ⊢
      exact max_eq_left (by linarith)
    · simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, Set.mem_setOf_eq,
        Fin.sum_univ_one, neg_mul, one_mul] at hx ⊢
      exact max_eq_right (by linarith)

/-- `Agent018.CPWL` is strictly stronger than `Ref.CPWL`, so the two differ. -/
theorem cpwl_ne : ∃ n, Agent018.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  have hmem : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent018.CPWL 1 := by
    rw [h]; exact max_mem_ref
  exact max_not_mem 0 hmem

/-! ### The `Agent018` reading of Theorem 2 is outright false -/

/-- `max 0 (x 0)` on `ℝ³` is a one-hidden-layer network, hence in `Agent018.ReLUn 3 _`. -/
private lemma relu3_mem :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent018.ReLUn 3 (Agent018.depthBound 3) := by
  refine ⟨1, Nat.le_add_left 1 _,
    Agent018.ReLUNet.layer (m := 1)
      (⟨Matrix.of fun _ j => if j = 0 then (1 : ℝ) else 0, 0⟩ : Agent018.AffineMap' 3 1)
      (Agent018.ReLUNet.output (n := 1)
        (⟨Matrix.of fun _ _ => (1 : ℝ), 0⟩ : Agent018.AffineMap' 1 1)), ?_⟩
  funext x
  simp [Agent018.ReLUNet.eval, Agent018.AffineMap'.eval, Agent018.reluVec, Agent018.relu,
    Matrix.mulVec, dotProduct, Fin.sum_univ_one, Fin.sum_univ_three]

/-- The `Agent018` statement of Theorem 2 is false: its `CPWL` does not even contain
`relu` of a coordinate, which its own `ReLUn` does. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent018.CPWL n = Agent018.ReLUn n (Agent018.depthBound n)) := by
  intro h
  have hmem : (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent018.CPWL 3 := by
    rw [h 3 (by norm_num)]; exact relu3_mem
  exact max_not_mem 2 hmem

/-- The two readings are *not* equivalent: the left side is false (`agent_side_false`)
while the right side is the genuine Theorem 2, which is true.  Honest `sorry`: the only
missing input is the truth of `Ref.theorem2`, which is itself `sorry`-ed and which the
spec forbids routing through. -/
theorem statement_ne :
    ¬ ((∀ n, 3 ≤ n → Agent018.CPWL n = Agent018.ReLUn n (Agent018.depthBound n)) ↔
      (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n))) := by
  intro hiff
  exact agent_side_false (hiff.2 (by sorry))

end Star_018

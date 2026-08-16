namespace Star_067

/-!
# Star comparison: `Agent067` vs `Ref`

* `depthBound` is *literally* the same term (`⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`), so `depth`
  is `rfl`.
* `ReLUn` is the "**exactly** `k` hidden layers" reading, while `Ref.ReLUn` is "at most `k`".
  These denote the same set, but only through the padding identity `x = relu x - relu (-x)`,
  which is a real theorem; `relun` is left as an honest `sorry`.
* `CPWL` does **not** agree: `Agent067.CPWL` asks that every point have a *neighbourhood*
  on which `f` coincides with one member of a finite affine family.  On connected `ℝⁿ` that
  forces `f` to be globally affine, so it is strictly stronger than piecewise linearity.
  Hence `cpwl` is false; we prove `cpwl_ne`, and moreover `agent_side_false`: the `Agent067`
  reading of Theorem 2 is outright false, since `x ↦ relu (x 0)` is a one-hidden-layer
  network that its `CPWL` rejects.
-/

/-- Every halfspace is a polyhedron (the intersection of the one-element family). -/
private lemma poly_of_half {n : ℕ} {S : Set (Fin n → ℝ)} (h : Ref.IsHalfspace n S) :
    Ref.IsPolyhedron n S :=
  ⟨1, fun _ => S, fun _ => h, by rw [Set.iInter_const]⟩

/-- `relu` is idempotent. -/
private lemma relu_relu (a : ℝ) : max 0 (max 0 a) = max 0 a := max_eq_right (le_max_left 0 a)

/-- `x ↦ max 0 (x 0)` is CPWL in the reference sense: the two halflines cover `ℝ`. -/
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

/-- `x ↦ max 0 (x 0)` is *not* in `Agent067.CPWL`: agreement with a single affine map on a
neighbourhood of the origin forces `max 0 t = a * t + b` for all small `t`, which is absurd
(`t = 0` gives `b = 0`, `t = r/2` gives `a = 1`, `t = -r/2` then gives `0 = -r/2`). -/
private lemma max_not_mem (n : ℕ) :
    (fun x : Fin (n + 1) → ℝ => max 0 (x 0)) ∉ Agent067.CPWL (n + 1) := by
  rintro ⟨-, N, w, b, h⟩
  obtain ⟨i, hi⟩ := h 0
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hi
  have key : ∀ t : ℝ, |t| < r → max 0 t = (∑ j, w i j) * t + b i := by
    intro t ht
    have hd : dist (fun _ => t : Fin (n + 1) → ℝ) 0 < r := by
      rw [dist_pi_lt_iff hr]
      intro j
      simpa [Real.dist_eq] using ht
    simpa [Finset.sum_mul] using hball hd
  have h0 := key 0 (by simpa using hr)
  have h1 := key (r / 2) (by rw [abs_of_pos] <;> linarith)
  have h2 := key (-(r / 2)) (by rw [abs_of_neg] <;> linarith)
  rw [max_self] at h0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ r / 2)] at h1
  rw [max_eq_left (by linarith : -(r / 2) ≤ (0 : ℝ))] at h2
  nlinarith [h0, h1, h2]

/-- `Agent067.CPWL` is strictly stronger than `Ref.CPWL`, so the two differ.  Witness:
`f = fun x => max 0 (x 0)` at `n = 1`. -/
theorem cpwl_ne : ∃ n, Agent067.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  have hmem : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent067.CPWL 1 := by
    rw [h]; exact max_mem_ref
  exact max_not_mem 0 hmem

/-- `⌈log₃ (4 - 1)⌉ + 1 = 2`, since `log₃ 3 = 1`. -/
private lemma depthBound_four : Agent067.depthBound 4 = 2 := by
  have h3 : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have harg : ((4 : ℕ) : ℝ) - 1 = 3 := by norm_num
  have hlog : Real.logb 3 (((4 : ℕ) : ℝ) - 1) = 1 := by
    rw [harg]; simp [Real.logb, div_self h3]
  rw [show Agent067.depthBound 4 = ⌈Real.logb 3 (((4 : ℕ) : ℝ) - 1)⌉₊ + 1 from rfl, hlog,
    Nat.ceil_one]

/-- `x ↦ max 0 (x 0)` on `ℝ⁴` is computed by a network with *exactly* two hidden layers:
the first applies `relu` to `x 0`, the second applies `relu` again (harmless, as `relu` is
idempotent), and the readout is the identity functional. -/
private lemma relu4_mem :
    (fun x : Fin 4 → ℝ => max 0 (x 0)) ∈ Agent067.ReLUn 4 2 := by
  refine ⟨1, Matrix.of fun _ j => if j = 0 then (1 : ℝ) else 0, 0,
    (fun y : Fin 1 → ℝ => max 0 (y 0)), ?_, ?_⟩
  · refine ⟨1, 1, 0, (fun z : Fin 1 → ℝ => (∑ i, (1 : ℝ) * z i) + 0), ⟨fun _ => 1, 0, rfl⟩, ?_⟩
    funext y
    simp [Agent067.reluVec, Agent067.relu, Agent067.affineEval, Matrix.mulVec, dotProduct,
      Matrix.one_apply, Fin.sum_univ_one]
  · funext x
    simp [Agent067.reluVec, Agent067.relu, Agent067.affineEval, Matrix.mulVec, dotProduct,
      Fin.sum_univ_one, Fin.sum_univ_four, relu_relu]

/-- The `Agent067` reading of Theorem 2 is outright false: at `n = 4` the one-kink function
`x ↦ relu (x 0)` lies in `ReLUn 4 (depthBound 4) = ReLUn 4 2` but not in its `CPWL 4`. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent067.CPWL n = Agent067.ReLUn n (Agent067.depthBound n)) := by
  intro h
  have hmem : (fun x : Fin 4 → ℝ => max 0 (x 0)) ∈ Agent067.CPWL 4 := by
    rw [h 4 (by norm_num), depthBound_four]; exact relu4_mem
  exact max_not_mem 3 hmem

/-- `Agent067.ReLUn` counts hidden layers *exactly*, `Ref.ReLUn` counts them *at most*.
The sets coincide, but only via the padding identity `x = relu x - relu (-x)`, i.e. the
monotonicity of `Represents` in `k`, which is a genuine theorem.  Honest `sorry`. -/
theorem relun (n k : ℕ) : Agent067.ReLUn n k = Ref.ReLUn n k := sorry

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent067.depthBound n = Ref.depthBound n := rfl

/-- The left-hand side is false (`agent_side_false`), so this iff is equivalent to the
negation of the right-hand side, i.e. to refuting the *reference* Theorem 2 — which is in
fact true.  Proving the iff false therefore needs the true content of `Ref.theorem2`, which
is `sorry`-ed there and may not be routed through.  Honest `sorry`. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent067.CPWL n = Agent067.ReLUn n (Agent067.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_067

import QuickTest.Formalizations.Thm2_099
import QuickTest.Reference

namespace Star_099

/-! ## `depthBound` and `ReLUn`

`Agent099.depthBound` is syntactically the reference definition, so `depth` is `rfl`.

For `ReLUn`, both files take **at most** `k` hidden layers; the only difference is
that the agent packages the network as an inductive `Type` while the reference uses
a `Prop`-valued recursion.  The two are interchangeable by induction on the depth. -/

/-- A `Ref`-style ReLU computation of depth `k` is the same thing as an
`Agent099.ReLUNet` of depth `k` computing the same function. -/
private lemma computedBy_iff (k : ℕ) : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Ref.ComputedBy n k f ↔ ∃ net : Agent099.ReLUNet n k, ∀ x, net.eval x = f x := by
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨T, hT⟩
      exact ⟨.last ⟨fun i j => T.M i j, T.c⟩, fun x => (hT x).symm⟩
    · rintro ⟨net, hnet⟩
      cases net with
      | last T => exact ⟨⟨Matrix.of T.A, T.bias⟩, fun x => (hnet x).symm⟩
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, T, g, hg, hf⟩
      obtain ⟨net, hnet⟩ := (ih m g).mp hg
      exact ⟨.cons m ⟨fun i j => T.M i j, T.c⟩ net, fun x => (hnet _).trans (hf x).symm⟩
    · rintro ⟨net, hnet⟩
      cases net with
      | cons m T rest =>
        exact ⟨m, ⟨Matrix.of T.A, T.bias⟩, rest.eval,
          (ih m rest.eval).mpr ⟨rest, fun _ => rfl⟩, fun x => (hnet x).symm⟩

theorem relun (n k : ℕ) : Agent099.ReLUn n k = Ref.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨k', hk', net, hnet⟩
    exact ⟨k', hk', (computedBy_iff k' n f).mpr ⟨net, hnet⟩⟩
  · rintro ⟨j, hj, hf⟩
    obtain ⟨net, hnet⟩ := (computedBy_iff j n f).mp hf
    exact ⟨j, hj, net, hnet⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent099.depthBound n = Ref.depthBound n := rfl

/-! ## `CPWL`: the agent's condition is strictly stronger

`Agent099.CPWL` asks that `f` agree with one of finitely many affine maps on a
*neighbourhood* of every point.  That forbids kinks entirely, so `max 0 (x 0)` is
excluded — while it is a genuine continuous piecewise-linear function, and lies in
`Ref.CPWL`. -/

/-- No affine function agrees with `t ↦ max 0 t` near `0`. -/
private lemma affine_not_max {a b : ℝ}
    (h : ∀ᶠ t in nhds (0 : ℝ), max 0 t = a * t + b) : False := by
  obtain ⟨ε, hε, H⟩ := Metric.eventually_nhds_iff.mp h
  have h0 : max 0 (0 : ℝ) = a * 0 + b := H (by simpa using hε)
  have hb : b = 0 := by simpa using h0.symm
  have hp : max 0 (ε / 2) = a * (ε / 2) + b :=
    H (by rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
  have hm : max 0 (-(ε / 2)) = a * (-(ε / 2)) + b :=
    H (by rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by linarith)]; linarith)
  rw [max_eq_right (by linarith : (0:ℝ) ≤ ε / 2), hb, add_zero] at hp
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0:ℝ)), hb, add_zero] at hm
  have hz : a * (ε / 2) = 0 := by linear_combination hm
  linarith

/-- The kink at the origin: `max 0 (y i₀)` cannot agree with a single affine map
on a neighbourhood of `0` in `ℝⁿ`. -/
private lemma kink_aux {n : ℕ} (i0 : Fin n) (a : Fin n → ℝ) (b : ℝ)
    (h : ∀ᶠ y in nhds (0 : Fin n → ℝ), max 0 (y i0) = (∑ k, a k * y k) + b) : False := by
  have hc : Filter.Tendsto (fun t : ℝ => (fun _ => t : Fin n → ℝ)) (nhds 0)
      (nhds (0 : Fin n → ℝ)) :=
    (continuous_pi fun _ => continuous_id).tendsto' 0 0 (funext fun _ => rfl)
  refine affine_not_max (a := ∑ k, a k) (b := b) ?_
  filter_upwards [hc.eventually h] with t ht
  simpa [Finset.sum_mul] using ht

private lemma max_notMem_cpwl (n : ℕ) (i0 : Fin n) :
    (fun x : Fin n → ℝ => max 0 (x i0)) ∉ Agent099.CPWL n := by
  rintro ⟨-, m, g, hg, hloc⟩
  obtain ⟨i, hi⟩ := hloc 0
  obtain ⟨a, b, ha⟩ := hg i
  exact kink_aux i0 a b (hi.mono fun y hy => hy.trans (ha y))

private lemma poly_of_half {n : ℕ} {S : Set (Fin n → ℝ)} (h : Ref.IsHalfspace n S) :
    Ref.IsPolyhedron n S :=
  ⟨1, fun _ => S, fun _ => h, (Set.iInter_const _).symm⟩

/-- `max 0 (x 0)` *is* CPWL in the reference sense: the two halflines `{x 0 ≤ 0}`
and `{-x 0 ≤ 0}` are polyhedra covering `ℝ`, and `f` is affine on each. -/
private lemma f1_mem_ref : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Ref.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2,
    ![{x : Fin 1 → ℝ | (∑ i, (1:ℝ) * x i) ≤ 0}, {x : Fin 1 → ℝ | (∑ i, (-1:ℝ) * x i) ≤ 0}],
    ![fun _ => 0, fun x => x 0], ?_, ?_, ?_, ?_⟩
  · exact Fin.forall_fin_two.mpr
      ⟨poly_of_half ⟨fun _ => 1, 0, rfl⟩, poly_of_half ⟨fun _ => -1, 0, rfl⟩⟩
  · exact Fin.forall_fin_two.mpr
      ⟨⟨fun _ => 0, 0, by intro x; simp⟩, ⟨fun _ => 1, 0, by intro x; simp⟩⟩
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    rcases le_total (x 0) 0 with h | h
    · refine ⟨0, ?_⟩
      simp only [Matrix.cons_val_zero, Set.mem_setOf_eq, Fin.sum_univ_one]
      linarith
    · refine ⟨1, ?_⟩
      simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero,
        Matrix.cons_val_fin_one, Set.mem_setOf_eq, Fin.sum_univ_one]
      linarith
  · refine Fin.forall_fin_two.mpr ⟨fun x hx => ?_, fun x hx => ?_⟩
    · simp only [Matrix.cons_val_zero, Set.mem_setOf_eq, Fin.sum_univ_one] at hx ⊢
      exact max_eq_left (by linarith)
    · simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero,
        Matrix.cons_val_fin_one, Set.mem_setOf_eq, Fin.sum_univ_one] at hx ⊢
      exact max_eq_right (by linarith)

/-- `Agent099.CPWL` is **not** the reference `CPWL`: at `n = 1` it already misses
`max 0 (x 0)`. -/
theorem cpwl_ne : ∃ n, Agent099.CPWL n ≠ Ref.CPWL n :=
  ⟨1, fun h => max_notMem_cpwl 1 0 (by rw [h]; exact f1_mem_ref)⟩

/-- `max 0 (x 0)` on `ℝ³` is a one-hidden-layer ReLU network, hence within the
agent's depth budget. -/
private lemma f3_mem_relun :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent099.ReLUn 3 (Agent099.depthBound 3) := by
  refine ⟨1, Nat.le_add_left 1 _,
    .cons 1 ⟨fun _ j => if j = 0 then 1 else 0, fun _ => 0⟩
      (.last ⟨fun _ _ => 1, fun _ => 0⟩), fun x => ?_⟩
  simp [Agent099.ReLUNet.eval, Agent099.AffMap.eval, Agent099.reluVec, Agent099.relu,
    Fin.sum_univ_one, Fin.sum_univ_three]

/-- The agent's own Theorem 2 is false as stated: at `n = 3` the right-hand side
contains `max 0 (x 0)` and the (neighbourhood-based) left-hand side does not. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent099.CPWL n = Agent099.ReLUn n (Agent099.depthBound n)) := by
  intro h
  exact max_notMem_cpwl 3 0 (by rw [h 3 le_rfl]; exact f3_mem_relun)

-- The agent side is false (`agent_side_false`); refuting the iff would need the
-- reference side to be *true*, i.e. the real Theorem 2, which `Ref.theorem2`
-- only `sorry`s.  Honest `sorry`.
theorem statement :
    (∀ n, 3 ≤ n → Agent099.CPWL n = Agent099.ReLUn n (Agent099.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_099

import QuickTest.Formalizations.Thm2_079
import QuickTest.Reference

namespace Star_079

/-!
# Star comparison: `Agent079` vs `Ref`

* `depthBound` is *literally* the same term (`⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1`), so `depth`
  is `rfl`.
* `ReLUn` agrees: both files take **at most** `k` hidden layers.  `Ref` uses a recursive
  `Prop` (`ComputedBy`), `Agent079` uses an inductive `Type` of networks (`ReLUNet`) plus
  its evaluation; the two are interchangeable by an easy induction, proved below.
* `CPWL` does **not** agree.  Despite the doc comment advertising a
  "polyhedral-subdivision style definition", `Agent079.CPWL` actually asks for agreement
  with a *single* affine map on an `ε`-ball around every point.  On connected `ℝⁿ` that
  forces global affineness, so `Agent079.CPWL` is strictly smaller than `Ref.CPWL`; we
  prove `cpwl_ne`, and moreover that the `Agent079` reading of Theorem 2 is outright
  false (`agent_side_false`).
-/

/-- `Fin 1` is a subsingleton, so the raw index used by `ReLUNet.eval` is `0`. -/
private lemma fin1_zero : (⟨0, Nat.one_pos⟩ : Fin 1) = 0 := Subsingleton.elim _ _

/-- The two network formalisms denote the same functions, layer for layer. -/
private lemma net_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Ref.ComputedBy n k f ↔ ∃ net : Agent079.ReLUNet n k, ∀ x, f x = net.eval x := by
  intro k
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨T, hT⟩
      refine ⟨Agent079.ReLUNet.output n ⟨T.M, T.c⟩, fun x => ?_⟩
      rw [hT x]
      simp [Agent079.ReLUNet.eval, Agent079.AffineTransform.eval, Ref.Aff.eval, fin1_zero]
    · rintro ⟨net, hnet⟩
      cases net with
      | output _ T =>
        refine ⟨⟨T.A, T.c⟩, fun x => ?_⟩
        rw [hnet x]
        simp [Agent079.ReLUNet.eval, Agent079.AffineTransform.eval, Ref.Aff.eval, fin1_zero]
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, T, g, hg, hf⟩
      obtain ⟨net, hnet⟩ := (ih m g).1 hg
      refine ⟨Agent079.ReLUNet.layer n m k ⟨T.M, T.c⟩ net, fun x => ?_⟩
      have hstep : (Agent079.ReLUNet.layer n m k ⟨T.M, T.c⟩ net).eval x
          = net.eval (Ref.reluVec (T.eval x)) := rfl
      rw [hf x, hnet, hstep]
    · rintro ⟨net, hnet⟩
      cases net with
      | layer _ m _ T rest =>
        refine ⟨m, ⟨T.A, T.c⟩, rest.eval, (ih m rest.eval).2 ⟨rest, fun _ => rfl⟩,
          fun x => ?_⟩
        rw [hnet x]

theorem relun (n k : ℕ) : Agent079.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent079.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, hnet⟩
    exact ⟨j, hj, (net_iff j n f).2 hnet⟩
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (net_iff j n f).1 hf⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent079.depthBound n = Ref.depthBound n := rfl

/-- Every halfspace is a polyhedron (intersection of the one-element family). -/
private lemma poly_of_half {n : ℕ} {S : Set (Fin n → ℝ)} (h : Ref.IsHalfspace n S) :
    Ref.IsPolyhedron n S :=
  ⟨1, fun _ => S, fun _ => h, by rw [Set.iInter_const]⟩

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

/-- `x ↦ max 0 (x 0)` is *not* in `Agent079.CPWL`: agreement with one affine map on a whole
`ε`-ball around the origin forces `max 0 t = a * t + b` for all small `t`, which is absurd
(`t = 0` gives `b = 0`, `t = ε/2` gives `a = 1`, `t = -ε/2` then gives `0 = -ε/2`). -/
private lemma max_not_mem (n : ℕ) :
    (fun x : Fin (n + 1) → ℝ => max 0 (x 0)) ∉ Agent079.CPWL (n + 1) := by
  rintro ⟨-, m, g, hg, h⟩
  obtain ⟨i, ε, hε, hi⟩ := h 0
  obtain ⟨a, b, ha⟩ := hg i
  have key : ∀ t : ℝ, |t| < ε → max 0 t = (∑ j, a j) * t + b := by
    intro t ht
    have hd : dist (fun _ => t : Fin (n + 1) → ℝ) 0 < ε := by
      rw [dist_pi_lt_iff hε]
      intro j
      simpa [Real.dist_eq] using ht
    have hx := hi (fun _ => t) hd
    rw [ha] at hx
    simpa [Finset.sum_mul] using hx
  have h0 := key 0 (by simpa using hε)
  have h1 := key (ε / 2) (by rw [abs_of_pos] <;> linarith)
  have h2 := key (-(ε / 2)) (by rw [abs_of_neg] <;> linarith)
  rw [max_self] at h0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ ε / 2)] at h1
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0 : ℝ))] at h2
  nlinarith [h0, h1, h2]

/-- `Agent079.CPWL` is strictly stronger than `Ref.CPWL`, so the two differ. -/
theorem cpwl_ne : ∃ n, Agent079.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  have hmem : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent079.CPWL 1 := by
    rw [h]; exact max_mem_ref
  exact max_not_mem 0 hmem

/-- `max 0 (x 0)` on `ℝ³` is computed by a one-hidden-layer network. -/
private lemma relu3_mem :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent079.ReLUn 3 (Agent079.depthBound 3) := by
  refine ⟨1, Nat.le_add_left 1 _,
    Agent079.ReLUNet.layer 3 1 0 ⟨Matrix.of fun _ j => if j = 0 then (1 : ℝ) else 0, 0⟩
      (Agent079.ReLUNet.output 1 ⟨1, 0⟩), fun x => ?_⟩
  simp [Agent079.ReLUNet.eval, Agent079.AffineTransform.eval, Agent079.reluVec,
    Agent079.relu, Matrix.mulVec, dotProduct, Matrix.one_apply, Fin.sum_univ_three,
    Fin.sum_univ_one]

/-- The `Agent079` reading of Theorem 2 is outright false: its `CPWL` misses `relu`,
which its own `ReLUn` contains. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent079.CPWL n = Agent079.ReLUn n (Agent079.depthBound n)) := by
  intro h
  have hmem : (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent079.CPWL 3 := by
    rw [h 3 (by norm_num)]; exact relu3_mem
  exact max_not_mem 2 hmem

/-- The two readings of Theorem 2 are *not* equivalent: the left side is false
(`agent_side_false`), while the right side is the real Theorem 2, which is true.
Honest `sorry`: discharging it needs the true direction of `Ref.theorem2`, which is itself
`sorry`-ed, and routing through it is forbidden. -/
theorem statement_ne :
    ¬ ((∀ n, 3 ≤ n → Agent079.CPWL n = Agent079.ReLUn n (Agent079.depthBound n)) ↔
      (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n))) := by
  intro hiff
  exact agent_side_false (hiff.2 (by sorry))

end Star_079

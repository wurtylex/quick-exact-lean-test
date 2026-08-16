import QuickTest.Formalizations.Thm2_076
import QuickTest.Reference

namespace Star_076

/-!
`Agent076` defines `CPWL` by *neighbourhood agreement* (`f =ᶠ[nhds x] g i` for a
finite family of affine `g`), which is strictly stronger than piecewise
linearity: it forces `f` to be affine near every point, hence (on connected
`ℝⁿ`) globally affine.  So `cpwl` is **false** and we refute it, and the
agent-side Theorem 2 is false outright (`agent_side_false`).

`ReLUn` and `depthBound` agree with the reference (both use "at most `k` hidden
layers" and the same ceiling of `logb 3 (n-1)`), and both are proved.
-/

/-- Any halfspace is a polyhedron (intersection of a one-element family). -/
private lemma halfspace_polyhedron {n : ℕ} {S : Set (Fin n → ℝ)}
    (hS : Ref.IsHalfspace n S) : Ref.IsPolyhedron n S :=
  ⟨1, fun _ => S, fun _ => hS, (Set.iInter_const _).symm⟩

/-- The kink argument: `x ↦ max 0 (x i₀)` is not affine on any neighbourhood of
the origin, so it fails `Agent076`'s neighbourhood-agreement condition. -/
private lemma witness_not_agent (N : ℕ) (i₀ : Fin N) :
    (fun x : Fin N → ℝ => max 0 (x i₀)) ∉ Agent076.CPWL N := by
  rintro ⟨-, m, g, hg, hcov⟩
  obtain ⟨i, hi⟩ := hcov 0
  obtain ⟨a, c, ha⟩ := hg i
  obtain ⟨s, hs, hEq⟩ := Filter.eventuallyEq_iff_exists_mem.mp hi
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  have hsum : ∀ (b : Fin N → ℝ) (t : ℝ),
      (∑ j, b j * (if j = i₀ then t else 0)) = b i₀ * t := by
    intro b t
    rw [Finset.sum_eq_single i₀]
    · rw [if_pos rfl]
    · intro d _ hd; rw [if_neg hd, mul_zero]
    · intro hcon; exact absurd (Finset.mem_univ i₀) hcon
  have key : ∀ t : ℝ, |t| < ε → max 0 t = c + a i₀ * t := by
    intro t ht
    have hmem : (fun j => if j = i₀ then t else 0) ∈ Metric.ball (0 : Fin N → ℝ) ε := by
      rw [Metric.mem_ball, dist_pi_lt_iff hε]
      intro b
      rcases eq_or_ne b i₀ with hb | hb
      · simpa [hb, Real.dist_eq] using ht
      · simpa [hb, Real.dist_eq] using hε
    have h := hEq (hball hmem)
    rw [ha] at h
    simpa [hsum] using h
  have e0 := key 0 (by simpa using hε)
  have e1 := key (ε / 2) (by rw [abs_of_pos (by linarith)]; linarith)
  have e2 := key (-(ε / 2)) (by rw [abs_of_neg (by linarith)]; linarith)
  rw [max_self, mul_zero, add_zero] at e0
  rw [max_eq_right (by linarith : (0:ℝ) ≤ ε / 2), ← e0, zero_add] at e1
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0:ℝ)), ← e0, zero_add] at e2
  linarith

/-- The same function *is* piecewise linear in the reference sense: the two
halfspaces `{x 0 ≤ 0}` and `{-x 0 ≤ 0}` cover `ℝ`. -/
private lemma witness_mem_ref :
    (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Ref.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2,
    fun i => {x : Fin 1 → ℝ | (∑ j, (if i = 0 then (1:ℝ) else -1) * x j) ≤ 0},
    fun i => fun x => if i = 0 then 0 else x 0, ?_, ?_, ?_, ?_⟩
  · exact fun i => halfspace_polyhedron ⟨fun _ => if i = 0 then (1:ℝ) else -1, 0, rfl⟩
  · intro i
    by_cases hi : i = 0
    · exact ⟨fun _ => 0, 0, fun x => by simp [hi]⟩
    · exact ⟨fun _ => 1, 0, fun x => by simp [hi]⟩
  · refine Set.eq_univ_of_forall fun x => ?_
    rcases le_or_gt (x 0) 0 with h | h
    · refine Set.mem_iUnion.2 ⟨0, ?_⟩
      show (∑ j : Fin 1, (if (0 : Fin 2) = 0 then (1:ℝ) else -1) * x j) ≤ 0
      rw [Fin.sum_univ_one, if_pos rfl]; linarith
    · refine Set.mem_iUnion.2 ⟨1, ?_⟩
      show (∑ j : Fin 1, (if (1 : Fin 2) = 0 then (1:ℝ) else -1) * x j) ≤ 0
      rw [Fin.sum_univ_one, if_neg (by decide)]; linarith
  · intro i x hx
    by_cases hi : i = 0
    · subst hi
      have h0 : (∑ j : Fin 1, (if (0 : Fin 2) = 0 then (1:ℝ) else -1) * x j) ≤ 0 := hx
      rw [Fin.sum_univ_one, if_pos rfl, one_mul] at h0
      simp [max_eq_left h0]
    · have h0 : (∑ j : Fin 1, (if i = 0 then (1:ℝ) else -1) * x j) ≤ 0 := hx
      rw [Fin.sum_univ_one, if_neg hi] at h0
      simp [hi, max_eq_right (by linarith : (0:ℝ) ≤ x 0)]

/-- The two recursive network definitions describe the same functions: the only
difference is that `Agent076` packages the affine maps as predicates on
functions and `Ref` as a `structure`. -/
private lemma computes_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent076.ComputesWithHiddenLayers k n f ↔ Ref.ComputedBy n k f := by
  intro k
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨a, c, h⟩
      refine ⟨⟨Matrix.of fun _ j => a j, fun _ => c⟩, fun x => ?_⟩
      rw [h x]
      show c + ∑ i, a i * x i = (∑ j, a j * x j) + c
      exact add_comm _ _
    · rintro ⟨T, h⟩
      refine ⟨fun j => T.M 0 j, T.c 0, fun x => ?_⟩
      rw [h x]
      show (∑ j, T.M 0 j * x j) + T.c 0 = T.c 0 + ∑ i, T.M 0 i * x i
      exact add_comm _ _
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, T, g, ⟨A, c, hT⟩, hg, hf⟩
      refine ⟨m, ⟨A, c⟩, g, (ih m g).mp hg, fun x => ?_⟩
      have hx : Agent076.reluVec (T x) = Ref.reluVec ((⟨A, c⟩ : Ref.Aff n m).eval x) := by
        funext j
        show max 0 (T x j) = max 0 ((A.mulVec x + c) j)
        rw [hT x]
      rw [hf x, hx]
    · rintro ⟨m, T, g, hg, hf⟩
      exact ⟨m, fun x => T.eval x, g, ⟨T.M, T.c, fun _ => rfl⟩, (ih m g).mpr hg,
        fun x => by rw [hf x]⟩

theorem relun (n k : ℕ) : Agent076.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent076.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  exact ⟨fun ⟨j, hj, h⟩ => ⟨j, hj, (computes_iff j n f).mp h⟩,
    fun ⟨j, hj, h⟩ => ⟨j, hj, (computes_iff j n f).mpr h⟩⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent076.depthBound n = Ref.depthBound n := rfl

/-- `Agent076.CPWL` is the neighbourhood-agreement condition, which is strictly
stronger than the reference's polyhedral-cover condition. -/
theorem cpwl_ne : ∃ n, Agent076.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  have hm : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent076.CPWL 1 := by
    rw [h]; exact witness_mem_ref
  exact witness_not_agent 1 0 hm

/-- The agent's own Theorem 2 is false: at `n = 3`, `x ↦ max 0 (x 0)` is a
one-hidden-layer ReLU network but fails the neighbourhood-agreement `CPWL`. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent076.CPWL n = Agent076.ReLUn n (Agent076.depthBound n)) := by
  intro h
  have h3 := h 3 (by norm_num)
  have hmem : (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈
      Agent076.ReLUn 3 (Agent076.depthBound 3) := by
    refine ⟨1, Nat.le_add_left 1 _, 1, fun x => fun _ => x 0, fun y => y 0, ?_,
      ⟨fun _ => 1, 0, fun y => by simp⟩, fun x => rfl⟩
    refine ⟨Matrix.of fun _ j => if j = 0 then (1:ℝ) else 0, 0, fun x => ?_⟩
    funext i
    show x 0 = (∑ j, (if j = 0 then (1:ℝ) else 0) * x j) + (0:ℝ)
    rw [add_zero, Finset.sum_eq_single (0 : Fin 3)]
    · rw [if_pos rfl, one_mul]
    · intro d _ hd; rw [if_neg hd, zero_mul]
    · intro hcon; exact absurd (Finset.mem_univ (0 : Fin 3)) hcon
  rw [← h3] at hmem
  exact witness_not_agent 3 0 hmem

/-- Honest `sorry`: the left side of the iff is false (`agent_side_false`), so
the iff is equivalent to the *negation* of the reference Theorem 2, which can be
settled only by proving/refuting Theorem 2 itself. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent076.CPWL n = Agent076.ReLUn n (Agent076.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_076

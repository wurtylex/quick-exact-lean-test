import QuickTest.Formalizations.Thm2_056
import QuickTest.Reference

namespace Star_056

/-!
# Star comparison for `Agent056`

* `ReLUn`: both files use **at most `k`** hidden layers; the only difference is the
  encoding (`Ref.ComputedBy`, a recursion on `k`, versus `Agent056.ReLUNet`, an
  inductive family).  These are genuinely equivalent, and `relun` is proved.
* `depthBound`: literally the same definition, so `depth` is `rfl`.
* `CPWL`: `Agent056` uses *neighbourhood agreement* (`∀ᶠ y in nhds x`) with a finite
  family of affine functionals, **not** a polyhedral cover.  That condition forces `f`
  to be globally affine, so it is strictly stronger than CPWL: `cpwl` is false
  (`cpwl_ne`), and the agent's Theorem 2 is false outright (`agent_side_false`).
-/

/-- `Matrix.mulVec` evaluated at a coordinate, definitionally. -/
private lemma mulVec_apply {a b : ℕ} (A : Matrix (Fin b) (Fin a) ℝ) (x : Fin a → ℝ)
    (i : Fin b) : A.mulVec x i = ∑ j, A i j * x j := rfl

/-! ### `ReLUn`: the two encodings agree -/

private lemma compute_computedBy : ∀ {n k : ℕ} (net : Agent056.ReLUNet n k),
    Ref.ComputedBy n k net.compute := by
  intro n k net
  induction net with
  | output T => exact ⟨⟨T.A, T.bias⟩, fun _ => rfl⟩
  | layer T rest ih => exact ⟨_, ⟨T.A, T.bias⟩, rest.compute, ih, fun _ => rfl⟩

private lemma computedBy_net : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ), Ref.ComputedBy n k f →
    ∃ net : Agent056.ReLUNet n k, ∀ x, f x = net.compute x := by
  intro k
  induction k with
  | zero =>
    intro n f h
    obtain ⟨T, hT⟩ := h
    exact ⟨Agent056.ReLUNet.output ⟨T.M, T.c⟩, hT⟩
  | succ k ih =>
    intro n f h
    obtain ⟨m, T, g, hg, hf⟩ := h
    obtain ⟨net, hnet⟩ := ih m g hg
    exact ⟨Agent056.ReLUNet.layer ⟨T.M, T.c⟩ net, fun x => (hf x).trans (hnet _)⟩

theorem relun (n k : ℕ) : Agent056.ReLUn n k = Ref.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨j, hj, net, hnet⟩
    refine ⟨j, hj, ?_⟩
    have hfe : f = net.compute := funext hnet
    rw [hfe]
    exact compute_computedBy net
  · rintro ⟨j, hj, h⟩
    obtain ⟨net, hnet⟩ := computedBy_net j n f h
    exact ⟨j, hj, net, hnet⟩

/-! ### `depthBound`: identical definitions -/

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent056.depthBound n = Ref.depthBound n := rfl

/-! ### `CPWL`: neighbourhood agreement is strictly stronger -/

/-- No affine function agrees with `max 0 ·` on a neighbourhood of `0`. -/
private lemma no_affine_kink (a b : ℝ) :
    ¬ (∀ᶠ t : ℝ in nhds 0, max 0 t = a * t + b) := by
  intro h
  rw [Metric.eventually_nhds_iff] at h
  obtain ⟨ε, hε, H⟩ := h
  have h0 : max (0:ℝ) 0 = a * 0 + b := H (by simpa using hε)
  have hp : max (0:ℝ) (ε / 2) = a * (ε / 2) + b :=
    H (by rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
  have hm : max (0:ℝ) (-(ε / 2)) = a * (-(ε / 2)) + b :=
    H (by rw [Real.dist_eq, sub_zero, abs_of_neg (by linarith)]; linarith)
  rw [max_self] at h0
  rw [max_eq_right (by linarith : (0:ℝ) ≤ ε / 2)] at hp
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0:ℝ))] at hm
  linarith

/-- A `relu` of a coordinate is never in the agent's `CPWL`, in any dimension. -/
private lemma kink_not_cpwl {n : ℕ} (i : Fin n) :
    (fun x : Fin n → ℝ => max 0 (x i)) ∉ Agent056.CPWL n := by
  rintro ⟨-, m, g, hg⟩
  obtain ⟨j, hj⟩ := hg (fun _ => (0:ℝ))
  have hc : Filter.Tendsto (fun t : ℝ => (fun _ => t : Fin n → ℝ)) (nhds 0)
      (nhds (fun _ => (0:ℝ))) := (continuous_pi fun _ => continuous_id).tendsto 0
  have key : ∀ᶠ t : ℝ in nhds 0,
      max 0 t = (∑ k, (g j).coeff k) * t + (g j).const := by
    filter_upwards [hc.eventually hj] with t ht
    simpa [Agent056.AffineFunctional.eval, Finset.sum_mul] using ht
  exact no_affine_kink _ _ key

/-- `max 0 (x 0)` *is* CPWL in the reference sense: two halfspaces cover `ℝ`. -/
private lemma ref_mem : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Ref.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2,
    ![{x | x 0 ≤ 0}, {x | -x 0 ≤ 0}], ![fun _ => 0, fun x => x 0], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · refine ⟨1, fun _ => {x : Fin 1 → ℝ | x 0 ≤ 0}, fun _ => ⟨fun _ => 1, 0, ?_⟩, ?_⟩
      · ext x; simp
      · exact (Set.iInter_const _).symm
    · refine ⟨1, fun _ => {x : Fin 1 → ℝ | -x 0 ≤ 0}, fun _ => ⟨fun _ => -1, 0, ?_⟩, ?_⟩
      · ext x; simp
      · exact (Set.iInter_const _).symm
  · intro i
    fin_cases i
    · exact ⟨0, 0, by intro x; simp⟩
    · exact ⟨fun _ => 1, 0, by intro x; simp⟩
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    rcases le_or_gt (x 0) 0 with h | h
    · exact ⟨0, show x 0 ≤ 0 from h⟩
    · exact ⟨1, show -x 0 ≤ 0 by linarith⟩
  · intro i
    fin_cases i
    · intro x hx
      have h : x 0 ≤ 0 := hx
      exact max_eq_left h
    · intro x hx
      have h : -x 0 ≤ 0 := hx
      exact max_eq_right (by linarith)

/-- The agent's `CPWL` differs from the reference `CPWL`: at `n = 1` the function
`x ↦ max 0 (x 0)` lies in the reference set but not in the agent's. -/
theorem cpwl_ne : ∃ n, Agent056.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => kink_not_cpwl (0 : Fin 1) ?_⟩
  rw [h]
  exact ref_mem

/-- The agent's Theorem 2 is false on its own terms: `relu (x 0)` is computed by a
one-hidden-layer network on `ℝ³` but fails the neighbourhood-agreement `CPWL`. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent056.CPWL n = Agent056.ReLUn n (Agent056.depthBound n)) := by
  intro h
  have hmem : (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈
      Agent056.ReLUn 3 (Agent056.depthBound 3) := by
    refine ⟨1, by unfold Agent056.depthBound; omega,
      (Agent056.ReLUNet.layer (m := 1)
          ⟨Matrix.of fun _ (j : Fin 3) => if j = 0 then (1:ℝ) else 0, 0⟩
          (Agent056.ReLUNet.output (n := 1) ⟨Matrix.of fun _ _ => (1:ℝ), 0⟩) :
        Agent056.ReLUNet 3 1), fun x => ?_⟩
    simp [Agent056.ReLUNet.compute, Agent056.AffMap.eval, Agent056.reluVec, Agent056.relu,
      mulVec_apply, Fin.sum_univ_one, Fin.sum_univ_three]
  exact kink_not_cpwl (0 : Fin 3) (by rw [h 3 le_rfl]; exact hmem)

-- `statement` is in fact **false** (its left side is refuted by `agent_side_false`,
-- while its right side is the true Theorem 2), but refuting it requires *proving*
-- `Ref.theorem2`, which is itself `sorry`-ed.  Left as an honest `sorry`.
theorem statement :
    (∀ n, 3 ≤ n → Agent056.CPWL n = Agent056.ReLUn n (Agent056.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_056

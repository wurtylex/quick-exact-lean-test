import QuickTest.Formalizations.Thm2_061
import QuickTest.Reference

namespace Star_061

/-!
`Agent061` differs from `Ref` in exactly one place: its `IsCPWL` is the
*local* ("neighbourhood agreement") condition
`∀ x, ∃ h ∈ S, ∀ᶠ y in nhds x, f y = h y` with `S` a finite family of affine
functions, rather than a finite polyhedral cover.  That condition is strictly
stronger than continuous piecewise linearity, so `cpwl` is **false**
(`cpwl_ne`) and the agent's Theorem 2 is false outright (`agent_side_false`).

`ReLUn` and `depthBound` do agree with the reference, and both are proved here.
-/

/-- No affine function on `ℝ` agrees with `relu` on a whole neighbourhood of `0`. -/
private lemma no_local_affine (A b : ℝ)
    (hev : ∀ᶠ t : ℝ in nhds 0, max 0 t = A * t + b) : False := by
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hb⟩ := hev
  have h0 : max (0:ℝ) 0 = A * 0 + b := hb (by simpa using hε)
  have hp : max (0:ℝ) (ε / 2) = A * (ε / 2) + b :=
    hb (by rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
  have hm : max (0:ℝ) (-(ε / 2)) = A * (-(ε / 2)) + b :=
    hb (by rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by linarith)]; linarith)
  rw [max_self] at h0
  rw [max_eq_right (by linarith : (0:ℝ) ≤ ε / 2)] at hp
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0:ℝ))] at hm
  nlinarith

/-- The kink argument: `x ↦ relu (x i)` fails the agent's neighbourhood-agreement
condition, because agreement with one affine map near `0` forces linearity there. -/
private lemma not_isCPWL_relu {n : ℕ} (i : Fin n) :
    ¬ Agent061.IsCPWL (fun x : Fin n → ℝ => max 0 (x i)) := by
  rintro ⟨-, S, hS, hloc⟩
  obtain ⟨h, hhS, hev⟩ := hloc 0
  obtain ⟨a, b, hab⟩ := hS h hhS
  have hc : Continuous (fun t : ℝ => (fun _ => t : Fin n → ℝ)) :=
    continuous_pi fun _ => continuous_id
  have htend : Filter.Tendsto (fun t : ℝ => (fun _ => t : Fin n → ℝ)) (nhds 0) (nhds 0) :=
    hc.tendsto 0
  refine no_local_affine (∑ j, a j) b ?_
  filter_upwards [htend.eventually hev] with t ht
  rw [hab] at ht
  simpa [Finset.sum_mul] using ht

private lemma halfspace_isPolyhedron {n : ℕ} {S : Set (Fin n → ℝ)}
    (h : Ref.IsHalfspace n S) : Ref.IsPolyhedron n S :=
  ⟨1, fun _ => S, fun _ => h, (Set.iInter_const S).symm⟩

/-- `relu` of a coordinate *is* CPWL in the reference sense: two halfspaces cover `ℝ`. -/
private lemma relu_mem_ref : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Ref.CPWL 1 := by
  show Ref.IsCPWL 1 _
  refine ⟨continuous_const.max (continuous_apply 0), 2,
    ![{x : Fin 1 → ℝ | (∑ j, (1:ℝ) * x j) ≤ 0}, {x : Fin 1 → ℝ | (∑ j, (-1:ℝ) * x j) ≤ 0}],
    ![fun _ => 0, fun x => x 0], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact halfspace_isPolyhedron ⟨fun _ => 1, 0, rfl⟩
    · exact halfspace_isPolyhedron ⟨fun _ => -1, 0, rfl⟩
  · intro i
    fin_cases i
    · exact ⟨fun _ => 0, 0, by intro x; simp⟩
    · exact ⟨fun _ => 1, 0, by intro x; simp⟩
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    rcases le_total (x 0) 0 with hx | hx
    · exact ⟨0, by simpa using hx⟩
    · exact ⟨1, by simpa using hx⟩
  · intro i
    fin_cases i
    · intro x hx
      have hx0 : x 0 ≤ 0 := by simpa using hx
      simpa using max_eq_left hx0
    · intro x hx
      have hx0 : (0:ℝ) ≤ x 0 := by simpa using hx
      simpa using max_eq_right hx0

/-- The agent's `CPWL` is **not** the reference `CPWL`: `x ↦ max 0 (x 0)` is in the
latter but not the former. -/
theorem cpwl_ne : ∃ n, Agent061.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun hEq => ?_⟩
  exact not_isCPWL_relu (0 : Fin 1) ((Set.ext_iff.mp hEq _).mpr relu_mem_ref)

/-- The two network definitions agree: `Ref.Aff.eval` and `Agent061.IsAffineMap`
describe the same affine maps, layer by layer. -/
private lemma computedBy_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Ref.ComputedBy n k f ↔ Agent061.NetComputes k n f := by
  intro k
  induction k with
  | zero =>
      intro n f
      constructor
      · rintro ⟨T, hT⟩
        exact ⟨fun i => T.M 0 i, T.c 0, fun x => hT x⟩
      · rintro ⟨a, b, hab⟩
        exact ⟨⟨Matrix.of fun _ j => a j, fun _ => b⟩, fun x => hab x⟩
  | succ k ih =>
      intro n f
      constructor
      · rintro ⟨m, T, g, hg, hfx⟩
        exact ⟨m, T.eval, g, ⟨T.M, T.c, fun x => rfl⟩, (ih m g).mp hg, fun x => hfx x⟩
      · rintro ⟨m, T, g, ⟨A, c, hA⟩, hg, hfx⟩
        refine ⟨m, ⟨A, c⟩, g, (ih m g).mpr hg, fun x => ?_⟩
        have hx := hfx x
        rw [hA x] at hx
        exact hx

theorem relun (n k : ℕ) : Agent061.ReLUn n k = Ref.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (computedBy_iff j n f).mpr hf⟩
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (computedBy_iff j n f).mp hf⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent061.depthBound n = Ref.depthBound n := rfl

/-- `x ↦ max 0 (x 0)` on `ℝ³` is a one-hidden-layer ReLU network. -/
private lemma relu_mem_relun :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent061.ReLUn 3 (Agent061.depthBound 3) := by
  refine ⟨1, Nat.le_add_left 1 _, 3, id, fun v => v 0, ?_, ?_, fun x => rfl⟩
  · exact ⟨1, 0, by intro x; simp⟩
  · exact ⟨![1, 0, 0], 0, by intro v; simp [Fin.sum_univ_three]⟩

/-- The agent's statement of Theorem 2 is false: at `n = 3`, `relu` of a coordinate
is a depth-1 network but fails the agent's (too strong) `CPWL`. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent061.CPWL n = Agent061.ReLUn n (Agent061.depthBound n)) := by
  intro hthm
  have hmem := relu_mem_relun
  rw [← hthm 3 le_rfl] at hmem
  exact not_isCPWL_relu (0 : Fin 3) hmem

/-- Honest `sorry`: the agent side is false (`agent_side_false`), so this iff holds
iff the reference side is false; but the reference side *is* Theorem 2, which is
`sorry`-ed in `Ref` and would have to be proved from scratch here. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent061.CPWL n = Agent061.ReLUn n (Agent061.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_061

import QuickTest.Formalizations.Thm2_070
import QuickTest.Reference

/-!
# Star comparison: `Agent070` vs `Ref`

* `ReLUn` and `depthBound` agree (both proved below).
* `CPWL` does **not** agree: `Agent070.CPWL` asks for agreement with a member of a
  finite affine family on a *neighbourhood* of every point, which on connected `ℝⁿ`
  forces `f` to be globally affine.  It is strictly stronger than the reference's
  finite polyhedral cover, so `cpwl` is refuted via `cpwl_ne`.
-/

namespace Star_070

/-! ### `ReLUn` -/

/-- The agent's inductive network relation implies the reference's recursive one;
the two affine-map structures differ only in field names. -/
private lemma toRef {n j : ℕ} {f : (Fin n → ℝ) → ℝ}
    (h : Agent070.NetworkComputes n j f) : Ref.ComputedBy n j f := by
  induction h with
  | base n T => exact ⟨⟨T.A, T.c⟩, fun x => rfl⟩
  | step n m j T g _ ih => exact ⟨m, ⟨T.A, T.c⟩, g, ih, fun x => rfl⟩

/-- The converse of `toRef`, by induction on the number of hidden layers. -/
private lemma ofRef : ∀ (j n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Ref.ComputedBy n j f → Agent070.NetworkComputes n j f := by
  intro j
  induction j with
  | zero =>
    rintro n f ⟨T, hT⟩
    have hf : f = fun x => (Agent070.AffineMap.mk T.M T.c).eval x 0 := funext hT
    rw [hf]
    exact .base n _
  | succ j ih =>
    rintro n f ⟨m, T, g, hg, hfx⟩
    have hf : f = fun x =>
        g (Agent070.reluVec ((Agent070.AffineMap.mk T.M T.c).eval x)) := funext hfx
    rw [hf]
    exact .step n m j ⟨T.M, T.c⟩ g (ih m g hg)

/-- Both files read `ReLU_{n,k}` as *at most* `k` hidden layers, so the sets agree. -/
theorem relun (n k : ℕ) : Agent070.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent070.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  exact exists_congr fun j => and_congr_right fun _ => ⟨toRef, ofRef j n f⟩

/-! ### `depthBound` -/

/-- Both files write `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1` verbatim. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent070.depthBound n = Ref.depthBound n := rfl

/-! ### `CPWL` -/

private def half₁ : Set (Fin 1 → ℝ) := {x | (∑ i, (1 : ℝ) * x i) ≤ 0}
private def half₂ : Set (Fin 1 → ℝ) := {x | (∑ i, (-1 : ℝ) * x i) ≤ 0}

/-- A single halfspace is a polyhedron (intersect it with itself once). -/
private lemma poly_of_half {S : Set (Fin 1 → ℝ)} (h : Ref.IsHalfspace 1 S) :
    Ref.IsPolyhedron 1 S := ⟨1, fun _ => S, fun _ => h, by ext x; simp⟩

/-- `x ↦ max 0 (x 0)` is CPWL in the reference sense: the two halflines
`{x 0 ≤ 0}` and `{-x 0 ≤ 0}` cover `ℝ`, and `f` is affine on each. -/
private lemma mem_ref : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Ref.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2, ![half₁, half₂],
    ![fun _ => 0, fun x => x 0], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact poly_of_half ⟨fun _ => 1, 0, rfl⟩
    · exact poly_of_half ⟨fun _ => -1, 0, rfl⟩
  · intro i
    fin_cases i
    · exact ⟨0, 0, by simp⟩
    · exact ⟨fun _ => 1, 0, by simp⟩
  · refine Set.eq_univ_iff_forall.mpr fun x => Set.mem_iUnion.mpr ?_
    rcases le_or_gt (x 0) 0 with h | h
    · exact ⟨0, by simpa [half₁] using h⟩
    · exact ⟨1, by simpa [half₂] using h.le⟩
  · intro i x hx
    fin_cases i
    · have hx0 : x 0 ≤ 0 := by simpa [half₁] using hx
      simp [hx0, max_eq_left hx0]
    · have hx0 : (0 : ℝ) ≤ x 0 := by simpa [half₂] using hx
      simp [hx0, max_eq_right hx0]

/-- `x ↦ max 0 (x 0)` is **not** in the agent's `CPWL n`: near the origin the
required affine map `a·x + b` would have to satisfy `max 0 t = c*t + b` for all
small `t`, which fails at `t = 0`, `t = ε/2`, `t = -ε/2`. -/
private lemma not_mem_agent (n : ℕ) [NeZero n] :
    (fun x : Fin n → ℝ => max 0 (x 0)) ∉ Agent070.CPWL n := by
  rintro ⟨-, m, g, hga, hnb⟩
  obtain ⟨i, hi⟩ := hnb 0
  obtain ⟨a, b, hgi⟩ := hga i
  have hcont : Continuous (fun t : ℝ => (fun _ => t : Fin n → ℝ)) :=
    continuous_pi fun _ => continuous_id
  have hev := (hcont.tendsto' 0 0 rfl).eventually hi
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have E : ∀ t : ℝ, |t| < ε → max 0 t = (∑ j, a j) * t + b := by
    intro t ht
    have h := hball (show dist t 0 < ε by rwa [Real.dist_eq, sub_zero])
    rw [hgi] at h
    simpa [← Finset.sum_mul] using h
  have e0 := E 0 (by simpa using hε)
  have e1 := E (ε / 2) (by rw [abs_of_pos (by linarith)]; linarith)
  have e2 := E (-(ε / 2)) (by rw [abs_of_neg (by linarith)]; linarith)
  rw [max_self, mul_zero, zero_add] at e0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ ε / 2)] at e1
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0 : ℝ)), mul_neg] at e2
  linarith

/-- The agent's `CPWL` is strictly stronger than the reference's, so the two
definitions denote different sets. -/
theorem cpwl_ne : ∃ n, Agent070.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => not_mem_agent 1 ?_⟩
  rw [h]
  exact mem_ref

/-! ### The statement

The left-hand side is *false*: by `not_mem_agent` the agent's `CPWL n` contains no
`x ↦ max 0 (x 0)`, while that function is a one-hidden-layer ReLU network and
`Agent070.depthBound n ≥ 1`.  The right-hand side is the genuine Theorem 2, which
is true.  So the iff is false — but refuting it means *proving* the right-hand
side, i.e. proving Theorem 2 itself, which is exactly the `sorry` in both files.
Hence neither `statement` nor `statement_ne` is available honestly here. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent070.CPWL n = Agent070.ReLUn n (Agent070.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry
-- Honest `sorry`: the iff is false, but its refutation requires proving `Ref.theorem2`.

end Star_070

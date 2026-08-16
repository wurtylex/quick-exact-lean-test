import QuickTest.Formalizations.Thm2_004
import QuickTest.Reference

/-!
# Star comparison: `Agent004` vs `Ref`

* `depthBound` is *literally* the same expression in both files, so `depth` is `rfl`.
* `ReLUn` agrees: both read "**at most** `k` hidden layers", and `Agent004`'s
  inductive `ReLUNet` computes exactly the functions of `Ref.ComputedBy`.
* `CPWL` does **not** agree.  `Agent004` phrases piecewise-linearity as *local*
  agreement (`∀ᶠ y in nhds x`) with a member of a finite affine family.  On a
  connected domain that forces the function to be globally affine, so it is
  strictly stronger than the reference's polyhedral-cover condition.  Refuted
  below as `cpwl_ne`.
-/

namespace Star_004

/-! ### `depthBound` -/

/-- Both files write `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1` verbatim. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent004.depthBound n = Ref.depthBound n := rfl

/-! ### `ReLUn` -/

/-- `Ref.ComputedBy n k` (a recursive predicate) and `Agent004.ReLUNet n k` (an
inductive family of network terms) describe the same functions, layer by layer. -/
private lemma computedBy_iff :
    ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
      Ref.ComputedBy n k f ↔ ∃ net : Agent004.ReLUNet n k, f = net.eval := by
  intro k
  induction k with
  | zero =>
    intro n f
    show (∃ T : Ref.Aff n 1, ∀ x, f x = T.eval x 0) ↔ _
    constructor
    · rintro ⟨T, hT⟩
      exact ⟨Agent004.ReLUNet.last ⟨T.M, T.c⟩, by funext x; exact hT x⟩
    · rintro ⟨net, rfl⟩
      cases net with
      | last T => exact ⟨⟨T.A, T.c⟩, fun x => rfl⟩
  | succ k ih =>
    intro n f
    show (∃ (m : ℕ) (T : Ref.Aff n m) (g : (Fin m → ℝ) → ℝ),
        Ref.ComputedBy m k g ∧ ∀ x, f x = g (Ref.reluVec (T.eval x))) ↔ _
    constructor
    · rintro ⟨m, T, g, hgk, hf⟩
      obtain ⟨net, rfl⟩ := (ih m g).1 hgk
      exact ⟨Agent004.ReLUNet.step ⟨T.M, T.c⟩ net, by funext x; exact hf x⟩
    · rintro ⟨net, rfl⟩
      cases net with
      | step T rest =>
        exact ⟨_, ⟨T.A, T.c⟩, rest.eval, (ih _ _).2 ⟨rest, rfl⟩, fun x => rfl⟩

theorem relun (n k : ℕ) : Agent004.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent004.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, net, rfl⟩
    exact ⟨j, hj, (computedBy_iff j n _).2 ⟨net, rfl⟩⟩
  · rintro ⟨j, hj, hf⟩
    obtain ⟨net, rfl⟩ := (computedBy_iff j n f).1 hf
    exact ⟨j, hj, net, rfl⟩

/-! ### `CPWL` : refutation -/

private lemma halfspace_polyhedron {n : ℕ} {S : Set (Fin n → ℝ)}
    (h : Ref.IsHalfspace n S) : Ref.IsPolyhedron n S :=
  ⟨1, fun _ => S, fun _ => h, by rw [Set.iInter_const]⟩

/-- `x ↦ max 0 (x 0)` is CPWL in the reference sense: the two halflines
`{x 0 ≤ 0}` and `{-x 0 ≤ 0}` are polyhedra covering `ℝ¹`. -/
private lemma witness_mem :
    (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Ref.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2,
    ![{x : Fin 1 → ℝ | x 0 ≤ 0}, {x : Fin 1 → ℝ | -(x 0) ≤ 0}],
    ![fun _ => 0, fun x => x 0], ?_, ?_, ?_, ?_⟩
  · refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · exact halfspace_polyhedron ⟨fun _ => 1, 0, by ext x; simp⟩
    · exact halfspace_polyhedron ⟨fun _ => -1, 0, by ext x; simp⟩
  · refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · exact ⟨fun _ => 0, 0, fun x => by simp⟩
    · exact ⟨fun _ => 1, 0, fun x => by simp⟩
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    rcases le_total (x 0) 0 with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  · refine Fin.forall_fin_two.2 ⟨fun x hx => ?_, fun x hx => ?_⟩
    · simp only [Matrix.cons_val_zero, Set.mem_setOf_eq] at hx ⊢
      exact max_eq_left hx
    · have hx' : (0 : ℝ) ≤ x 0 := by simpa using hx
      show max (0 : ℝ) (x 0) = x 0
      exact max_eq_right hx'

/-- `x ↦ max 0 (x 0)` is *not* CPWL in `Agent004`'s sense: local agreement with a
single affine functional at the origin forces `max 0 y = a * y + c` on a whole
interval around `0`, which is impossible. -/
private lemma witness_not_mem :
    (fun x : Fin 1 → ℝ => max 0 (x 0)) ∉ Agent004.CPWL 1 := by
  rintro ⟨-, m, g, hg⟩
  obtain ⟨i, hi⟩ := hg (fun _ => (0 : ℝ))
  have hi' : ∀ᶠ y : Fin 1 → ℝ in nhds (fun _ => (0 : ℝ)),
      max 0 (y 0) = (g i).a 0 * y 0 + (g i).c := by
    filter_upwards [hi] with y hy
    simpa [Agent004.AffFunctional.eval, Fin.sum_univ_one] using hy
  have htend : Filter.Tendsto (fun t : ℝ => (fun _ => t : Fin 1 → ℝ))
      (nhds 0) (nhds (fun _ => (0 : ℝ))) :=
    (continuous_pi fun _ => continuous_id).tendsto 0
  have key : ∀ᶠ t : ℝ in nhds 0, max 0 t = (g i).a 0 * t + (g i).c :=
    htend.eventually hi'
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 key
  have h0 : max (0 : ℝ) 0 = (g i).a 0 * 0 + (g i).c := by
    refine hball ?_
    simpa using hε
  have hp : max (0 : ℝ) (ε / 2) = (g i).a 0 * (ε / 2) + (g i).c := by
    refine hball ?_
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
    linarith
  have hn : max (0 : ℝ) (-(ε / 2)) = (g i).a 0 * (-(ε / 2)) + (g i).c := by
    refine hball ?_
    rw [Real.dist_eq, sub_zero, abs_of_neg (by linarith)]
    linarith
  rw [max_self] at h0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ ε / 2)] at hp
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0 : ℝ))] at hn
  have hring : (g i).a 0 * (ε / 2) + (g i).a 0 * (-(ε / 2)) = 0 := by ring
  have hzero : (g i).a 0 * (0 : ℝ) = 0 := by ring
  linarith

/-- `Agent004.CPWL` is strictly stronger than `Ref.CPWL`; already at `n = 1`
they differ, witnessed by `x ↦ max 0 (x 0)`. -/
theorem cpwl_ne : ∃ n, Agent004.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => witness_not_mem ?_⟩
  rw [h]
  exact witness_mem

/-! ### The statement -/

/-- Honest `sorry`.  The left-hand side is *false* (for `n ≥ 3` the
neighbourhood definition again collapses to the globally affine functions, while
`ReLUn n (depthBound n)` contains non-affine functions), so `statement` is false
and `statement_ne` is the true form.  But proving `statement_ne` requires
establishing the right-hand side, i.e. the actual content of Theorem 2, which is
`sorry`-ed in both `Ref` and `Agent004`.  Routing through `Ref.theorem2` would
prove nothing, so this is left open. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent004.CPWL n = Agent004.ReLUn n (Agent004.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_004

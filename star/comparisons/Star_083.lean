/-!
# Star comparison: `Agent083` vs `Ref`

`Agent083` is in the *polyhedral subdivision* family: its `CPWL` asks for a finite
cover of `ℝⁿ` by **closed convex** pieces carrying affine functions, while `Ref`
asks for a finite cover by **polyhedra**.  Every polyhedron is closed and convex,
so `Ref.CPWL n ⊆ Agent083.CPWL n` is proved below in full.  The converse is the
genuine mathematical content and is left as an honest `sorry` (see
`agent_subset_ref`).

`ReLUn` matches exactly (both files say *at most* `k` hidden layers, and the two
network encodings — a `Prop`-valued recursion versus an inductive `Type` — are
proved equivalent below), and `depthBound` is literally the same expression.
-/

namespace Star_083

/-- The halfspace `{x | ∑ i, a i * x i ≤ b}` is convex. -/
private lemma convex_halfspace_sum (n : ℕ) (a : Fin n → ℝ) (b : ℝ) :
    Convex ℝ {x : Fin n → ℝ | (∑ i, a i * x i) ≤ b} := by
  intro x hx y hy s t hs ht hst
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  have key : ∑ i, a i * (s • x + t • y) i
      = s * (∑ i, a i * x i) + t * (∑ i, a i * y i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [key]
  calc s * (∑ i, a i * x i) + t * (∑ i, a i * y i)
      ≤ s * b + t * b :=
        add_le_add (mul_le_mul_of_nonneg_left hx hs) (mul_le_mul_of_nonneg_left hy ht)
    _ = b := by rw [← add_mul, hst, one_mul]

/-- `x ↦ ∑ i, a i * x i` is continuous. -/
private lemma contLin (n : ℕ) (a : Fin n → ℝ) :
    Continuous (fun x : Fin n → ℝ => ∑ i, a i * x i) :=
  continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_apply i)

/-- A `Ref` polyhedron is closed and convex, which is exactly what `Agent083`
demands of its pieces. -/
private lemma polyhedron_convex_closed {n : ℕ} {S : Set (Fin n → ℝ)}
    (h : Ref.IsPolyhedron n S) : Convex ℝ S ∧ IsClosed S := by
  obtain ⟨m, H, hH, rfl⟩ := h
  constructor
  · refine convex_iInter fun i => ?_
    obtain ⟨a, b, hEq⟩ := hH i
    rw [hEq]
    exact convex_halfspace_sum n a b
  · refine isClosed_iInter fun i => ?_
    obtain ⟨a, b, hEq⟩ := hH i
    rw [hEq]
    exact isClosed_le (contLin n a) continuous_const

private lemma ref_subset_agent (n : ℕ) : Ref.CPWL n ⊆ Agent083.CPWL n := by
  intro f hf
  simp only [Ref.CPWL, Ref.IsCPWL, Set.mem_setOf_eq] at hf
  obtain ⟨hcont, m, P, g, hP, hg, hcov, hagr⟩ := hf
  refine ⟨hcont, m, P, g, fun i => ?_, fun i => (polyhedron_convex_closed (hP i)).1,
    fun i => (polyhedron_convex_closed (hP i)).2, hcov, hagr⟩
  obtain ⟨a, b, h⟩ := hg i
  exact ⟨a, b, h⟩

/-- The missing ingredient.  Given a continuous `f` and a finite cover of `ℝⁿ` by
closed convex sets on which `f` is affine, one must *refine* the cover to a
polyhedral one: take the hyperplane arrangement `{x | g i x = g j x}` over the
finitely many affine pieces, whose closed cells are polyhedra covering `ℝⁿ`, and
show `f` agrees with a single `g i` on each cell (the ordering of the `g i` is
constant on a cell, and a Baire-type argument gives one piece with interior in
the cell; continuity plus connectedness of the cell then propagates the
agreement).  Mathlib has neither hyperplane arrangements nor this refinement, so
this direction is left as an honest `sorry`. -/
private lemma agent_subset_ref (n : ℕ) : Agent083.CPWL n ⊆ Ref.CPWL n := by
  sorry

theorem cpwl (n : ℕ) : Agent083.CPWL n = Ref.CPWL n :=
  Set.Subset.antisymm (agent_subset_ref n) (ref_subset_agent n)

/-- The inductive network type of `Agent083` and the `Prop`-valued recursion of
`Ref` describe the same class of functions, layer count by layer count. -/
private lemma exact_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent083.IsRepresentableExact n k f ↔ Ref.ComputedBy n k f := by
  intro k
  induction k with
  | zero =>
    intro n f
    simp only [Agent083.IsRepresentableExact, Ref.ComputedBy]
    constructor
    · rintro ⟨net, hnet⟩
      cases net with
      | output T =>
        refine ⟨⟨T.A, T.c⟩, fun x => ?_⟩
        simpa [Agent083.ReLUNet.eval, Agent083.AffineTransform.apply, Ref.Aff.eval] using hnet x
    · rintro ⟨T, hT⟩
      refine ⟨Agent083.ReLUNet.output ⟨T.M, T.c⟩, fun x => ?_⟩
      simpa [Agent083.ReLUNet.eval, Agent083.AffineTransform.apply, Ref.Aff.eval] using hT x
  | succ k ih =>
    intro n f
    simp only [Agent083.IsRepresentableExact, Ref.ComputedBy]
    constructor
    · rintro ⟨net, hnet⟩
      cases net with
      | @layer n' m k' T rest =>
        simp only [Agent083.ReLUNet.eval] at hnet
        refine ⟨m, ⟨T.A, T.c⟩, rest.eval, (ih m rest.eval).mp ⟨rest, fun x => rfl⟩,
          fun x => ?_⟩
        rw [hnet x]
        congr 1
    · rintro ⟨m, T, g, hg, hf⟩
      obtain ⟨net, hnet⟩ := (ih m g).mpr hg
      refine ⟨Agent083.ReLUNet.layer ⟨T.M, T.c⟩ net, fun x => ?_⟩
      have harg : Ref.reluVec (T.eval x)
          = Agent083.reluVec ((⟨T.M, T.c⟩ : Agent083.AffineTransform n m).apply x) := by
        funext i
        simp [Ref.reluVec, Agent083.reluVec, Ref.relu, Agent083.relu, Ref.Aff.eval,
          Agent083.AffineTransform.apply]
      simp only [Agent083.ReLUNet.eval]
      rw [hf x, hnet, harg]

theorem relun (n k : ℕ) : Agent083.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent083.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, (exact_iff j n f).mp h⟩
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, (exact_iff j n f).mpr h⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent083.depthBound n = Ref.depthBound n := rfl

theorem statement :
    (∀ n, 3 ≤ n → Agent083.CPWL n = Agent083.ReLUn n (Agent083.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
  constructor
  · intro h n hn
    rw [← cpwl n, ← relun, ← depth n hn]
    exact h n hn
  · intro h n hn
    rw [cpwl n, relun, depth n hn]
    exact h n hn

end Star_083

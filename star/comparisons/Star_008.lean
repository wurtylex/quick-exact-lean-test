/-!
# Star comparison for Agent 008

Agent 008 is a *faithful* formalization: `ReLUn` is "at most `k` hidden layers"
(inductive predicate instead of the reference's recursive one), `CPWL` is the
honest polyhedral-subdivision definition (matrix-form polyhedra and affine maps
instead of the reference's halfspace/`IsAffine` form), and `depthBound` is
literally the same expression.  All four obligations are provable.
-/

namespace Star_008

/-! ### Polyhedra: matrix form versus intersection-of-halfspaces form -/

/-- A matrix-form polyhedron `{x | A x ≤ b}` is a finite intersection of halfspaces. -/
private lemma ref_poly_of_agent_poly {n : ℕ} {P : Set (Fin n → ℝ)}
    (h : Agent008.IsPolyhedron P) : Ref.IsPolyhedron n P := by
  obtain ⟨m, A, b, rfl⟩ := h
  refine ⟨m, fun i => {x | (∑ j, A i j * x j) ≤ b i},
    fun i => ⟨fun j => A i j, b i, rfl⟩, ?_⟩
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iInter]
  exact ⟨fun hx i => Pi.le_def.1 hx i, fun hx => Pi.le_def.2 fun i => hx i⟩

/-- A finite intersection of halfspaces is a matrix-form polyhedron. -/
private lemma agent_poly_of_ref_poly {n : ℕ} {P : Set (Fin n → ℝ)}
    (h : Ref.IsPolyhedron n P) : Agent008.IsPolyhedron P := by
  obtain ⟨m, H, hH, rfl⟩ := h
  choose a b hab using hH
  refine ⟨m, Matrix.of fun i j => a i j, b, ?_⟩
  ext x
  simp only [Set.mem_iInter, hab, Set.mem_setOf_eq]
  exact ⟨fun hx => Pi.le_def.2 fun i => hx i, fun hx i => Pi.le_def.1 hx i⟩

/-! ### The two `CPWL` definitions agree -/

/-- Both files define `CPWL` as "continuous, plus a finite polyhedral cover on each
piece of which `f` is affine"; only the encoding of the pieces and of the affine
functionals differs. -/
theorem cpwl (n : ℕ) : Agent008.CPWL n = Ref.CPWL n := by
  ext f
  constructor
  · rintro ⟨hf, m, P, g, hP, hcov, hagree⟩
    exact ⟨hf, m, P, fun i x => (g i).apply x 0, fun i => ref_poly_of_agent_poly (hP i),
      fun i => ⟨fun j => (g i).A 0 j, (g i).c 0, fun _ => rfl⟩, hcov, hagree⟩
  · rintro ⟨hf, m, P, g, hP, hg, hcov, hagree⟩
    choose a b hab using hg
    refine ⟨hf, m, P, fun i => ⟨Matrix.of fun _ j => a i j, fun _ => b i⟩,
      fun i => agent_poly_of_ref_poly (hP i), hcov, ?_⟩
    intro i x hx
    rw [hagree i x hx]
    exact hab i x

/-! ### The two network definitions agree -/

/-- The agent's inductive `NetworkComputes` implies the reference's recursive
`ComputedBy`. -/
private lemma ref_computedBy_of_agent {n k : ℕ} {f : (Fin n → ℝ) → ℝ}
    (h : Agent008.NetworkComputes n k f) : Ref.ComputedBy n k f := by
  induction h with
  | @base n T => exact ⟨⟨T.A, T.c⟩, fun _ => rfl⟩
  | @step n m k T g hg ih => exact ⟨m, ⟨T.A, T.c⟩, g, ih, fun _ => rfl⟩

/-- The reference's recursive `ComputedBy` implies the agent's inductive
`NetworkComputes`. -/
private lemma agent_networkComputes_of_ref :
    ∀ {k n : ℕ} {f : (Fin n → ℝ) → ℝ}, Ref.ComputedBy n k f →
      Agent008.NetworkComputes n k f := by
  intro k
  induction k with
  | zero =>
    intro n f h
    obtain ⟨T, hT⟩ := h
    have hfe : f = fun x => (⟨T.M, T.c⟩ : Agent008.AffineMap' n 1).apply x 0 := funext hT
    rw [hfe]
    exact Agent008.NetworkComputes.base _
  | succ k ih =>
    intro n f h
    obtain ⟨m, T, g, hg, hf⟩ := h
    have hfe : f = fun x =>
        g (Agent008.reluVec ((⟨T.M, T.c⟩ : Agent008.AffineMap' n m).apply x)) := funext hf
    rw [hfe]
    exact Agent008.NetworkComputes.step _ (ih hg)

/-- Both files read `ReLU_{n,k}` as "**at most** `k` hidden layers", so no padding
identity is needed here: the two layer relations are directly interderivable. -/
theorem relun (n k : ℕ) : Agent008.ReLUn n k = Ref.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, ref_computedBy_of_agent hf⟩
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, agent_networkComputes_of_ref hf⟩

/-! ### The depth bounds agree -/

/-- The two depth bounds are the *same* expression `⌈logb 3 (n-1)⌉₊ + 1`. -/
private lemma depthBound_eq (n : ℕ) : Agent008.depthBound n = Ref.depthBound n := rfl

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent008.depthBound n = Ref.depthBound n :=
  depthBound_eq n

/-! ### The statements agree -/

theorem statement :
    (∀ n, 3 ≤ n → Agent008.CPWL n = Agent008.ReLUn n (Agent008.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
  constructor
  · intro h n hn
    rw [← cpwl n, ← relun n (Ref.depthBound n), ← depthBound_eq n]
    exact h n hn
  · intro h n hn
    rw [cpwl n, relun n (Agent008.depthBound n), depthBound_eq n]
    exact h n hn

end Star_008

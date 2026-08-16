import QuickTest.Formalizations.Thm2_088
import QuickTest.Reference

/-!
# Star comparison for Agent 088

Agent 088 is a *faithful* formalization.

* `CPWL n` is the honest polyhedral-subdivision definition: continuous, plus a
  finite family of polyhedra covering `ℝⁿ` on each of which `f` agrees with an
  affine functional.  This is **not** the refutable neighbourhood-agreement
  family — there is no `nhds`/`∃ ε > 0` anywhere in the file.  Only the
  *encoding* differs from the reference: a polyhedron is written directly as
  `{x | ∀ j, ⟪a j, x⟫ ≤ b j}` rather than as an intersection of halfspaces, and
  the affine functional is packaged inside `IsAffineOn` rather than supplied as a
  separate family `g` of affine functions.
* `ReLUn n k` is "**at most** `k` hidden layers" on both sides, so no padding
  identity is needed; the recursions match layer for layer, with the reference's
  `Aff`/`mulVec` encoding replaced by an explicit matrix/bias pair.
* `depthBound` is literally the same expression `⌈Real.logb 3 (n-1)⌉₊ + 1`.

All four obligations are provable.
-/

namespace Star_088

/-! ### Polyhedra: inequality-system form versus intersection-of-halfspaces form -/

/-- `{x | ∀ j, ⟪a j, x⟫ ≤ b j}` is a finite intersection of halfspaces. -/
private lemma ref_poly_of_agent_poly {n : ℕ} {P : Set (Fin n → ℝ)}
    (h : Agent088.IsPolyhedron n P) : Ref.IsPolyhedron n P := by
  obtain ⟨m, a, b, rfl⟩ := h
  refine ⟨m, fun j => {x | (∑ i, a j i * x i) ≤ b j},
    fun j => ⟨a j, b j, rfl⟩, ?_⟩
  ext x
  constructor
  · intro hx
    exact Set.mem_iInter.2 fun j => hx j
  · intro hx j
    exact Set.mem_iInter.1 hx j

/-- A finite intersection of halfspaces is cut out by an inequality system. -/
private lemma agent_poly_of_ref_poly {n : ℕ} {P : Set (Fin n → ℝ)}
    (h : Ref.IsPolyhedron n P) : Agent088.IsPolyhedron n P := by
  obtain ⟨m, H, hH, rfl⟩ := h
  choose a b hab using hH
  refine ⟨m, a, b, ?_⟩
  ext x
  simp only [Set.mem_iInter, hab, Set.mem_setOf_eq]

/-! ### The two `CPWL` definitions agree -/

/-- Both files define `CPWL` as "continuous, plus a finite polyhedral cover of
`ℝⁿ` on each piece of which `f` is affine"; only the encoding of the pieces and
the placement of the affine functional differ. -/
theorem cpwl (n : ℕ) : Agent088.CPWL n = Ref.CPWL n := by
  ext f
  constructor
  · rintro ⟨hf, m, P, hP, hcov, haff⟩
    choose a b hab using haff
    exact ⟨hf, m, P, fun j x => (∑ i, a j i * x i) + b j,
      fun j => ref_poly_of_agent_poly (hP j), fun j => ⟨a j, b j, fun _ => rfl⟩,
      hcov, hab⟩
  · rintro ⟨hf, m, P, g, hP, hg, hcov, hagree⟩
    choose a b hab using hg
    refine ⟨hf, m, P, fun j => agent_poly_of_ref_poly (hP j), hcov, ?_⟩
    intro j
    exact ⟨a j, b j, fun x hx => by rw [hagree j x hx, hab j x]⟩

/-! ### The two network definitions agree -/

/-- The agent's recursion on the number of hidden layers is the reference's
recursion with `Aff.eval` spelled out as `x ↦ (∑ j, A i j * x j) + c i`. -/
private lemma computed_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent088.IsComputedByReLUNetwork n k f ↔ Ref.ComputedBy n k f := by
  intro k
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨a, b, rfl⟩
      exact ⟨⟨Matrix.of fun _ j => a j, fun _ => b⟩, fun _ => rfl⟩
    · rintro ⟨T, hT⟩
      exact ⟨fun j => T.M 0 j, T.c 0, funext hT⟩
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, A, c, g, hg, rfl⟩
      exact ⟨m, ⟨A, c⟩, g, (ih m g).1 hg, fun _ => rfl⟩
    · rintro ⟨m, T, g, hg, hf⟩
      exact ⟨m, T.M, T.c, g, (ih m g).2 hg, funext hf⟩

/-- Both files read `ReLU_{n,k}` as "**at most** `k` hidden layers", so no
padding identity is needed here. -/
theorem relun (n k : ℕ) : Agent088.ReLUn n k = Ref.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (computed_iff j n f).1 hf⟩
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (computed_iff j n f).2 hf⟩

/-! ### The depth bounds agree -/

/-- The two depth bounds are the *same* expression `⌈logb 3 (n-1)⌉₊ + 1`
(`⌈·⌉₊` is notation for `Nat.ceil`). -/
private lemma depthBound_eq (n : ℕ) : Agent088.depthBound n = Ref.depthBound n := rfl

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent088.depthBound n = Ref.depthBound n :=
  depthBound_eq n

/-! ### The statements agree -/

theorem statement :
    (∀ n, 3 ≤ n → Agent088.CPWL n = Agent088.ReLUn n (Agent088.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
  constructor
  · intro h n hn
    rw [← cpwl n, ← relun n (Ref.depthBound n), ← depthBound_eq n]
    exact h n hn
  · intro h n hn
    rw [cpwl n, relun n (Agent088.depthBound n), depthBound_eq n]
    exact h n hn

end Star_088

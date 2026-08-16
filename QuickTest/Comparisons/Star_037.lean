import QuickTest.Formalizations.Thm2_037
import QuickTest.Reference

namespace Star_037

/-!
# Agent037 vs the reference

Agent037 is a *faithful* copy of the reference, up to bookkeeping:

* `depthBound`  — literally the same term (`Nat.ceil` vs `⌈·⌉₊` is notation), so `rfl`.
* `ReLUn`       — the same "at most `k` hidden layers" reading; only the affine-map
  record differs (`Agent037.AffineMap` with fields `A, c` vs `Ref.Aff` with fields
  `M, c`), so the two recursive predicates transport into one another field by field.
* `CPWL`        — the same genuine polyhedral-subdivision condition.  Two cosmetic
  differences: Agent037 inlines the halfspaces of a polyhedron as
  `{x | ∀ i, ⟨a i, x⟩ ≤ b i}` where the reference writes `⋂ i, H i` with each `H i`
  a halfspace, and Agent037 states the covering condition pointwise
  (`∀ x, ∃ i, x ∈ P i`) where the reference writes `⋃ i, P i = univ`.  Both are
  genuine equivalences, so `cpwl` is **true** and proved below.

Consequently `statement` is proved outright, by transporting along the three
equalities — no appeal to either (`sorry`-ed) `theorem2`.
-/

/-! ### Networks -/

/-- The two network predicates agree; only the affine-map record differs. -/
private lemma computes_iff :
    ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ), Agent037.computesReLU k n f ↔ Ref.ComputedBy n k f := by
  intro k
  induction k with
  | zero =>
    intro n f
    constructor
    · intro h
      obtain ⟨T, hT⟩ : ∃ T : Agent037.AffineMap n 1, ∀ x, f x = T.eval x 0 := h
      show ∃ T : Ref.Aff n 1, ∀ x, f x = T.eval x 0
      exact ⟨⟨T.A, T.c⟩, hT⟩
    · intro h
      obtain ⟨T, hT⟩ : ∃ T : Ref.Aff n 1, ∀ x, f x = T.eval x 0 := h
      show ∃ T : Agent037.AffineMap n 1, ∀ x, f x = T.eval x 0
      exact ⟨⟨T.M, T.c⟩, hT⟩
  | succ k ih =>
    intro n f
    constructor
    · intro h
      obtain ⟨m, T, g, hg, hf⟩ :
          ∃ (m : ℕ) (T : Agent037.AffineMap n m) (g : (Fin m → ℝ) → ℝ),
            Agent037.computesReLU k m g ∧ ∀ x, f x = g (Agent037.reluVec (T.eval x)) := h
      show ∃ (m : ℕ) (T : Ref.Aff n m) (g : (Fin m → ℝ) → ℝ),
          Ref.ComputedBy m k g ∧ ∀ x, f x = g (Ref.reluVec (T.eval x))
      exact ⟨m, ⟨T.A, T.c⟩, g, (ih m g).mp hg, hf⟩
    · intro h
      obtain ⟨m, T, g, hg, hf⟩ :
          ∃ (m : ℕ) (T : Ref.Aff n m) (g : (Fin m → ℝ) → ℝ),
            Ref.ComputedBy m k g ∧ ∀ x, f x = g (Ref.reluVec (T.eval x)) := h
      show ∃ (m : ℕ) (T : Agent037.AffineMap n m) (g : (Fin m → ℝ) → ℝ),
          Agent037.computesReLU k m g ∧ ∀ x, f x = g (Agent037.reluVec (T.eval x))
      exact ⟨m, ⟨T.M, T.c⟩, g, (ih m g).mpr hg, hf⟩

theorem relun (n k : ℕ) : Agent037.ReLUn n k = Ref.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨j, hj, h⟩; exact ⟨j, hj, (computes_iff j n f).mp h⟩
  · rintro ⟨j, hj, h⟩; exact ⟨j, hj, (computes_iff j n f).mpr h⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent037.depthBound n = Ref.depthBound n := rfl

/-! ### Polyhedra and `CPWL` -/

/-- Agent037's inlined "system of linear inequalities" description of a polyhedron and the
reference's "finite intersection of halfspaces" description define the same sets. -/
private lemma poly_iff (n : ℕ) (S : Set (Fin n → ℝ)) :
    Agent037.IsPolyhedron n S ↔ Ref.IsPolyhedron n S := by
  constructor
  · rintro ⟨m, a, b, hS⟩
    refine ⟨m, fun i => {x | (∑ j, a i j * x j) ≤ b i}, fun i => ⟨a i, b i, rfl⟩, ?_⟩
    rw [hS]
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
  · rintro ⟨m, H, hH, hS⟩
    choose a b hab using hH
    refine ⟨m, a, b, ?_⟩
    ext x
    constructor
    · intro hx i
      have hxi : x ∈ H i := by rw [hS] at hx; exact Set.mem_iInter.mp hx i
      rw [hab i] at hxi
      exact hxi
    · intro hx
      rw [hS]
      refine Set.mem_iInter.mpr fun i => ?_
      rw [hab i]
      exact hx i

/-- The two affineness predicates are literally the same proposition. -/
private lemma affine_iff (n : ℕ) (g : (Fin n → ℝ) → ℝ) :
    Agent037.IsAffineFn n g ↔ Ref.IsAffine g := Iff.rfl

/-- The `CPWL` definitions agree: both are the honest polyhedral-subdivision condition. -/
theorem cpwl (n : ℕ) : Agent037.CPWL n = Ref.CPWL n := by
  ext f
  constructor
  · rintro ⟨hc, m, P, g, hP, hg, hcov, hagr⟩
    refine ⟨hc, m, P, g, fun i => (poly_iff n (P i)).mp (hP i),
      fun i => (affine_iff n (g i)).mp (hg i), ?_, hagr⟩
    refine Set.eq_univ_of_forall fun x => ?_
    exact Set.mem_iUnion.mpr (hcov x)
  · rintro ⟨hc, m, P, g, hP, hg, hcov, hagr⟩
    refine ⟨hc, m, P, g, fun i => (poly_iff n (P i)).mpr (hP i),
      fun i => (affine_iff n (g i)).mpr (hg i), ?_, hagr⟩
    intro x
    have hx : x ∈ ⋃ i, P i := by rw [hcov]; exact Set.mem_univ x
    exact Set.mem_iUnion.mp hx

/-! ### The two statements of Theorem 2 -/

/-- Since all three ingredients coincide, the two readings of Theorem 2 are equivalent.
This is proved by transport, not by invoking either (`sorry`-ed) `theorem2`. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent037.CPWL n = Agent037.ReLUn n (Agent037.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
  constructor
  · intro h n hn
    have hn' := h n hn
    rw [cpwl n, depth n hn, relun n (Ref.depthBound n)] at hn'
    exact hn'
  · intro h n hn
    have hn' := h n hn
    rw [← cpwl n, ← depth n hn, ← relun n (Agent037.depthBound n)] at hn'
    exact hn'

end Star_037

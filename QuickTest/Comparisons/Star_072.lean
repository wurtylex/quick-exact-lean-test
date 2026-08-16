import QuickTest.Formalizations.Thm2_072
import QuickTest.Reference

/-!
# Star comparison: `Agent072` vs `Ref`

Agent 072 makes exactly the same modelling choices as the reference:

* `CPWL` is the honest polyhedral-subdivision condition (continuity plus a finite
  polyhedral cover with an affine functional on each piece) — **not** the
  neighbourhood-agreement variant, so it is genuinely equal to `Ref.CPWL`.
  The only difference is bookkeeping: the reference packages a polyhedron as an
  intersection `⋂ i, H i` of sets each of which *is* a halfspace, while 072 writes
  the same set as `{x | ∀ i, ⟪a i, x⟫ ≤ b i}`; and 072 states affineness /
  network-agreement as an equality of functions where the reference uses `∀ x`.
* `ReLUn` is *at most* `k` hidden layers on both sides, and the recursion defining
  a network is the same, peeled from the input side.  So even `relun` — usually
  the hard obligation — is provable here, by induction on the depth.
* `depthBound` is literally the same expression, so `depth` is `rfl`.
-/

namespace Star_072

/-! ### Dictionary between the two affine-map structures -/

/-- 072's `AffineT` viewed as a reference `Aff`. -/
private def toAff {a b : ℕ} (T : Agent072.AffineT a b) : Ref.Aff a b := ⟨T.A, T.c⟩

/-- A reference `Aff` viewed as one of 072's `AffineT`. -/
private def ofAff {a b : ℕ} (T : Ref.Aff a b) : Agent072.AffineT a b := ⟨T.M, T.c⟩

/-! ### The two `CPWL` ingredients agree -/

/-- 072's `isAffineFunctional` (an equality of functions) is the reference's
`IsAffine` (a pointwise equation). -/
private lemma isAffine_iff {n : ℕ} (g : (Fin n → ℝ) → ℝ) :
    Agent072.isAffineFunctional n g ↔ Ref.IsAffine g := by
  constructor
  · rintro ⟨c, d, rfl⟩
    exact ⟨c, d, fun _ => rfl⟩
  · rintro ⟨a, b, h⟩
    exact ⟨a, b, funext h⟩

/-- 072's `isPolyhedron` (one conjunction of inequalities) is the reference's
`IsPolyhedron` (an intersection of halfspaces). -/
private lemma isPolyhedron_iff {n : ℕ} (S : Set (Fin n → ℝ)) :
    Agent072.isPolyhedron n S ↔ Ref.IsPolyhedron n S := by
  constructor
  · rintro ⟨m, a, b, rfl⟩
    refine ⟨m, fun i => {x | (∑ j, a i j * x j) ≤ b i}, fun i => ⟨a i, b i, rfl⟩, ?_⟩
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
  · rintro ⟨m, H, hH, rfl⟩
    choose a b hab using hH
    refine ⟨m, a, b, ?_⟩
    ext x
    simp only [Set.mem_iInter, hab, Set.mem_setOf_eq]

/-- The two `CPWL` definitions denote the same set of functions. -/
theorem cpwl (n : ℕ) : Agent072.CPWL n = Ref.CPWL n := by
  ext f
  simp only [Agent072.CPWL, Ref.CPWL, Ref.IsCPWL, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hc, m, P, g, hP, hg, hcov, hagree⟩
    exact ⟨hc, m, P, g, fun i => (isPolyhedron_iff _).1 (hP i),
      fun i => (isAffine_iff _).1 (hg i), hcov, hagree⟩
  · rintro ⟨hc, m, P, g, hP, hg, hcov, hagree⟩
    exact ⟨hc, m, P, g, fun i => (isPolyhedron_iff _).2 (hP i),
      fun i => (isAffine_iff _).2 (hg i), hcov, hagree⟩

/-! ### The two network predicates agree -/

/-- `IsReLUNet` and `ComputedBy` are the same recursion; they differ only in
stating the output layer as `f = fun x => …` versus `∀ x, f x = …`, and in the
structure used for affine maps.  Induction on the depth `k`, generalising the
input dimension `n` (which changes at every layer). -/
private lemma isReLUNet_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent072.IsReLUNet n k f ↔ Ref.ComputedBy n k f := by
  intro k
  induction k with
  | zero =>
    intro n f
    simp only [Agent072.IsReLUNet, Ref.ComputedBy]
    constructor
    · rintro ⟨T, rfl⟩
      exact ⟨toAff T, fun _ => rfl⟩
    · rintro ⟨T, h⟩
      exact ⟨ofAff T, funext h⟩
  | succ k ih =>
    intro n f
    simp only [Agent072.IsReLUNet, Ref.ComputedBy]
    constructor
    · rintro ⟨m, T, g, hg, rfl⟩
      exact ⟨m, toAff T, g, (ih m g).1 hg, fun _ => rfl⟩
    · rintro ⟨m, T, g, hg, h⟩
      exact ⟨m, ofAff T, g, (ih m g).2 hg, funext h⟩

/-- Both files read `ReLU_{n,k}` as *at most* `k` hidden layers, so the sets are
equal — no padding lemma is needed. -/
theorem relun (n k : ℕ) : Agent072.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent072.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, (isReLUNet_iff j n f).1 h⟩
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, (isReLUNet_iff j n f).2 h⟩

/-- Both files define the depth bound as `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent072.depthBound n = Ref.depthBound n := rfl

/-- Consequently the two statements of Theorem 2 are equivalent — proved from the
three componentwise equalities above, not by routing through either (`sorry`-ed)
`theorem2`. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent072.CPWL n = Agent072.ReLUn n (Agent072.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
  constructor
  · intro h n hn
    rw [← cpwl n, ← relun n (Ref.depthBound n), ← depth n hn]
    exact h n hn
  · intro h n hn
    rw [cpwl n, relun n (Agent072.depthBound n), depth n hn]
    exact h n hn

end Star_072

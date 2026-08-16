import QuickTest.Formalizations.Thm2_049
import QuickTest.Reference

/-!
# Star comparison: `Agent049` vs `Ref`

`Agent049` is a genuine polyhedral-subdivision formalization, and it matches the
reference on every component:

* `IsAffine` differs only by `funext` (`g = fun x => …` versus `∀ x, g x = …`).
* Polyhedra are packaged as one matrix inequality `{x | ∀ i, A.mulVec x i ≤ b i}`
  rather than as a finite intersection of individually-presented halfspaces;
  the two are interchangeable by `choose`, since `A.mulVec x i` is by definition
  `∑ j, A i j * x j`.
* The pieces carry their affine function existentially per piece rather than as a
  family; again a `choose`.
* `ComputesK` and `Ref.ComputedBy` are the same recursion, with `Ref.Aff` inlined
  as a matrix/bias pair, so they agree definitionally layer by layer.
* Both take `ReLUn` to be *at most* `k` hidden layers, so no padding argument is
  needed and `relun` is provable outright.
* `depthBound` is character-for-character the reference definition.

All four obligations are proved; nothing is `sorry`-ed.
-/

namespace Star_049

/-! ### Affine functionals -/

private lemma isAffine_iff (n : ℕ) (g : (Fin n → ℝ) → ℝ) :
    Agent049.IsAffine n g ↔ Ref.IsAffine g := by
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨a, b, fun x => rfl⟩
  · rintro ⟨a, b, h⟩
    exact ⟨a, b, funext h⟩

/-! ### Polyhedra -/

/-- `A.mulVec x i` is by definition the inner product `∑ j, A i j * x j`. -/
private lemma mulVec_apply {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℝ) (x : Fin n → ℝ)
    (i : Fin r) : A.mulVec x i = ∑ j, A i j * x j := rfl

private lemma isPolyhedron_iff (n : ℕ) (P : Set (Fin n → ℝ)) :
    Agent049.IsPolyhedron n P ↔ Ref.IsPolyhedron n P := by
  constructor
  · rintro ⟨r, A, b, rfl⟩
    refine ⟨r, fun i => {x | (∑ j, A i j * x j) ≤ b i}, fun i => ⟨A i, b i, rfl⟩, ?_⟩
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact ⟨fun hx i => hx i, fun hx i => hx i⟩
  · rintro ⟨m, H, hH, rfl⟩
    choose a b hab using hH
    refine ⟨m, Matrix.of a, b, ?_⟩
    ext x
    simp only [Set.mem_iInter, hab, Set.mem_setOf_eq]
    exact ⟨fun hx i => hx i, fun hx i => hx i⟩

/-! ### The four obligations -/

/-- The two `CPWL` definitions agree: both are "continuous, plus a finite
polyhedral cover on each piece of which `f` is affine". -/
theorem cpwl (n : ℕ) : Agent049.CPWL n = Ref.CPWL n := by
  ext f
  constructor
  · rintro ⟨hc, r, P, hP, hcov, hg⟩
    choose g hg1 hg2 using hg
    exact ⟨hc, r, P, g, fun i => (isPolyhedron_iff n (P i)).1 (hP i),
      fun i => (isAffine_iff n (g i)).1 (hg1 i), hcov, fun i x hx => hg2 i hx⟩
  · rintro ⟨hc, m, P, g, hP, hga, hcov, hfg⟩
    exact ⟨hc, m, P, fun i => (isPolyhedron_iff n (P i)).2 (hP i), hcov,
      fun i => ⟨g i, (isAffine_iff n (g i)).2 (hga i), fun x hx => hfg i x hx⟩⟩

/-- `Agent049.ComputesK` and `Ref.ComputedBy` are the same recursion; the only
difference is that the reference bundles the affine map into a structure. -/
private lemma computes_iff (k : ℕ) : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent049.ComputesK n k f ↔ Ref.ComputedBy n k f := by
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨a, b, rfl⟩
      exact ⟨⟨Matrix.of fun _ j => a j, fun _ => b⟩, fun x => rfl⟩
    · rintro ⟨T, hT⟩
      exact ⟨fun j => T.M 0 j, T.c 0, funext fun x => hT x⟩
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, A, c, g, hg, rfl⟩
      exact ⟨m, ⟨A, c⟩, g, (ih m g).1 hg, fun x => rfl⟩
    · rintro ⟨m, T, g, hg, hf⟩
      exact ⟨m, T.M, T.c, g, (ih m g).2 hg, funext fun x => hf x⟩

/-- Both files read `ReLU_{n,k}` as *at most* `k` hidden layers, so the sets are
equal without any padding argument. -/
theorem relun (n k : ℕ) : Agent049.ReLUn n k = Ref.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, (computes_iff j n f).1 h⟩
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, (computes_iff j n f).2 h⟩

/-- Identical definitions `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent049.depthBound n = Ref.depthBound n := rfl

theorem statement :
    (∀ n, 3 ≤ n → Agent049.CPWL n = Agent049.ReLUn n (Agent049.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
  have hd : ∀ n, 3 ≤ n →
      Agent049.ReLUn n (Agent049.depthBound n) = Ref.ReLUn n (Ref.depthBound n) :=
    fun n hn => (relun n (Agent049.depthBound n)).trans
      (congrArg (Ref.ReLUn n) (depth n hn))
  constructor
  · intro h n hn
    exact (cpwl n).symm.trans ((h n hn).trans (hd n hn))
  · intro h n hn
    exact (cpwl n).trans ((h n hn).trans (hd n hn).symm)

end Star_049

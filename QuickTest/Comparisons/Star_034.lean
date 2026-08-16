import QuickTest.Formalizations.Thm2_034
import QuickTest.Reference

namespace Star_034

/-!
# Star comparison: `Agent034` vs `Ref`

* `depthBound` is *literally* the same expression in both files (`⌈Real.logb 3
  ((n : ℝ) - 1)⌉₊ + 1`), so `depth` is `rfl`.
* `ReLUn` agrees: both read "**at most** `k` hidden layers".  `Agent034` packages a
  network as an inductive family `ReLUNet n 1 k` of terms, the reference as a
  recursive predicate `ComputedBy n k`; they compute the same functions, by
  induction on the depth.
* `CPWL` agrees.  `Agent034` is in the honest polyhedral-subdivision family: a
  finite cover of `ℝⁿ` by pieces `{x | ∀ j, ⟪w j, x⟫ + b j ≤ 0}` on each of which
  `f` is affine.  Such a piece is exactly a finite intersection of the reference's
  halfspaces `{x | ⟪a, x⟫ ≤ c}` (take `a = w j`, `c = -b j`), so the two `CPWL`
  sets are equal; the only work is repackaging the cutting data.
-/

/-! ### `depthBound` -/

/-- Both files write `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1` verbatim. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent034.depthBound n = Ref.depthBound n := rfl

/-! ### `ReLUn` -/

/-- `Ref.ComputedBy n k` (a recursive predicate) and `Agent034.ReLUNet n 1 k` (an
inductive family of network terms) describe the same functions, layer by layer.
The affine packagings (`Matrix.mulVec` plus a translation versus an explicit sum)
and the two componentwise ReLUs agree definitionally. -/
private lemma computedBy_iff :
    ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
      Ref.ComputedBy n k f ↔ ∃ net : Agent034.ReLUNet n 1 k, f = fun x => net.eval x 0 := by
  intro k
  induction k with
  | zero =>
    intro n f
    show (∃ T : Ref.Aff n 1, ∀ x, f x = T.eval x 0) ↔ _
    constructor
    · rintro ⟨T, hT⟩
      exact ⟨Agent034.ReLUNet.zero ⟨T.M, T.c⟩, by funext x; exact hT x⟩
    · rintro ⟨net, rfl⟩
      cases net with
      | zero T => exact ⟨⟨T.A, T.c⟩, fun x => rfl⟩
  | succ k ih =>
    intro n f
    show (∃ (m : ℕ) (T : Ref.Aff n m) (g : (Fin m → ℝ) → ℝ),
        Ref.ComputedBy m k g ∧ ∀ x, f x = g (Ref.reluVec (T.eval x))) ↔ _
    constructor
    · rintro ⟨m, T, g, hgk, hf⟩
      obtain ⟨net, rfl⟩ := (ih m g).1 hgk
      exact ⟨Agent034.ReLUNet.succ ⟨T.M, T.c⟩ net, by funext x; exact hf x⟩
    · rintro ⟨net, rfl⟩
      cases net with
      | succ T rest =>
        exact ⟨_, ⟨T.A, T.c⟩, fun y => rest.eval y 0, (ih _ _).2 ⟨rest, rfl⟩, fun x => rfl⟩

theorem relun (n k : ℕ) : Agent034.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent034.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, net, hf⟩
    exact ⟨j, hj, (computedBy_iff j n f).2 ⟨net, funext hf⟩⟩
  · rintro ⟨j, hj, hf⟩
    obtain ⟨net, rfl⟩ := (computedBy_iff j n f).1 hf
    exact ⟨j, hj, net, fun x => rfl⟩

/-! ### `CPWL` -/

/-- The two notions of an affine functional are the same. -/
private lemma isAffine_iff {n : ℕ} (g : (Fin n → ℝ) → ℝ) :
    Agent034.IsAffineFun g ↔ Ref.IsAffine g := by
  constructor
  · rintro ⟨w, b, h⟩; exact ⟨w, b, h⟩
  · rintro ⟨w, b, h⟩; exact ⟨w, b, h⟩

/-- The two descriptions of a polyhedral piece agree: `{x | ∀ j, ⟪w j, x⟫ + b j ≤ 0}`
is the intersection of the halfspaces `{x | ⟪w j, x⟫ ≤ -b j}`, and conversely a finite
intersection of halfspaces is cut out by finitely many inequalities `⟪a j, x⟫ - c j ≤ 0`. -/
private lemma isCPWL_iff (n : ℕ) (f : (Fin n → ℝ) → ℝ) :
    Agent034.IsCPWL f ↔ Ref.IsCPWL n f := by
  constructor
  · rintro ⟨hc, m, P, A, hcov, hpoly, haff, hagree⟩
    refine ⟨hc, m, P, A, fun i => ?_, fun i => (isAffine_iff _).1 (haff i), hcov, hagree⟩
    obtain ⟨ι, w, b, hPi⟩ := hpoly i
    refine ⟨ι, fun j => {x | (∑ l, w j l * x l) ≤ -b j}, fun j => ⟨w j, -b j, rfl⟩, ?_⟩
    rw [hPi]
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact ⟨fun h j => by linarith [h j], fun h j => by linarith [h j]⟩
  · rintro ⟨hc, m, P, A, hpoly, haff, hcov, hagree⟩
    refine ⟨hc, m, P, A, hcov, fun i => ?_, fun i => (isAffine_iff _).2 (haff i), hagree⟩
    obtain ⟨ι, H, hH, hPi⟩ := hpoly i
    choose a c hac using hH
    refine ⟨ι, a, fun j => -c j, ?_⟩
    rw [hPi]
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro h j
      have hj := h j
      rw [hac j, Set.mem_setOf_eq] at hj
      linarith
    · intro h j
      rw [hac j, Set.mem_setOf_eq]
      linarith [h j]

/-- `Agent034.CPWL` is the reference's `CPWL`: both are "continuous, plus a finite
polyhedral cover on each piece of which `f` is affine". -/
theorem cpwl (n : ℕ) : Agent034.CPWL n = Ref.CPWL n := by
  ext f
  exact isCPWL_iff n f

/-! ### The statement of Theorem 2 -/

/-- All three ingredients agree, so the two readings of Theorem 2 are equivalent
(proved directly from `cpwl`, `relun` and `depth`, not via either `theorem2`). -/
theorem statement :
    (∀ n, 3 ≤ n → Agent034.CPWL n = Agent034.ReLUn n (Agent034.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
  constructor
  · intro h n hn
    rw [← cpwl n, ← depth n hn, ← relun n (Agent034.depthBound n)]
    exact h n hn
  · intro h n hn
    rw [cpwl n, relun n (Agent034.depthBound n), depth n hn]
    exact h n hn

end Star_034

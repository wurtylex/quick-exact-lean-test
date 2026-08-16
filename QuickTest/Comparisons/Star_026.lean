import QuickTest.Formalizations.Thm2_026
import QuickTest.Reference

namespace Star_026

/-!
# Comparison of `Agent026` against `Ref`

`Agent026` makes the same three modelling choices as the reference:

* `ReLUn n k` is **at most** `k` hidden layers (`∃ k' ≤ k`), exactly as in `Ref`;
  the only difference is bookkeeping — `Ref` uses an inductive predicate
  `ComputedBy`, `Agent026` uses a recursively defined parameter type `NetParams`
  together with its `eval`.  These two recursions match layer for layer, so
  `relun` is provable by induction on the number of hidden layers (no padding
  identity is needed).
* `CPWL n` is the honest finite polyhedral subdivision condition, *not*
  neighbourhood agreement.  The only difference is that `Ref` quantifies over
  affine functionals via `IsAffine`, while `Agent026` carries the coefficient
  data `(A i, c i)` directly; `choose` converts one into the other.
* `depthBound` is literally the same expression, so `depth` is `rfl`.
-/

/-- The two spellings of "finite intersection of closed halfspaces" agree. -/
private lemma poly_iff {n : ℕ} (S : Set (Fin n → ℝ)) :
    Agent026.IsPolyhedron S ↔ Ref.IsPolyhedron n S := by
  constructor
  · rintro ⟨m, a, b, rfl⟩
    exact ⟨m, fun i => {x : Fin n → ℝ | (∑ j, a i j * x j) ≤ b i},
      fun i => ⟨a i, b i, rfl⟩, rfl⟩
  · rintro ⟨m, H, hH, rfl⟩
    choose a b hab using hH
    refine ⟨m, a, b, ?_⟩
    have hH : H = fun i => {x : Fin n → ℝ | (∑ j, a i j * x j) ≤ b i} := funext hab
    rw [hH]

/-- `Ref.Aff.eval` and `Agent026.applyAffine` are the same map, spelled with
`Matrix.mulVec` on one side and an explicit `Finset.sum` on the other. -/
private lemma aff_eval_eq {a b : ℕ} (T : Ref.Aff a b) (x : Fin a → ℝ) :
    T.eval x = Agent026.applyAffine (T.M, T.c) x := rfl

/-- The core bridge: `Ref.ComputedBy n k f` (an inductive predicate) and
"`f` is the evaluation of some `NetParams n 1 k`" define the same class of
functions, for every fixed number `k` of hidden layers. -/
private lemma computedBy_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Ref.ComputedBy n k f ↔
      ∃ P : Agent026.NetParams n 1 k, f = fun x => Agent026.NetParams.eval k P x 0 := by
  intro k
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨T, hT⟩
      exact ⟨(T.M, T.c), funext fun x => hT x⟩
    · rintro ⟨⟨M, c⟩, rfl⟩
      exact ⟨⟨M, c⟩, fun x => rfl⟩
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, T, g, hg, hf⟩
      obtain ⟨P, rfl⟩ := (ih m g).1 hg
      exact ⟨⟨m, (T.M, T.c), P⟩, funext fun x => hf x⟩
    · rintro ⟨⟨h, ⟨M, c⟩, rest⟩, rfl⟩
      exact ⟨h, ⟨M, c⟩, fun y => Agent026.NetParams.eval k rest y 0,
        (ih h _).2 ⟨rest, rfl⟩, fun x => rfl⟩

/-- The two `CPWL` definitions agree: both are "continuous, plus a finite
polyhedral cover on each piece of which `f` is affine". -/
theorem cpwl (n : ℕ) : Agent026.CPWL n = Ref.CPWL n := by
  ext f
  simp only [Agent026.CPWL, Ref.CPWL, Ref.IsCPWL, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hc, m, S, A, c, hpoly, hcov, hagree⟩
    exact ⟨hc, m, S, fun i x => (∑ j, A i j * x j) + c i,
      fun i => (poly_iff (S i)).1 (hpoly i), fun i => ⟨A i, c i, fun _ => rfl⟩, hcov, hagree⟩
  · rintro ⟨hc, m, P, g, hpoly, haff, hcov, hagree⟩
    choose A c hAc using haff
    refine ⟨hc, m, P, A, c, fun i => (poly_iff (P i)).2 (hpoly i), hcov, ?_⟩
    intro i x hx
    rw [hagree i x hx, hAc i x]

/-- The two `ReLUn` definitions agree: both read "at most `k` hidden layers",
and `computedBy_iff` identifies the layer-by-layer recursions. -/
theorem relun (n k : ℕ) : Agent026.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent026.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, hP⟩
    exact ⟨j, hj, (computedBy_iff j n f).2 hP⟩
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (computedBy_iff j n f).1 hf⟩

/-- Both files write the depth bound as `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent026.depthBound n = Ref.depthBound n := rfl

/-- Pointwise version of `statement`. -/
private lemma statement_iff (n : ℕ) (hn : 3 ≤ n) :
    (Agent026.CPWL n = Agent026.ReLUn n (Agent026.depthBound n)) ↔
      (Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
  rw [cpwl n, depth n hn, relun n (Ref.depthBound n)]

theorem statement :
    (∀ n, 3 ≤ n → Agent026.CPWL n = Agent026.ReLUn n (Agent026.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) :=
  ⟨fun h n hn => (statement_iff n hn).1 (h n hn),
   fun h n hn => (statement_iff n hn).2 (h n hn)⟩

end Star_026

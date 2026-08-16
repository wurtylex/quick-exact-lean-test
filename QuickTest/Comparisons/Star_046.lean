import QuickTest.Formalizations.Thm2_046
import QuickTest.Reference

namespace Star_046

/-!
# Comparison of `Agent046` with the reference formalization

`Agent046` makes the same modelling choices as `Ref` on every axis:

* `NetComputes` is the alternating-composition recursion on the number of hidden
  layers, and `ReLUn n k` is **at most** `k` hidden layers — exactly as in `Ref`.
  The only difference is bookkeeping: `Agent046` states the layer equation as a
  function equality `f = fun x => …` where `Ref` states it pointwise, and it
  spells out the affine map as `∑ j, A i j * x j + bias i` where `Ref` writes
  `M.mulVec x + c`.
* `CPWL n` is the honest polyhedral-cover definition, not neighbourhood
  agreement and not a ReLU-representability definition.  The only difference is
  that `Agent046.IsPolyhedron` inlines the halfspaces into the intersection
  where `Ref.IsPolyhedron` quantifies over a family of `IsHalfspace` sets.
* `depthBound` is literally the same expression.

So all four obligations are true, and all four are proved below.
-/

/-- The two spellings of an affine map agree: `M.mulVec x + c` is
`fun i => ∑ j, M i j * x j + c i`. -/
private lemma eval_eq_apply {a b : ℕ} (T : Agent046.AffineMap a b) (x : Fin a → ℝ) :
    Ref.Aff.eval ⟨T.A, T.bias⟩ x = T.apply x := by
  funext i
  first
    | simp [Ref.Aff.eval, Agent046.AffineMap.apply, Matrix.mulVec, Matrix.dotProduct]
    | simp [Ref.Aff.eval, Agent046.AffineMap.apply, Matrix.mulVec, dotProduct]
    | simp [Ref.Aff.eval, Agent046.AffineMap.apply, Matrix.mulVec_eq_sum]

private lemma apply_eq_eval {a b : ℕ} (T : Ref.Aff a b) (x : Fin a → ℝ) :
    (Agent046.AffineMap.mk T.M T.c).apply x = T.eval x :=
  (eval_eq_apply (Agent046.AffineMap.mk T.M T.c) x).symm

/-- Both files apply `max 0 ·` componentwise, so the two `reluVec`s are the same
function. -/
private lemma reluVec_eq {m : ℕ} (v : Fin m → ℝ) :
    Ref.reluVec v = Agent046.reluVec v := rfl

/-- The two network-computation predicates agree.  Induction on the number of
hidden layers; each step is just the translation between the two affine-map
encodings together with `funext`. -/
private lemma net_iff (n k : ℕ) (f : (Fin n → ℝ) → ℝ) :
    Agent046.NetComputes n k f ↔ Ref.ComputedBy n k f := by
  induction k generalizing n f with
  | zero =>
      constructor
      · rintro ⟨T, rfl⟩
        exact ⟨⟨T.A, T.bias⟩, fun x => by rw [eval_eq_apply]⟩
      · rintro ⟨T, hT⟩
        refine ⟨⟨T.M, T.c⟩, funext fun x => ?_⟩
        rw [hT, ← apply_eq_eval]
  | succ k ih =>
      constructor
      · rintro ⟨m, T, g, hg, rfl⟩
        exact ⟨m, ⟨T.A, T.bias⟩, g, (ih m g).mp hg,
          fun x => by rw [eval_eq_apply, reluVec_eq]⟩
      · rintro ⟨m, T, g, hg, hf⟩
        refine ⟨m, ⟨T.M, T.c⟩, g, (ih m g).mpr hg, funext fun x => ?_⟩
        rw [hf, ← apply_eq_eval, ← reluVec_eq]

/-- The two notions of polyhedron agree: naming the halfspaces is the only
difference.  The backward direction needs `choose` to extract the normal vector
and offset of each halfspace. -/
private lemma polyhedron_iff (n : ℕ) (S : Set (Fin n → ℝ)) :
    Agent046.IsPolyhedron n S ↔ Ref.IsPolyhedron n S := by
  constructor
  · rintro ⟨m, a, b, rfl⟩
    exact ⟨m, fun i => {x : Fin n → ℝ | (∑ j, a i j * x j) ≤ b i},
      fun i => ⟨a i, b i, rfl⟩, rfl⟩
  · rintro ⟨m, H, hH, hS⟩
    choose a b hab using hH
    exact ⟨m, a, b, hS.trans (by simp only [hab])⟩

/-- The two affinity predicates are the same statement (`Ref` merely leaves `n`
implicit). -/
private lemma affine_iff (n : ℕ) (g : (Fin n → ℝ) → ℝ) :
    Agent046.IsAffineFun n g ↔ Ref.IsAffine g := Iff.rfl

/-- `Agent046.CPWL` is the reference `CPWL`: both are "continuous, plus a finite
polyhedral cover of `ℝⁿ` with an affine function on each piece".  Only the order
of the existentials and the packaging of the halfspaces differ. -/
theorem cpwl (n : ℕ) : Agent046.CPWL n = Ref.CPWL n := by
  ext f
  constructor
  · rintro ⟨hc, m, g, P, hg, hP, hcov, hagree⟩
    exact ⟨hc, m, P, g, fun i => (polyhedron_iff n (P i)).mp (hP i),
      fun i => (affine_iff n (g i)).mp (hg i), hcov, hagree⟩
  · rintro ⟨hc, m, P, g, hP, hg, hcov, hagree⟩
    exact ⟨hc, m, g, P, fun i => (affine_iff n (g i)).mpr (hg i),
      fun i => (polyhedron_iff n (P i)).mpr (hP i), hcov, hagree⟩

/-- Both files read `ReLU_{n,k}` as *at most* `k` hidden layers, so no padding
argument is needed here — the sets are equal via `net_iff`. -/
theorem relun (n k : ℕ) : Agent046.ReLUn n k = Ref.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, (net_iff n j f).mp h⟩
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, (net_iff n j f).mpr h⟩

/-- Both depth bounds are the literal expression `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`,
so this is definitional; `hn` is not needed. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent046.depthBound n = Ref.depthBound n := rfl

theorem statement :
    (∀ n, 3 ≤ n → Agent046.CPWL n = Agent046.ReLUn n (Agent046.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
  constructor
  · intro h n hn
    have hthis := h n hn
    rw [cpwl n, relun n (Agent046.depthBound n), depth n hn] at hthis
    exact hthis
  · intro h n hn
    have hthis := h n hn
    rw [← depth n hn, ← relun n (Agent046.depthBound n), ← cpwl n] at hthis
    exact hthis

end Star_046

import QuickTest.Formalizations.Thm2_050
import QuickTest.Reference

/-!
# Star comparison: `Agent050` vs `Ref`

`Agent050` is in the "polyhedral subdivision" family, and it matches the
reference on every count:

* `CPWL` is the honest condition — continuous, plus a finite polyhedral cover on
  each piece of which `f` agrees with an affine functional.  The only difference
  is the packaging of a polyhedron: `Ref` intersects a family of halfspaces,
  `Agent050` writes the intersection out as a single `∀ i` in the set-builder.
  Bridging that needs `choose` (to extract the coefficients of each halfspace)
  but nothing more.
* `ReLUn` is **at most** `k` hidden layers on both sides — so the hard padding
  identity `x = relu x - relu (-x)` is *not* needed here.  `Agent050` carries the
  network as an inductive `ReLUNet` datum and `Ref` as the recursive predicate
  `ComputedBy`; the two recursions are step-for-step the same, so the sets agree
  by induction on the depth (`computed_iff` below).
* `depthBound` is literally the same expression, so `depth` is `rfl`.

Consequently all four obligations are proved, with no `sorry`.
-/

namespace Star_050

/-! ### Affine maps and componentwise ReLU -/

/-- The two packagings of an affine map evaluate to the same function:
`Agent050` sums by hand, `Ref` uses `Matrix.mulVec` plus `Pi` addition. -/
private lemma aff_eval_eq {a b : ℕ} (T : Agent050.AffMap a b) :
    T.eval = (Ref.Aff.mk T.A T.c).eval := by
  funext x i
  simp [Agent050.AffMap.eval, Ref.Aff.eval, Matrix.mulVec, dotProduct]

/-- The same equality, read from the reference side. -/
private lemma aff_eval_eq' {a b : ℕ} (T : Ref.Aff a b) :
    (Agent050.AffMap.mk T.M T.c).eval = T.eval :=
  aff_eval_eq ⟨T.M, T.c⟩

/-- The two componentwise ReLUs are the same function. -/
private lemma reluVec_eq {m : ℕ} : (Agent050.reluVec (m := m)) = (Ref.reluVec (n := m)) := by
  funext v i
  simp [Agent050.reluVec, Ref.reluVec, Agent050.relu, Ref.relu]

/-! ### Networks -/

/-- The inductive network datum and the recursive predicate denote the same
class of functions, at every fixed depth. -/
private lemma computed_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    (∃ net : Agent050.ReLUNet n k, f = net.eval) ↔ Ref.ComputedBy n k f := by
  intro k
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨net, hf⟩
      cases net with
      | last T =>
        refine ⟨⟨T.A, T.c⟩, fun x => ?_⟩
        rw [hf]
        simp only [Agent050.ReLUNet.eval]
        rw [aff_eval_eq T]
    · rintro ⟨T, hT⟩
      refine ⟨Agent050.ReLUNet.last ⟨T.M, T.c⟩, funext fun x => ?_⟩
      rw [hT x]
      simp only [Agent050.ReLUNet.eval]
      rw [aff_eval_eq' T]
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨net, hf⟩
      cases net with
      | cons T rest =>
        refine ⟨_, ⟨T.A, T.c⟩, rest.eval, (ih _ rest.eval).1 ⟨rest, rfl⟩, fun x => ?_⟩
        rw [hf]
        simp only [Agent050.ReLUNet.eval]
        rw [aff_eval_eq T, reluVec_eq]
    · rintro ⟨m, T, g, hg, hf⟩
      obtain ⟨net, hnet⟩ := (ih m g).2 hg
      refine ⟨Agent050.ReLUNet.cons ⟨T.M, T.c⟩ net, funext fun x => ?_⟩
      rw [hf x, hnet]
      simp only [Agent050.ReLUNet.eval]
      rw [aff_eval_eq' T, reluVec_eq]

theorem relun (n k : ℕ) : Agent050.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent050.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, net, hf⟩
    exact ⟨j, hj, (computed_iff j n f).1 ⟨net, hf⟩⟩
  · rintro ⟨j, hj, hf⟩
    obtain ⟨net, hnet⟩ := (computed_iff j n f).2 hf
    exact ⟨j, hj, net, hnet⟩

/-! ### CPWL -/

/-- A finite intersection of halfspaces is the same thing as a set cut out by
finitely many linear inequalities. -/
private lemma poly_iff {n : ℕ} (P : Set (Fin n → ℝ)) :
    Agent050.IsPolyhedron P ↔ Ref.IsPolyhedron n P := by
  constructor
  · rintro ⟨m, A, b, hP⟩
    refine ⟨m, fun i => {x | (∑ j, A i j * x j) ≤ b i}, fun i => ⟨A i, b i, rfl⟩, ?_⟩
    rw [hP]
    ext x
    simp [Set.mem_iInter]
  · rintro ⟨m, H, hH, hP⟩
    choose a b hab using hH
    refine ⟨m, a, b, ?_⟩
    rw [hP]
    ext x
    simp [hab, Set.mem_iInter]

private lemma affine_iff {n : ℕ} (g : (Fin n → ℝ) → ℝ) :
    Agent050.IsAffineFun g ↔ Ref.IsAffine g := Iff.rfl

theorem cpwl (n : ℕ) : Agent050.CPWL n = Ref.CPWL n := by
  ext f
  simp only [Agent050.CPWL, Ref.CPWL, Ref.IsCPWL, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hc, m, P, g, hP, hg, hcov, hf⟩
    exact ⟨hc, m, P, g, fun i => (poly_iff (P i)).1 (hP i),
      fun i => (affine_iff (g i)).1 (hg i), hcov, hf⟩
  · rintro ⟨hc, m, P, g, hP, hg, hcov, hf⟩
    exact ⟨hc, m, P, g, fun i => (poly_iff (P i)).2 (hP i),
      fun i => (affine_iff (g i)).2 (hg i), hcov, hf⟩

/-! ### Depth bound and the statement -/

/-- Both files write `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`, so this is `rfl`. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent050.depthBound n = Ref.depthBound n := rfl

theorem statement :
    (∀ n, 3 ≤ n → Agent050.CPWL n = Agent050.ReLUn n (Agent050.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
  constructor
  · intro h n hn
    rw [← cpwl n, ← relun n (Ref.depthBound n), ← depth n hn]
    exact h n hn
  · intro h n hn
    rw [cpwl n, relun n (Agent050.depthBound n), depth n hn]
    exact h n hn

end Star_050

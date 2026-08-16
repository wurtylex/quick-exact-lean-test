import QuickTest.Formalizations.Thm2_030
import QuickTest.Reference

/-!
# Star comparison: `Agent030` vs `Ref`

Agent 030 belongs to the *polyhedral subdivision* family: its `CPWL` is the
honest geometric definition (continuous + a finite polyhedral cover of `ℝⁿ` on
each piece of which `f` agrees with an affine functional), exactly as in
`Ref.IsCPWL`.  Modulo binder names and the fact that `Ref.IsAffine` takes `n`
implicitly while `Agent030.IsAffineFn` takes it explicitly, the two predicates
unfold to *literally the same* proposition, so `cpwl` is a `rfl`-level fact and
needs no auxiliary lemma at all.

`ReLUn` is "at most `k`" on **both** sides, so the hard padding identity
`x = relu x - relu (-x)` is *not* needed here; the only real content is that
`Agent030.ComputesWithHiddenLayers` uses two separate existentials for the
matrix and the bias where `Ref.ComputedBy` bundles them into the structure
`Ref.Aff`.  That is a one-line repackaging, handled by `computedBy_iff` below.

`depthBound` is syntactically identical on both sides (`⌈·⌉₊` *is* `Nat.ceil`),
so `hn` is not even needed.

Verdict: everything is provable; nothing is refuted; no `sorry`.
-/

namespace Star_030

/-! ### CPWL -/

/-- The two `CPWL` definitions unfold to the same proposition: `Continuous f`
together with a finite family of polyhedra covering `ℝⁿ` and affine functionals
agreeing with `f` on each.  `Ref` bundles this through the auxiliary predicate
`Ref.IsCPWL`, but that is a plain `def`, so the two sets are definitionally
equal.

No auxiliary lemma is required: the halfspace, polyhedron and affine-functional
predicates match on the nose (`∑ i, a i * x i ≤ b`, a finite `⋂` of halfspaces,
and `∑ i, a i * x i + c` respectively). -/
theorem cpwl (n : ℕ) : Agent030.CPWL n = Ref.CPWL n :=
  Set.ext fun _ => Iff.rfl

/-! ### ReLUn -/

/-- The only mismatch between the two network predicates is bookkeeping: agent
030 quantifies over a matrix `A` and a bias `c` separately, while the reference
quantifies over a single `Ref.Aff n m` record whose fields are exactly `A` and
`c`.  Since `Ref.Aff.eval ⟨A, c⟩ x = A.mulVec x + c = Agent030.affineMap A c x`
definitionally, each direction is just (un)packing the structure; the recursive
step then goes through by the induction hypothesis at the hidden width `m`.

Note this is an *induction on the layer count*, generalised over `n` and `f`,
because the successor case changes the ambient dimension. -/
private lemma computedBy_iff :
    ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
      Agent030.ComputesWithHiddenLayers n k f ↔ Ref.ComputedBy n k f := by
  intro k
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨A, c, h⟩
      exact ⟨⟨A, c⟩, h⟩
    · rintro ⟨T, h⟩
      exact ⟨T.M, T.c, h⟩
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, A, c, g, hg, h⟩
      exact ⟨m, ⟨A, c⟩, g, (ih m g).mp hg, h⟩
    · rintro ⟨m, T, g, hg, h⟩
      exact ⟨m, T.M, T.c, g, (ih m g).mpr hg, h⟩

/-- Both files read `ReLU_{n,k}` as *at most* `k` hidden layers
(`∃ j ≤ k, …`), so no padding argument is needed and the equality follows
pointwise from `computedBy_iff`. -/
theorem relun (n k : ℕ) : Agent030.ReLUn n k = Ref.ReLUn n k := by
  ext f
  exact exists_congr fun j => and_congr_right fun _ => computedBy_iff j n f

/-! ### depthBound -/

/-- Agent 030 writes `Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1`; the reference
writes `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`.  `⌈·⌉₊` is notation for `Nat.ceil`,
so these are the same term and the hypothesis `hn` is unused.  (In particular
the `Real.natCeil_logb_natCast` bridge is not needed for this file.) -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent030.depthBound n = Ref.depthBound n :=
  rfl

/-! ### The statement of Theorem 2 -/

/-- Pointwise transport of the theorem-2 equation across the three component
identifications above.  This does **not** invoke `Agent030.theorem2` or
`Ref.theorem2` (both of which are `sorry`-ed); it only rewrites with `cpwl`,
`depth` and `relun`. -/
private lemma thm2_iff (n : ℕ) (hn : 3 ≤ n) :
    (Agent030.CPWL n = Agent030.ReLUn n (Agent030.depthBound n)) ↔
      (Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
  rw [cpwl n, depth n hn, relun n (Ref.depthBound n)]

theorem statement :
    (∀ n, 3 ≤ n → Agent030.CPWL n = Agent030.ReLUn n (Agent030.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
  constructor
  · intro h n hn
    exact (thm2_iff n hn).mp (h n hn)
  · intro h n hn
    exact (thm2_iff n hn).mpr (h n hn)

end Star_030

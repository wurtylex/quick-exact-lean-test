namespace Bridge_094_095

/- ## Comparing Agent094 and Agent095

Both files define `relu`, `reluVec`, a matrix-based affine transformation, a hidden-
layer count `ReLUn` ("at most k" via `∃ k' ≤ k, …`), a `CPWL` set, and `depthBound`.
The two `depthBound`s differ only in whether `n - 1` is computed in `ℝ` or in `ℕ`
before casting; for `n ≥ 3` these agree. The `ReLUn` families are built by the same
recursive "peel off the first affine+ReLU layer, keep scalar output throughout"
pattern, just packaged differently (094: direct recursion on scalar-valued `f`;
095: an auxiliary vector-valued inductive `HiddenLayers`, wrapped to force output
dimension 1). They are almost certainly equal but the isomorphism goes through
1×n-matrix/vector conversions (`Matrix.mulVec`, `dotProduct`) that are unsafe to
write without compiler feedback, so `relun` is left `sorry`. The two `CPWL`
definitions differ more substantively (local neighbourhood agreement with a finite
*shared* affine family vs. an explicit finite closed-convex polyhedral cover); both
should describe the true class of PWL functions but the equivalence is a genuine
convex-geometry argument, so `cpwl` is left `sorry` too, and `statement` (which would
be proved by rewriting via `cpwl`/`relun`/`depth`) is left `sorry` as a consequence. -/

/-- `depthBound` differs only in whether `n - 1` is truncated-ℕ-subtracted then cast,
or cast then subtracted in `ℝ`; for `n ≥ 1` (in particular `n ≥ 3`) these coincide. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) :
    Agent094.depthBound n = Agent095.depthBound n := by
  have h1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have h1n : (1 : ℕ) ≤ n := by omega
    rw [Nat.cast_sub h1n, Nat.cast_one]
  simp only [Agent094.depthBound, Agent095.depthBound, h1]

/- `ReLUn n k` is `{f | ∃ k' ≤ k, ComputedWithHiddenLayers n k' f}` in 094 and the
analogous statement with `ComputedByReLUNetwork` in 095. Both underlying predicates
recurse identically: base case is a single affine map into dimension 1 (094 via a
weight-vector-and-bias `IsAffine`, 095 via a `1×n` `Matrix`-and-bias `Affine`
structure whose output type `Fin 1 → ℝ` is forced by the `ComputedByReLUNetwork`
wrapper, which then propagates down through every `step` since the output dimension
`p` in 095's `step` constructor is shared between the outer network and the inner
one); step case peels off one affine map into an arbitrary intermediate width `m`
followed by `reluVec`. So the two predicates are provably in bijection by induction
on `k`, but the base case requires converting between a weight vector `a : Fin n → ℝ`
and a `1×n` matrix `A` via `Matrix.mulVec`/`Matrix.dotProduct` lemmas whose exact
names/simp-normal forms cannot be checked without compiling; getting this wrong would
produce a broken, not merely incomplete, proof, so it is left honestly `sorry`. -/
theorem relun (n k : ℕ) : Agent094.ReLUn n k = Agent095.ReLUn n k := by
  sorry

/- 094's `CPWL n` requires: `f` continuous, and a single finite family of affine
functions `g 0, …, g (m-1)` such that every point `x` has a neighbourhood on which
`f` agrees with *some* `g i` (no requirement that the agreement regions be convex or
closed, only that the same finite list of affine candidates works everywhere).
095's `CPWL n` instead requires an explicit finite cover of `ℝ^n` by *closed convex*
sets `S j` on which `f` is affine (with possibly-repeated affine data across
different `j`, so reusing one affine formula on several disjoint convex cells, e.g. a
1-D "zigzag" reusing slope `+1` on many separate intervals, is allowed on both
sides). Mathematically both descriptions pick out exactly the classical CPWL
functions: the closed-convex-cover description directly gives the local-agreement
description, and conversely a continuous, finite-locally-affine-family function can
be re-cut into finitely many closed convex cells (e.g. via the common refinement by
the sign patterns of pairwise differences `g i - g j` of the finite affine family).
That converse direction is a genuine convex-geometry construction, not a
Mathlib-library lookup, and is out of scope for a short bridge proof, so `cpwl` is
left honestly `sorry` rather than faked. -/
theorem cpwl (n : ℕ) : Agent094.CPWL n = Agent095.CPWL n := by
  sorry

/- This iff would be proved by rewriting each side with `cpwl` (for the `CPWL n`
occurrences) and with `relun` together with `depth` (for the `ReLUn n (depthBound n)`
occurrences), turning the two statements into syntactically identical propositions.
Since `cpwl` and `relun` above are honest `sorry`s, there is no route to `statement`
that does not either launder those gaps or invoke one of the agents' own sorry'd
`theorem2`, so it is left `sorry` as well. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent094.CPWL n = Agent094.ReLUn n (Agent094.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent095.CPWL n = Agent095.ReLUn n (Agent095.depthBound n)) := by
  sorry

end Bridge_094_095

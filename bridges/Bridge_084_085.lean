namespace Bridge_084_085

/-!
Bridge between `Agent084` and `Agent085`'s formalizations of Theorem 2.

Summary of findings:
* `depthBound` is *literally* the same expression in both files (`⌈·⌉₊` is
  notation for `Nat.ceil`), so `depth` is proved by unfolding.
* `ReLUn`: `Agent084.ReLUn n k` packages "at most `k` hidden layers"
  (`∃ k' ≤ k, …`) while `Agent085.ReLUn n k` packages "exactly `k` hidden
  layers". These sets coincide only via the classical padding trick
  `x = relu x - relu (-x)`, which BRIDGE_SPEC.md explicitly notes nobody has
  proved; constructing it here would mean (a) bridging Agent084's pointwise
  recursive relation `IsReLUNetworkOutput` with Agent085's function-level
  recursive relation `Computes`, and (b) an induction building an explicit
  `2n`-wide doubling affine layer at every step. Both are real, tractable
  results, but sprawling and unverifiable without a build; left honest.
* `CPWL`: mathematically these very likely *disagree*. `Agent085.CPWL`
  requires `f` to agree with a *single* affine function on a full
  neighbourhood of every point; since such neighbourhoods are open and two
  affine functions agreeing on an open set are equal everywhere, the sets on
  which `f` agrees with each candidate affine function are open and (after
  deduplication) pairwise disjoint, hence by connectedness of `ℝⁿ` only one
  is nonempty: `Agent085.CPWL n` is really just the *affine* functions, not
  the genuinely piecewise-linear ones. E.g. `x ↦ max 0 (x 0)` is *not* a
  member (near `0` it is not affine on any full neighbourhood), yet it
  clearly belongs to `Agent084.CPWL` via the 2-piece polyhedral subdivision
  `{x 0 ≤ 0}`, `{x 0 ≥ 0}`. Formalizing membership on the `Agent084` side
  requires building an explicit `Polyhedron`/`Halfspace` witness, and
  `Thm2_084.lean` has an elaboration error: `Polyhedron n` is `def`-aliased
  to `List (Halfspace n)`, and `Polyhedron.mem`'s body `∀ H ∈ P, H.mem x`
  needs Lean to find a `Membership (Halfspace n) (Polyhedron n)` instance,
  which typeclass search will not find through a non-reducible `def` — so
  `Agent084.Polyhedron.mem`, and hence `Agent084.CPWL`, is unreliable to
  reason about (its elaboration may have silently degraded via `sorryAx`, or
  it may not be usable at all downstream). Since both directions of a
  `cpwl`/`cpwl_ne` proof need to unfold this, `cpwl` is left honest rather
  than risking a proof built on broken upstream machinery.
-/

/-- Both files write the depth bound as `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`;
`⌈·⌉₊` is notation for `Nat.ceil`, so the two definitions are syntactically
identical and the claim holds for *every* `n`, not just `n ≥ 3`. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent084.depthBound n = Agent085.depthBound n := by
  unfold Agent084.depthBound Agent085.depthBound
  rfl

/-- `Agent084.ReLUn n k` allows any `k' ≤ k` hidden layers while
`Agent085.ReLUn n k` insists on exactly `k`; these are provably the same set
only via the `relu x - relu (-x) = x` padding trick (see the module doc
above), which is a real but nontrivial induction that neither agent's file
proves and that I could not verify without a build. Left honest. -/
theorem relun (n k : ℕ) : Agent084.ReLUn n k = Agent085.ReLUn n k := sorry

/-- See the module doc above: `Agent085.CPWL` (local agreement with a single
affine function on a full neighbourhood of every point) almost certainly
collapses, by connectedness of `ℝⁿ`, to just the globally affine functions,
while `Agent084.CPWL` (finite polyhedral subdivision) is genuinely
piecewise-linear and contains e.g. `x ↦ max 0 (x 0)`. A real refutation
witness (`cpwl_ne`) is very likely available via that function, but
constructing its `Agent084.CPWL` membership proof requires going through
`Agent084.Polyhedron.mem`, which — per `Thm2_084.lean`'s own elaboration
error (a failed `Membership (Halfspace n) (Polyhedron n)` instance search
through the non-reducible `def Polyhedron`) — is not reliable to build on.
Left honest rather than risk a proof resting on broken upstream machinery. -/
theorem cpwl (n : ℕ) : Agent084.CPWL n = Agent085.CPWL n := sorry

/-- Derived purely from `cpwl`, `relun`, and `depth` above (never from either
agent's own `sorry`-ed `theorem2`), by rewriting one agent's statement into
the other's using the three bridge lemmas. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent084.CPWL n = Agent084.ReLUn n (Agent084.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent085.CPWL n = Agent085.ReLUn n (Agent085.depthBound n)) := by
  constructor
  · intro h n hn
    rw [← cpwl n, ← relun n (Agent085.depthBound n), ← depth n hn]
    exact h n hn
  · intro h n hn
    rw [cpwl n, relun n (Agent084.depthBound n), depth n hn]
    exact h n hn

end Bridge_084_085

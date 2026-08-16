namespace Bridge_041_042

/-!
## Summary of the comparison

* `depthBound`: Agent041 casts `n - 1` (truncated `ℕ` subtraction) to `ℝ` before taking
  `logb`; Agent042 casts `n` to `ℝ` first and subtracts `1` in `ℝ`. For `n ≥ 3` (in fact
  for `n ≥ 1`) these coincide via `Nat.cast_sub`. **PROVED**.
* `CPWL`: both agents use the same *family* of definition (family (a) in the spec):
  Agent041's is "continuous and, at every point, agrees with one of finitely many
  globally-defined affine scalar functions"; Agent042's is "continuous and admits a
  finite polyhedral subdivision of `ℝⁿ` on each piece of which `f` is affine". The
  direction "polyhedral ⇒ pointwise-affine-selection" (Agent042 ⊆ Agent041) is a direct
  translation (take the affine formula on each polyhedral piece as one of the finitely
  many global candidates) and is proved below. The converse direction
  (Agent041 ⊆ Agent042) is mathematically true but genuinely hard: from finitely many
  global affine candidates `g_1, …, g_m` one has to build the hyperplane arrangement cut
  out by the pairwise differences `g_i - g_j`, argue that on each open cell the closed
  sets `{x : f x = g_j x}` are pairwise disjoint (since the `g_j` are pairwise distinct
  throughout an open cell) and cover the (connected) cell, hence `f` equals a *single*
  `g_j` on the whole open cell by a connectedness argument, and then extend to the closed
  cell (a polyhedron) by continuity. This is essentially the hard direction of the
  CPWL-characterization underlying Theorem 2 itself (both `Thm2_041.lean` and
  `Thm2_042.lean` leave the actual theorem as `sorry`), so it is left as an honest
  `sorry` here rather than faked. **SORRY** (one direction proved, one direction open).
* `ReLUn`: Agent041's is "**at most** `k` hidden layers" (`∃ k' ≤ k`, via the recursive
  predicate `NetFunc`, which is built by peeling the *last* affine layer off first).
  Agent042's is "**exactly** `k` hidden layers" (a `List AffineLayer` of length `k + 1`,
  consumed by `runLayers` from the *first* layer). Proving these sets equal for all `n k`
  needs two genuinely hard ingredients that neither source file supplies: (1) a
  translation between the two network encodings — an induction along *opposite ends* of
  the same list of layers (`NetFunc`'s recursion unfolds from the output side, `runLayers`
  from the input side), and (2) the identity-emulation padding lemma
  (`x = ReLU x - ReLU (-x)`, doubling the width) needed to promote a `k'`-hidden-layer
  network with `k' < k` into an "exactly `k`" one. Both are real, unproven results (flagged
  as such in `BRIDGE_SPEC.md`), not routine translations, so this is left as an honest
  `sorry`. **SORRY**.
* `statement`: this biconditional's truth depends on the two open questions above (the
  hard direction of `cpwl` and the full `relun` equivalence). Neither `Thm2_041.lean` nor
  `Thm2_042.lean` proves its own Theorem 2 (both are `sorry`), so there is no way to derive
  `statement` honestly from those admitted proofs — doing so would only launder a `sorry`
  through extra indirection, not establish anything. Resolving `statement` for real requires
  resolving `cpwl`'s hard direction and `relun` first. **SORRY**.
-/

/-! ### `depthBound` -/

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent041.depthBound n = Agent042.depthBound n := by
  have h1n : (1 : ℕ) ≤ n := by omega
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub h1n, Nat.cast_one]
  unfold Agent041.depthBound Agent042.depthBound
  rw [hcast]

/-! ### `CPWL` -/

theorem cpwl (n : ℕ) : Agent041.CPWL n = Agent042.CPWL n := by
  ext f
  constructor
  · -- Hard direction: Agent041.CPWL n ⊆ Agent042.CPWL n. A continuous function that
    -- pointwise agrees with one of finitely many *global* affine functions g_1,…,g_m
    -- must in fact be polyhedral: build the hyperplane arrangement cut out by all
    -- pairwise differences g_i - g_j (finitely many affine functions ⇒ finitely many
    -- hyperplanes), argue that on each open cell of the arrangement the sets
    -- {x : f x = g_j x} are pairwise disjoint, closed in the cell, and cover the
    -- (convex, hence connected) cell, so f agrees with a *single* g_j on the whole
    -- open cell, then extend to the closed cell (a polyhedron) by continuity of both
    -- f and g_j. This is a genuine, nontrivial theorem about finite affine selections
    -- (in essence the hard direction of the CPWL-characterization underlying Theorem 2
    -- itself, left `sorry` in both Thm2_041.lean and Thm2_042.lean); formalizing the
    -- arrangement-plus-connectedness argument is out of scope for this bridge.
    intro _
    sorry
  · -- Easy direction: Agent042.CPWL n ⊆ Agent041.CPWL n. Take the affine formula on
    -- each polyhedral piece as one of the finitely many global affine candidates; every
    -- point lies in some piece (the pieces cover `Set.univ`), so f agrees pointwise
    -- with that candidate there.
    rintro ⟨hf, m, P, A, c, hP, hcov, hpiece⟩
    refine ⟨hf, m, fun j x => (∑ k, A j k * x k) + c j, ?_, ?_⟩
    · intro j
      exact ⟨A j, c j, fun x => rfl⟩
    · intro x
      have hx : x ∈ (⋃ i, P i) := by rw [hcov]; exact Set.mem_univ x
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact ⟨i, hpiece i x hi⟩

/-! ### `ReLUn` -/

-- Agent041.ReLUn n k is "≤ k hidden layers" (∃ k' ≤ k, via the recursive predicate
-- `NetFunc`, built by peeling the *last* affine layer off first). Agent042.ReLUn n k is
-- "exactly k hidden layers" (a `List AffineLayer` of length k + 1, consumed by
-- `runLayers` from the *first* layer). Proving these sets equal for all n k needs two
-- genuinely hard ingredients neither source file supplies: (1) a translation between the
-- two network encodings (an induction along opposite ends of the same list of layers),
-- and (2) the identity-emulation padding lemma (x = ReLU x - ReLU (-x)) used to promote a
-- k'-hidden-layer network, k' < k, into an "exactly k" one. Both are real, unproven
-- results (per BRIDGE_SPEC.md), not routine translations, so this is left as an honest
-- `sorry`.
theorem relun (n k : ℕ) : Agent041.ReLUn n k = Agent042.ReLUn n k := by
  sorry

/-! ### `statement` -/

-- Truth of this biconditional hinges on the two open questions above: the hard direction
-- of `cpwl` (Agent041.CPWL ⊆ Agent042.CPWL) and the full `relun` equivalence. Neither
-- Agent041 nor Agent042 proves its own Theorem 2 (both `theorem2` are `sorry` in the
-- source files), so `statement` cannot be derived honestly from those admitted proofs —
-- doing so would only launder a `sorry` through extra indirection (any downstream use of
-- `Agent041.theorem2`/`Agent042.theorem2` would depend on `sorryAx`, from which both a
-- proposition and its negation are "provable"). Resolving `statement` for real requires
-- first resolving `cpwl`'s hard direction and `relun`, i.e. genuinely new mathematics
-- beyond what a single bridge file can responsibly produce.
theorem statement :
    (∀ n, 3 ≤ n → Agent041.CPWL n = Agent041.ReLUn n (Agent041.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent042.CPWL n = Agent042.ReLUn n (Agent042.depthBound n)) := by
  sorry

end Bridge_041_042

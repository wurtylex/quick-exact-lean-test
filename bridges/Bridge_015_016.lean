namespace Bridge_015_016

/-!
## Summary of the comparison

* `depthBound`: identical formulas. Both are `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`, with
  `⌈⌉₊` simply being notation for `Nat.ceil`; the two definitions are syntactically the
  same term once notation is expanded. **PROVED** (by `rfl`).
* `CPWL`: both agents use the "local agreement with some affine function in a
  neighbourhood of every point" reading (family (b) in the spec) — Agent015 phrases the
  neighbourhood via a `dist _ _ < ε` ball and packages the affine function as a bundled
  `AffineMap` (matrix `A` + bias `c`, evaluated at output coordinate `0`); Agent016 phrases
  the neighbourhood via the `nhds` filter and packages the affine function as an unbundled
  `∑ a i * x i + c` witness. These are the same condition once `AffineMap`s are converted
  to/from `(a, c)` pairs (via the matrix's `0`-th row) and `∃ ε > 0, ∀ y, dist y x < ε → …`
  is converted to/from `∀ᶠ y in nhds x, …` via `Metric.eventually_nhds_iff`. **PROVED**.
* `ReLUn`: Agent015's `ReLUn n k` is "computable with *exactly* `k` hidden layers"
  (`Represents`, a directly recursive `Prop`-valued definition on Agent015's own bundled
  `AffineMap`); Agent016's `ReLUn n k` is "computable with *at most* `k` hidden layers"
  (`∃ k' ≤ k, ComputesHidden n k' f`, an *inductive* predicate on Agent016's own
  `AffineT := Matrix × Vec` pair encoding). These two sets are in fact mathematically equal
  for every `n k` — not merely because `k = 0` forces `k' = 0`, but because a network with
  `k' < k` layers can always be *padded* to a network with exactly `k` layers computing the
  same function: insert, right after the input, the affine map `x ↦ (x, -x) : ℝ^n → ℝ^{2n}`,
  apply `ReLU`, then recombine with the affine map `(u, v) ↦ u - v`, using the identity
  `max 0 t - max 0 (-t) = t`. Formalizing this needs (i) a translation lemma between
  Agent015's `Represents`/`AffineMap` and Agent016's `ComputesHidden`/`AffineT` encodings,
  and (ii) the padding lemma itself. Nobody among the 100 original agents proved anything
  like it; it is genuine new mathematics beyond a single link's bridging task and involves a
  nontrivial `Fin (n + n)`-indexed matrix construction that cannot be verified without
  compiling, so it is left **SORRY** (see the comment on `relun` below).
* `statement`: both agents' `theorem2` are themselves `sorry`ed in their own files, so this
  is a purely definitional question relating the two phrasings of Theorem 2 to each other.
  Given `cpwl` and `depth` above, it reduces to `Agent015.ReLUn n (depthBound n) =
  Agent016.ReLUn n (depthBound n)` for `n ≥ 3`, i.e. exactly the `k = depthBound n` special
  case of the missing `relun` padding lemma, so it is also left **SORRY**.
-/

/-! ### `cpwl` -/

/-- Both `CPWL` predicates say: `f` is continuous, and there is a finite family of affine
functions such that `f` agrees with one member of the family on a whole neighbourhood of
every point. We convert Agent015's bundled `AffineMap n 1` (evaluated at coordinate `0`)
to and from Agent016's unbundled `∑ a i * x i + c` witness, and convert between the
`dist _ _ < ε`-ball and `nhds`-filter phrasings of "neighbourhood" via
`Metric.eventually_nhds_iff`. -/
theorem cpwl (n : ℕ) : Agent015.CPWL n = Agent016.CPWL n := by
  ext f
  simp only [Agent015.CPWL, Agent015.IsCPWL, Agent016.CPWL, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hf, m, g, hg⟩
    refine ⟨hf, m, fun i x => (g i).toFun x 0, ?_, ?_⟩
    · intro i
      refine ⟨fun j => (g i).A 0 j, (g i).c 0, fun x => ?_⟩
      simp [Agent015.AffineMap.toFun, Matrix.mulVec, dotProduct]
    · intro x
      obtain ⟨i, ε, hε, hix⟩ := hg x
      refine ⟨i, ?_⟩
      rw [Metric.eventually_nhds_iff]
      exact ⟨ε, hε, fun y hy => hix y hy⟩
  · rintro ⟨hf, m, g, hgaff, hg⟩
    choose a c hac using hgaff
    refine ⟨hf, m, fun i =>
      (⟨Matrix.of fun (_ : Fin 1) j => a i j, fun _ => c i⟩ : Agent015.AffineMap n 1), ?_⟩
    intro x
    obtain ⟨i, hi⟩ := hg x
    rw [Metric.eventually_nhds_iff] at hi
    obtain ⟨ε, hε, hi⟩ := hi
    refine ⟨i, ε, hε, fun y hy => ?_⟩
    rw [hi hy, hac i y]
    simp [Agent015.AffineMap.toFun, Matrix.mulVec, dotProduct, Matrix.of_apply]

/-! ### `relun` -/

-- Agent015.ReLUn n k is "exactly k hidden layers" (the recursive `Represents` predicate,
-- built on Agent015's own bundled `AffineMap`); Agent016.ReLUn n k is "at most k hidden
-- layers" (`∃ k' ≤ k, ComputesHidden n k' f`, an inductive predicate built on Agent016's own
-- `AffineT := Matrix × Vec` pair encoding). These sets are mathematically equal for every
-- `n k` (this is not a case where the formalizations genuinely disagree): the padding
-- argument sketched above — inserting a `x ↦ (x, -x)`-then-ReLU-then-`(u,v) ↦ u-v` block
-- via `max 0 t - max 0 (-t) = t` — turns any `k'`-layer network into a `k`-layer network
-- computing the same function whenever `k' ≤ k`, so "at most k" collapses onto "exactly k".
-- Proving this in Lean needs (1) a translation lemma
-- `Agent015.Represents n k f ↔ Agent016.ComputesHidden n k f` bridging the two independent
-- `AffineMap`/`AffineT` encodings, and (2) the padding lemma itself, built from an explicit
-- `Fin (n + n)`-indexed duplicate-and-negate matrix and its ReLU-recombination inverse. This
-- is genuine, nontrivial new mathematics that none of the 100 original agents proved, and
-- the resulting matrix/index construction cannot be reliably checked without compiling, so
-- it is left as an honest `sorry` rather than risking an unverifiable, possibly-broken term.
theorem relun (n k : ℕ) : Agent015.ReLUn n k = Agent016.ReLUn n k := by
  sorry

/-! ### `depth` -/

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent015.depthBound n = Agent016.depthBound n := rfl

/-! ### `statement` -/

-- Both agents' `theorem2` are themselves `sorry`ed, so this is a purely definitional
-- question. Using `cpwl` and `depth`, `statement` reduces to showing
-- `Agent015.ReLUn n (Agent015.depthBound n) = Agent016.ReLUn n (Agent016.depthBound n)` for
-- every `n ≥ 3`, which is exactly the `k = depthBound n` instance of the `relun` padding
-- lemma left `sorry` above; left `sorry` here for the same reason.
theorem statement :
    (∀ n, 3 ≤ n → Agent015.CPWL n = Agent015.ReLUn n (Agent015.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent016.CPWL n = Agent016.ReLUn n (Agent016.depthBound n)) := by
  sorry

end Bridge_015_016

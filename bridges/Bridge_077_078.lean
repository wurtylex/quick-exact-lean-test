namespace Bridge_077_078

/-!
## Summary of the comparison

* `depthBound`: both agents write the *literal same* expression
  `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1` (`⌈·⌉₊` is notation for `Nat.ceil`), so this is closed
  by `rfl` after unfolding. **PROVED**.
* `CPWL`: both agents use the "local agreement" family (b): continuous, and a finite family
  of genuinely affine functions such that every point has a neighbourhood on which `f`
  agrees with one of them. Agent077 spells the neighbourhood condition with an explicit
  `∃ ε > 0, ∀ y, dist y x < ε → …`; Agent078 spells it with `∀ᶠ y in nhds x, …`. These are
  the same condition (`Metric.ball`-basis of `nhds` in a Pi/metric space), and the
  "genuinely affine" predicates (`IsAffineMap` / `IsAffine`) are literally the same formula
  `∃ w b, ∀ x, g x = (∑ i, w i * x i) + b`. **PROVED**.
* `ReLUn`: both agents define "at most `k` hidden layers", but with genuinely different
  bookkeeping for the underlying networks. Agent077 recurses on `k`, peeling off one
  `Affine n m` map (`m` chosen freely at each layer) via `Fin`-indexed matrices. Agent078
  instead threads *all* layers' values through a single ambient type `ℕ → ℝ`, using a
  `width : ℕ → ℕ` function and matrices `A : ℕ → ℕ → ℕ → ℝ` indexed by (layer, out, in).
  Mathematically these describe the same class of networks (arbitrary per-layer widths,
  `k`-fold ReLU/affine alternation), but proving that requires building explicit
  translations `Agent077.Computes n k f → Agent078.ReLUNetwork.Computes …` and back, by
  induction on `k`, threading dimension bookkeeping (`Fin m` witnesses vs. `width`
  functions and zero-padding outside the active coordinates) through every layer. That is
  a substantial independent construction, not a short bridging fact, so it is left open.
  **SORRY**.
* `statement`: reduces, via `cpwl` and `depth` above, to `Agent077.ReLUn n (depthBound n) =
  Agent078.ReLUn n (depthBound n)` for every `n ≥ 3`, i.e. to the unproved `relun` fact
  above (or at least its instance at `k = depthBound n`). Without it there is no way to
  transport truth of one agent's Theorem 2 statement to the other's. **SORRY**.
-/

/-! ### `depthBound` -/

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent077.depthBound n = Agent078.depthBound n := by
  unfold Agent077.depthBound Agent078.depthBound
  rfl

/-! ### `CPWL` -/

/-- The ball-based and filter-based descriptions of "eventually near `x`" agree, for any
predicate on a metric space (here `Fin n → ℝ` with its Pi/sup metric). -/
private lemma eventuallyIffBall {n : ℕ} {p : (Fin n → ℝ) → Prop} {x : Fin n → ℝ} :
    (∀ᶠ y in nhds x, p y) ↔ ∃ ε > 0, ∀ y, dist y x < ε → p y := by
  rw [Filter.eventually_iff, Metric.mem_nhds_iff]
  constructor
  · rintro ⟨ε, hε, hsub⟩
    exact ⟨ε, hε, fun y hy => hsub (Metric.mem_ball.2 hy)⟩
  · rintro ⟨ε, hε, h⟩
    exact ⟨ε, hε, fun y hy => h y (Metric.mem_ball.1 hy)⟩

theorem cpwl (n : ℕ) : Agent077.CPWL n = Agent078.CPWL n := by
  ext f
  simp only [Agent077.CPWL, Agent078.CPWL, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hf, m, g, hg, hloc⟩
    refine ⟨hf, m, g, fun i => ?_, fun x => ?_⟩
    · obtain ⟨w, b, hw⟩ := hg i
      exact ⟨w, b, hw⟩
    · obtain ⟨i, ε, hε, hy⟩ := hloc x
      exact ⟨i, eventuallyIffBall.2 ⟨ε, hε, hy⟩⟩
  · rintro ⟨hf, m, g, hg, hloc⟩
    refine ⟨hf, m, g, fun i => ?_, fun x => ?_⟩
    · obtain ⟨w, b, hw⟩ := hg i
      exact ⟨w, b, hw⟩
    · obtain ⟨i, hev⟩ := hloc x
      obtain ⟨ε, hε, hy⟩ := eventuallyIffBall.1 hev
      exact ⟨i, ε, hε, hy⟩

/-! ### `ReLUn` -/

-- Both `ReLUn` are "computable by a ReLU network with at most k hidden layers", but the
-- underlying network representations differ in bookkeeping: Agent077's `Computes` recurses
-- on `k` with `Fin`-indexed `Affine n m` matrices (fresh `m` at each layer), while
-- Agent078's `ReLUNetwork` threads every layer's values through the single ambient type
-- `ℕ → ℝ`, governed by a `width : ℕ → ℕ` function and `A : ℕ → ℕ → ℕ → ℝ`. These describe
-- the same mathematical class of networks, but proving the set equality needs an explicit
-- induction-on-`k` translation between the two encodings (matching `Fin m` witnesses with
-- `width` values and zero-padding outside active coordinates) in both directions, which is
-- a substantial construction beyond what a short bridge file can responsibly attempt.
theorem relun (n k : ℕ) : Agent077.ReLUn n k = Agent078.ReLUn n k := by
  sorry

/-! ### `statement` -/

-- This reduces to `relun` (specifically its instance at `k = depthBound n`, for every
-- `n ≥ 3`) together with `cpwl` and `depth` above; since `relun` is left `sorry`, there is
-- no way here to transport truth of one agent's (still-`sorry`ed) Theorem 2 statement to
-- the other's.
theorem statement :
    (∀ n, 3 ≤ n → Agent077.CPWL n = Agent077.ReLUn n (Agent077.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent078.CPWL n = Agent078.ReLUn n (Agent078.depthBound n)) := by
  sorry

end Bridge_077_078

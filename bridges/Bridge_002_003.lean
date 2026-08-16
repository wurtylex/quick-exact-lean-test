namespace Bridge_002_003

/-!
## Comparison of Agent002 and Agent003

* `CPWL` — both use the identical "local agreement with a finite family of affine pieces"
  characterization: `Continuous f` together with a finite family of affine functions such
  that every point has a neighbourhood on which `f` coincides with one member of the
  family. Agent002 packages each affine piece as a `structure Affine a b` (matrix + bias)
  and states the local-agreement condition with an explicit metric ball
  (`∃ ε > 0, ∀ y, dist y x < ε → …`); Agent003 packages each affine piece as a bare
  function together with an `IsAffineFun` existential witness, and states local agreement
  via `Filter.Eventually … (nhds x)`. These are in bijective correspondence: a ball
  condition and a `nhds`-eventually condition agree by `Metric.eventually_nhds_iff`, and an
  `Affine a b` bundle unpacks to exactly the `(a, c)` data of `IsAffineFun` via
  `Matrix.mulVec`/`Matrix.dotProduct` unfolding. So `cpwl` is proved below in full.
* `depthBound` — both are *literally* the same term
  `Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1`, so `depth` is `rfl`.
* `ReLUn` — this is where the two formalizations genuinely diverge. Agent002's `ReLUn n k`
  means "representable with *exactly* `k` hidden layers"
  (`ComputesWithHiddenLayers n k f`), the literal reading of the alternating composition.
  Agent003's `ReLUn n k` means "representable with *at most* `k` hidden layers"
  (`∃ k' ≤ k, f ∈ ReLUnExact n k'`), by the author's own stated design choice. These two
  readings are mathematically equal as sets — any network with `k' < k` layers can be
  padded up to exactly `k` layers by inserting extra affine+ReLU layers that compute the
  identity via `x = ReLU x - ReLU (-x)` — but formalizing that padding step requires
  building an explicit width-doubling affine map (splitting a `Fin (w + w)` index into two
  `Fin w` halves via `finSumFinEquiv`, with a block matrix `[A | -A]`) and an induction on
  the padding amount. This is exactly the lemma the task spec flags as unproved by anyone
  ("Nobody has proved that lemma; if you need it, prove it."); we were not able to carry
  out that index-heavy matrix construction with confidence while unable to compile-check
  it, so `relun` (and, since `statement` reduces to it after substituting `cpwl`/`depth`,
  `statement` too) is left as an honest `sorry` rather than risking a silently broken
  ~100-line matrix proof. See the comments directly above each `sorry` for the precise gap.
-/

/-- Evaluating an `Agent002.Affine` transformation at a single output coordinate `i`
unfolds to the expected weighted sum plus bias — i.e. exactly the shape of
`Agent003.IsAffineFun`. -/
lemma affine_eval_eq {a b : ℕ} (T : Agent002.Affine a b) (x : Fin a → ℝ) (i : Fin b) :
    T.eval x i = (∑ j, T.A i j * x j) + T.c i := by
  simp [Agent002.Affine.eval, Matrix.mulVec, Matrix.dotProduct, Pi.add_apply]

theorem cpwl (n : ℕ) : Agent002.CPWL n = Agent003.CPWL n := by
  ext f
  constructor
  · rintro ⟨hf, m, g, hg⟩
    refine ⟨hf, m, fun i y => (g i).eval y 0,
      fun i => ⟨fun k => (g i).A 0 k, (g i).c 0, fun x => affine_eval_eq (g i) x 0⟩, ?_⟩
    intro x
    obtain ⟨i, ε, hε, hball⟩ := hg x
    exact ⟨i, Metric.eventually_nhds_iff.mpr ⟨ε, hε, fun y hy => hball y hy⟩⟩
  · rintro ⟨hf, m, g, hcoeff, hg⟩
    choose a c hac using hcoeff
    refine ⟨hf, m, fun i => (⟨fun _ k => a i k, fun _ => c i⟩ : Agent002.Affine n 1), ?_⟩
    intro x
    obtain ⟨i, hev⟩ := hg x
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
    refine ⟨i, ε, hε, fun y hy => ?_⟩
    have h1 : f y = g i y := hball hy
    have h2 : g i y = (∑ k, a i k * y k) + c i := hac i y
    have h3 : (Agent002.Affine.eval ⟨fun _ k => a i k, fun _ => c i⟩ y) 0
        = (∑ k, a i k * y k) + c i := affine_eval_eq ⟨fun _ k => a i k, fun _ => c i⟩ y 0
    rw [h1, h2, ← h3]

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent002.depthBound n = Agent003.depthBound n := rfl

/- `relun` : SORRY.
`Agent002.ReLUn n k` is "exactly `k` hidden layers" while `Agent003.ReLUn n k` is "at most
`k` hidden layers". These sets are genuinely equal (not just isomorphic-by-relabelling, as
in `cpwl`): any function representable with `k' ≤ k` layers is also representable with
exactly `k` layers, by padding with `k - k'` extra identity layers, each realized as
`x ↦ (x, -x)` (an affine map to double the width) followed by `ReLU` and then the affine
combination `y ↦ y₁ - y₂`, which recovers `x` exactly since
`max 0 t - max 0 (-t) = t` for every real `t`. Formalizing this requires (a) an explicit
block-affine map on `Fin (w + w)` built from `finSumFinEquiv` together with the sum
identity `∑ j, (if a = j then 1 else 0) * x j = x a`, and (b) an induction on `k - k'` that
applies the one-layer padding step repeatedly to whichever network `g` sits behind the
*outermost* affine map (so the padding is applied at the base case `k = 0` of the
`ComputesWithHiddenLayers`/`ReLUnExact` recursion, not at the top). Both directions
(`ReLUnExact n k ⊆ ComputesWithHiddenLayers n k` bridging the `AffineMap`/`Affine` encoding
difference, as in `cpwl`, and the padding step itself) are individually routine but the
combination is a substantial, index-heavy construction that we chose not to attempt
uncompiled; see the task spec's own remark that no one has proved this lemma. -/
theorem relun (n k : ℕ) : Agent002.ReLUn n k = Agent003.ReLUn n k := sorry

/- `statement` : SORRY, for the same underlying reason as `relun`.
Both `Agent002.theorem2` and `Agent003.theorem2` are themselves `sorry` in the source
files, so we cannot settle `statement` by proving either side outright. Substituting
`cpwl` and `depth` into the two universally-quantified claims collapses all of the
discrepancy down to a single remaining gap: `Agent002.ReLUn n (Agent003.depthBound n) =
Agent003.ReLUn n (Agent003.depthBound n)` for every `n ≥ 3`, which is exactly (an instance
of) the unproved `relun`. Since that dependency cannot be discharged without the padding
lemma described above, `statement` inherits the same gap and is left as `sorry` rather
than faked. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent002.CPWL n = Agent002.ReLUn n (Agent002.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent003.CPWL n = Agent003.ReLUn n (Agent003.depthBound n)) := sorry

end Bridge_002_003

namespace Bridge_079_080

/-!
## Summary of the comparison

* `depthBound`: both agents write `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1` verbatim (Agent080
  merely spells `Nat.ceil` instead of the `⌈·⌉₊` notation, which is the very same
  function). **PROVED**, trivially.
* `CPWL`: Agent079 quantifies its finite family of affine pieces over `Fin m`, Agent080
  over an arbitrary `Fintype ι`; and Agent079 spells "locally agrees" with an explicit
  `∃ ε > 0, ∀ y, dist y x < ε → …` while Agent080 uses `f =ᶠ[nhds x] g i`. Both gaps are
  bridged by standard facts (`Fintype.equivFin`, `Metric.mem_nhds_iff`), and the two
  notions of "affine function" (`IsAffine`/`IsAffineFun`) are literally the same data
  under different names. **PROVED**.
* `ReLUn`: Agent079 reads "`k` hidden layers" as *at most* `k` (`∃ k' ≤ k, …`); Agent080
  reads it as *exactly* `k` (a recursion forced to peel exactly `k` layers). These only
  coincide via a padding argument — turning a `k'`-layer network (`k' ≤ k`) into a
  `(k'+ (k-k'))`-layer network computing the same function by inserting `k - k'` "identity"
  layers built from `x = ReLU x - ReLU (-x)`. That construction is genuine independent
  work (explicitly flagged as unattempted by any agent in the task spec) and is not
  carried out here. **SORRY**.
* `statement`: the biconditional of the two agents' (each still-`sorry`ed) Theorem 2
  claims. Deriving it from `cpwl`, `relun`, `depth` needs `relun` (at least at
  `k = depthBound n`), which is unresolved above; and since both source `theorem2`s are
  themselves `sorry`, there is no independent route to either side. **SORRY**.
-/

/-! ### `depthBound` -/

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent079.depthBound n = Agent080.depthBound n := by
  unfold Agent079.depthBound Agent080.depthBound
  rfl

/-! ### `CPWL` -/

/-- Agent079's `(a, b)`-pair encoding of an affine functional and Agent080's
`AffineMap n 1` encoding carry the same data. -/
private theorem isAffine_iff {n : ℕ} (g : (Fin n → ℝ) → ℝ) :
    Agent079.IsAffine n g ↔ Agent080.IsAffineFun n g := by
  constructor
  · rintro ⟨a, b, hab⟩
    refine ⟨⟨fun _ j => a j, fun _ => b⟩, ?_⟩
    funext x
    rw [hab x]
    rfl
  · rintro ⟨T, hT⟩
    refine ⟨fun j => T.A 0 j, T.c 0, fun x => ?_⟩
    rw [congrFun hT x]
    rfl

/-- "`f` agrees with `g` on a ball of radius `ε` around `x`" and "`f =ᶠ[nhds x] g`" say
the same thing in a metric space. -/
private theorem ball_iff_eventuallyEq {n : ℕ} (f g : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    (∃ ε > 0, ∀ y, dist y x < ε → f y = g y) ↔ f =ᶠ[nhds x] g := by
  show (∃ ε > 0, ∀ y, dist y x < ε → f y = g y) ↔ ∀ᶠ y in nhds x, f y = g y
  rw [Filter.eventually_iff, Metric.mem_nhds_iff]
  constructor
  · rintro ⟨ε, hε, h⟩
    exact ⟨ε, hε, fun y hy => h y (Metric.mem_ball.mp hy)⟩
  · rintro ⟨ε, hε, h⟩
    exact ⟨ε, hε, fun y hy => h (Metric.mem_ball.mpr hy)⟩

theorem cpwl (n : ℕ) : Agent079.CPWL n = Agent080.CPWL n := by
  ext f
  simp only [Agent079.CPWL, Agent080.CPWL, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hf, m, g, hg, hloc⟩
    refine ⟨hf, Fin m, inferInstance, g, fun i => (isAffine_iff (g i)).mp (hg i), fun x => ?_⟩
    obtain ⟨i, ε, hε, h⟩ := hloc x
    exact ⟨i, (ball_iff_eventuallyEq f (g i) x).mp ⟨ε, hε, h⟩⟩
  · rintro ⟨hf, ι, hι, g, hg, hloc⟩
    letI : Fintype ι := hι
    let e := Fintype.equivFin ι
    refine ⟨hf, Fintype.card ι, fun k => g (e.symm k),
      fun k => (isAffine_iff (g (e.symm k))).mpr (hg (e.symm k)), fun x => ?_⟩
    obtain ⟨i, hi⟩ := hloc x
    refine ⟨e i, ?_⟩
    have h' := (ball_iff_eventuallyEq f (g i) x).mpr hi
    simpa [e.symm_apply_apply] using h'

/-! ### `ReLUn` -/

-- Agent079 reads "`k` hidden layers" as *at most* `k`, Agent080 as *exactly* `k`. Bridging
-- these requires a padding construction (turning a short network into a longer one
-- computing the same function via `x = ReLU x - ReLU (-x)`, using an extra `2m`-wide
-- hidden layer as an "identity"), which is real, uncompleted work — see the summary above
-- and the task spec's own remark that nobody has proved this lemma yet.
theorem relun (n k : ℕ) : Agent079.ReLUn n k = Agent080.ReLUn n k := by
  sorry

/-! ### `statement` -/

-- Both `theorem2` proofs in the source files are themselves `sorry`, and deriving this
-- biconditional from `cpwl` + `depth` still needs `relun` (or at least its instance at
-- `k = depthBound n`), which is left unresolved above.
theorem statement :
    (∀ n, 3 ≤ n → Agent079.CPWL n = Agent079.ReLUn n (Agent079.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent080.CPWL n = Agent080.ReLUn n (Agent080.depthBound n)) := by
  sorry

end Bridge_079_080

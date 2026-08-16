namespace Bridge_023_024

/-!
## Comparing `Agent023` and `Agent024`

Both agents made essentially the *same* modelling choices for Theorem 2:

* An affine map `ℝ^a → ℝ^b` is a matrix `A` plus a bias `c`, evaluated as
  `x ↦ A.mulVec x + c` (`Agent023.AffineMap`/`.eval`, `Agent024.Affine`/`.toFun`).
* `ReLUn n k` is "representable with *at most* `k` hidden layers"
  (`∃ k' ≤ k, …`) for both. The underlying "computed by a network with *exactly*
  `k'` hidden layers" predicate is written as a structurally-recursive `def`
  returning `Prop` by Agent023 (`IsReLUNetworkFunc`) and as a genuine inductive
  family by Agent024 (`NetComputes`); these unfold to the same alternating
  composition `T^(k'+1) ∘ ReLU ∘ ⋯ ∘ ReLU ∘ T^(1)`, so they agree by an
  induction on `k'` (`net_iff` below) that just repackages the affine-map data
  between the two structurally-identical bundle types.
* `CPWL n` is: `Continuous f` together with a finite family of affine
  functions such that every point has a neighbourhood on which `f` coincides
  with one member of the family. Agent023 states the neighbourhood condition
  with an explicit open set (`∃ U, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, …`); Agent024
  states it via `Filter.Eventually … (nhds x)`. These are the same condition
  (`eventually_nhds_iff`), and Agent023's affine pieces (`IsAffineFun`
  existential witnesses) unpack to exactly Agent024's `Affine n 1` bundles via
  `Matrix.mulVec`/`Matrix.dotProduct` unfolding.
* `depthBound n` is *literally* the same term `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`
  for both (`⌈·⌉₊` is notation for `Nat.ceil`), so `depth` is `rfl`.

So all four obligations are proved below in full; no refutation or `sorry` is
needed for this pair.
-/

/-- Evaluating an `Agent024.Affine` transformation at output coordinate `i`
unfolds to the expected weighted sum plus bias. -/
private lemma affine024_apply {a b : ℕ} (T : Agent024.Affine a b) (x : Fin a → ℝ) (i : Fin b) :
    T.toFun x i = (∑ j, T.A i j * x j) + T.c i := by
  simp [Agent024.Affine.toFun, Matrix.mulVec, Matrix.dotProduct, Pi.add_apply]

/-- `Agent023.IsAffineFun f` (the `∃ a b, f = fun x => (∑ i, a i * x i) + b` form) and
"`f` is computed by some `Agent024.Affine n 1` via its `0`-th coordinate" are the same
condition on `f`, just repackaging the same `(a, b)` data into a `1 × n` matrix bundle. -/
private lemma affine_iff {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    Agent023.IsAffineFun f ↔ ∃ T : Agent024.Affine n 1, f = fun x => T.toFun x 0 := by
  constructor
  · rintro ⟨a, b, hab⟩
    exact ⟨⟨(fun _ j => a j), fun _ => b⟩, by
      funext x; rw [hab]; exact (affine024_apply _ x 0).symm⟩
  · rintro ⟨T, hT⟩
    exact ⟨fun j => T.A 0 j, T.c 0, by
      funext x; rw [hT]; exact affine024_apply T x 0⟩

/-- `Agent023.IsReLUNetworkFunc k n f` (structural recursion on `k`, base case
`IsAffineFun`) and `Agent024.NetComputes n k f` (inductive family, base case
`Affine n 1`) describe the same "computed by a ReLU network with exactly `k`
hidden layers" condition. Proved by induction on `k`, converting the affine-map
data between the two (structurally identical) bundle types at each layer. -/
private lemma net_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent023.IsReLUNetworkFunc k n f ↔ Agent024.NetComputes n k f := by
  intro k
  induction k with
  | zero =>
      intro n f
      constructor
      · intro haff
        obtain ⟨T, hT⟩ := (affine_iff f).mp haff
        rw [hT]
        exact Agent024.NetComputes.base T
      · intro hnc
        obtain ⟨T⟩ := hnc
        exact (affine_iff _).mpr ⟨T, rfl⟩
  | succ k ih =>
      intro n f
      constructor
      · rintro ⟨m, T, g, hg, hf⟩
        have hg' : Agent024.NetComputes m k g := (ih m g).mp hg
        have heq : f = fun x => g (Agent024.reluVec ((⟨T.A, T.c⟩ : Agent024.Affine n m).toFun x)) := by
          funext x
          have hx : f x = g (Agent023.reluVec (T.eval x)) := by rw [hf]
          exact hx.trans rfl
        rw [heq]
        exact Agent024.NetComputes.step (⟨T.A, T.c⟩ : Agent024.Affine n m) hg'
      · intro hnc
        obtain ⟨m, T, f', hf'⟩ := hnc
        refine ⟨m, (⟨T.A, T.c⟩ : Agent023.AffineMap n m), f', (ih m f').mpr hf', ?_⟩
        funext x
        rfl

theorem cpwl (n : ℕ) : Agent023.CPWL n = Agent024.CPWL n := by
  ext f
  constructor
  · rintro ⟨hf, m, g, hg, hloc⟩
    choose a b hab using hg
    refine ⟨hf, m, fun j => (⟨(fun _ i => a j i), fun _ => b j⟩ : Agent024.Affine n 1), ?_⟩
    intro x
    obtain ⟨j, U, hUO, hxU, hUf⟩ := hloc x
    refine ⟨j, eventually_nhds_iff.mpr ⟨U, ?_, hUO, hxU⟩⟩
    intro y hy
    rw [hUf y hy, hab j]
    exact (affine024_apply _ y 0).symm
  · rintro ⟨hf, m, pieces, hloc⟩
    refine ⟨hf, m, fun j y => (pieces j).toFun y 0,
      fun j => ⟨fun i => (pieces j).A 0 i, (pieces j).c 0, by
        funext y; exact affine024_apply (pieces j) y 0⟩, ?_⟩
    intro x
    obtain ⟨j, hev⟩ := hloc x
    obtain ⟨U, hUf, hUO, hxU⟩ := eventually_nhds_iff.mp hev
    exact ⟨j, U, hUO, hxU, hUf⟩

theorem relun (n k : ℕ) : Agent023.ReLUn n k = Agent024.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (net_iff j n f).mp hf⟩
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (net_iff j n f).mpr hf⟩

/-- Both agents write `depthBound n` as `Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1`
(`⌈·⌉₊` is notation for `Nat.ceil`), so the two definitions are syntactically the
same term and agree by `rfl`, without even needing `hn`. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent023.depthBound n = Agent024.depthBound n := rfl

theorem statement :
    (∀ n, 3 ≤ n → Agent023.CPWL n = Agent023.ReLUn n (Agent023.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent024.CPWL n = Agent024.ReLUn n (Agent024.depthBound n)) := by
  constructor
  · intro h n hn
    have h1 := h n hn
    rw [cpwl n, relun n (Agent023.depthBound n), depth n hn] at h1
    exact h1
  · intro h n hn
    have h1 := h n hn
    rw [← depth n hn, ← relun n (Agent023.depthBound n), ← cpwl n] at h1
    exact h1

end Bridge_023_024

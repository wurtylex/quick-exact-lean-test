namespace Bridge_060_061

/-!
Agent060 and Agent061 are essentially the same formalization written twice:
* `depthBound` is the *literal same expression* `⌈Real.logb 3 ((n:ℝ)-1)⌉₊ + 1` in both.
* `CPWL` differs only in how "agrees with an affine piece near `x`" is phrased:
  Agent060 uses an explicit open set (`∃ U, IsOpen U ∧ x ∈ U ∧ EqOn f g U`), Agent061
  uses the `nhds` filter (`∀ᶠ y in nhds x, f y = h y`). These are the same statement via
  `mem_nhds_iff`, and the underlying `IsAffine`/`IsAffineFn` predicates are syntactically
  identical, so `CPWL` matches exactly.
* `ReLUn`/`represents`/`NetComputes` differ only in *how* an affine map is packaged:
  Agent060 bundles it as an `AffMap` structure with a `.eval` field, Agent061 uses a bare
  function together with an `IsAffineMap` existential. These describe the same class of
  functions, proved by induction on the hidden-layer count.
-/

private theorem represents_iff :
    ∀ (k n : ℕ) (f : Agent060.Vec n → ℝ),
      Agent060.represents n k f ↔ Agent061.NetComputes k n f := by
  intro k
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨T, hT⟩
      exact ⟨fun i => T.A 0 i, T.bias 0, fun x => by rw [hT x]; rfl⟩
    · rintro ⟨a, b, hf⟩
      exact ⟨⟨fun _ j => a j, fun _ => b⟩, fun x => by rw [hf x]; rfl⟩
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, T, g, hg, hf⟩
      exact ⟨m, T.eval, g, ⟨T.A, T.bias, fun x => rfl⟩, (ih m g).mp hg, hf⟩
    · rintro ⟨m, T, g, ⟨A, c, hT⟩, hg, hf⟩
      refine ⟨m, ⟨A, c⟩, g, (ih m g).mpr hg, fun x => ?_⟩
      have hTe : (⟨A, c⟩ : Agent060.AffMap n m).eval x = T x := (hT x).symm
      rw [hf x, hTe]

theorem cpwl (n : ℕ) : Agent060.CPWL n = Agent061.CPWL n := by
  ext f
  simp only [Agent060.CPWL, Agent061.CPWL, Agent061.IsCPWL, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hf, S, hS, hx⟩
    refine ⟨hf, S, hS, fun x => ?_⟩
    obtain ⟨g, hgS, U, hUo, hxU, hEq⟩ := hx x
    exact ⟨g, hgS, Filter.eventually_iff.mpr (mem_nhds_iff.mpr ⟨U, hEq, hUo, hxU⟩)⟩
  · rintro ⟨hf, S, hS, hx⟩
    refine ⟨hf, S, hS, fun x => ?_⟩
    obtain ⟨g, hgS, hev⟩ := hx x
    obtain ⟨U, hUsub, hUo, hxU⟩ := mem_nhds_iff.mp (Filter.eventually_iff.mp hev)
    exact ⟨g, hgS, U, hUo, hxU, hUsub⟩

theorem relun (n k : ℕ) : Agent060.ReLUn n k = Agent061.ReLUn n k := by
  ext f
  simp only [Agent060.ReLUn, Agent061.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k', hk', hf⟩
    exact ⟨k', hk', (represents_iff k' n f).mp hf⟩
  · rintro ⟨k', hk', hf⟩
    exact ⟨k', hk', (represents_iff k' n f).mpr hf⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent060.depthBound n = Agent061.depthBound n := rfl

theorem statement :
    (∀ n, 3 ≤ n → Agent060.CPWL n = Agent060.ReLUn n (Agent060.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent061.CPWL n = Agent061.ReLUn n (Agent061.depthBound n)) := by
  constructor
  · intro h n hn
    rw [← cpwl n, h n hn, relun n (Agent060.depthBound n), depth n hn]
  · intro h n hn
    rw [cpwl n, h n hn, ← depth n hn, ← relun n (Agent060.depthBound n)]

end Bridge_060_061

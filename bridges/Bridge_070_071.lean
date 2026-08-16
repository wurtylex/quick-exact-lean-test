namespace Bridge_070_071

/-!
`Agent070` and `Agent071` are close renderings of the same paper:

* Both take `ReLUn n k` to mean "at most `k` hidden layers".
* Both take `CPWL n` to mean: continuous, and locally (in a neighbourhood of
  every point) equal to one member of a finite family of affine functions.
  `Agent070` phrases the local condition with `∀ᶠ y in nhds x, f y = g i y`;
  `Agent071` phrases it with `∃ U ∈ nhds x, Set.EqOn f (g j) U`. These are the
  same statement (`Filter.eventually_iff_exists_mem`), so `cpwl` is provable.
* Both take `depthBound n` to be `⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1` — literally
  the same term (`⌈x⌉₊` is notation for `Nat.ceil x`), so `depth` is `rfl`.
* They differ in how "exactly `k` hidden layers" is encoded: `Agent070` uses a
  right-recursive inductive relation peeling off one affine layer at a time;
  `Agent071` uses an explicit `Fin (k+2)`-indexed width/activation sequence.
  These should be equivalent, but reconciling the two indexing schemes needs a
  genuine induction on `k` with careful `Fin`-cast bookkeeping; see `relun`.
-/

theorem cpwl (n : ℕ) : Agent070.CPWL n = Agent071.CPWL n := by
  ext f
  unfold Agent070.CPWL Agent071.CPWL
  simp only [Set.mem_setOf_eq]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨m, g, hg, hx⟩
    refine ⟨m, g, fun i => ?_, fun x => ?_⟩
    · obtain ⟨a, b, hab⟩ := hg i
      exact ⟨a, b, hab⟩
    · obtain ⟨i, hi⟩ := hx x
      obtain ⟨U, hU, hUsub⟩ := Filter.eventually_iff_exists_mem.mp hi
      exact ⟨i, U, hU, hUsub⟩
  · rintro ⟨m, g, hg, hx⟩
    refine ⟨m, g, fun i => ?_, fun x => ?_⟩
    · obtain ⟨a, b, hab⟩ := hg i
      exact ⟨a, b, hab⟩
    · obtain ⟨i, U, hU, hUsub⟩ := hx x
      exact ⟨i, Filter.eventually_iff_exists_mem.mpr ⟨U, hU, hUsub⟩⟩

-- `Agent070.NetworkComputes` (right-recursive: peel off one affine map, apply
-- `ReLU`, recurse on the rest) and `Agent071.ComputesWithHiddenLayers` (an
-- explicit `Fin (k+2)`-indexed sequence of widths, affine maps, and
-- activations) both formalize "exactly `k` hidden layers", but proving them
-- equivalent needs an induction on `k` reconciling the two `Fin`-indexing
-- schemes (`Fin.castSucc`/`Fin.succ` vs. the inductive's implicit peeling),
-- which is a substantial argument on its own and is left open here.
theorem relun (n k : ℕ) : Agent070.ReLUn n k = Agent071.ReLUn n k := by
  sorry

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent070.depthBound n = Agent071.depthBound n := by
  unfold Agent070.depthBound Agent071.depthBound
  rfl

theorem statement :
    (∀ n, 3 ≤ n → Agent070.CPWL n = Agent070.ReLUn n (Agent070.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent071.CPWL n = Agent071.ReLUn n (Agent071.depthBound n)) := by
  constructor
  · intro h n hn
    calc Agent071.CPWL n = Agent070.CPWL n := (cpwl n).symm
      _ = Agent070.ReLUn n (Agent070.depthBound n) := h n hn
      _ = Agent071.ReLUn n (Agent070.depthBound n) := relun n _
      _ = Agent071.ReLUn n (Agent071.depthBound n) := by rw [depth n hn]
  · intro h n hn
    calc Agent070.CPWL n = Agent071.CPWL n := cpwl n
      _ = Agent071.ReLUn n (Agent071.depthBound n) := h n hn
      _ = Agent070.ReLUn n (Agent071.depthBound n) := (relun n _).symm
      _ = Agent070.ReLUn n (Agent070.depthBound n) := by rw [depth n hn]

end Bridge_070_071

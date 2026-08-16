namespace Bridge_075_076

/-!
Bridge between `Agent075` and `Agent076`.

* `depthBound`: both agents use the *literal same* term
  `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`, so `depth` is `rfl`.
* `CPWL`: both agents use the same "local agreement with one of finitely many
  affine functions, on a neighborhood of every point" shape. They differ only
  in two cosmetic respects: `IsAffineFn` (Agent075) writes `∑ + b` while
  `IsAffineScalar` (Agent076) writes `c + ∑` (commutative, `ring` closes it),
  and Agent075 phrases the neighborhood condition as
  `∃ U ∈ nhds x, Set.EqOn f (g i) U` while Agent076 uses the filter notation
  `f =ᶠ[nhds x] g i`, which are the same proposition via
  `Filter.eventually_iff_exists_mem`. So `cpwl` is fully provable.
* `ReLUn`: Agent075 reads "exactly `k` hidden layers" (an inductive
  `ReLUNet a k` type indexed by `k`), Agent076 reads "at most `k` hidden
  layers" (`∃ k' ≤ k, ComputesWithHiddenLayers k' n f`). Taking `k' := k`
  shows `Agent075.ReLUn n k ⊆ Agent076.ReLUn n k` is easy, but the converse
  needs the padding lemma flagged in the spec (`x = ReLU x - ReLU (-x)` lets a
  layer act as the identity, so "at most k" collapses into "exactly k"); this
  is a genuine multi-step construction (induction on `k'`, doubling the
  hidden width at every subsequent layer to carry the padding through) that
  neither agent's file supplies and that is out of scope for a short bridge.
  So `relun` is left `sorry`, and since `statement` reduces to exactly this
  same missing equality (after substituting `cpwl` and `depth`), it is left
  `sorry` too.
-/

private lemma affineFn_iff_affineScalar {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    Agent075.IsAffineFn f ↔ Agent076.IsAffineScalar f := by
  constructor
  · rintro ⟨w, b, hw⟩
    exact ⟨w, b, fun x => by rw [hw x]; ring⟩
  · rintro ⟨a, c, hc⟩
    exact ⟨a, c, fun x => by rw [hc x]; ring⟩

private lemma eventuallyEq_iff_exists_eqOn {n : ℕ} (f g : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) :
    f =ᶠ[nhds x] g ↔ ∃ U ∈ nhds x, Set.EqOn f g U := by
  constructor
  · intro h
    rcases Filter.eventually_iff_exists_mem.mp h with ⟨U, hU, hU'⟩
    exact ⟨U, hU, fun y hy => hU' y hy⟩
  · rintro ⟨U, hU, hEq⟩
    exact Filter.eventually_iff_exists_mem.mpr ⟨U, hU, fun y hy => hEq hy⟩

theorem cpwl (n : ℕ) : Agent075.CPWL n = Agent076.CPWL n := by
  ext f
  simp only [Agent075.CPWL, Agent076.CPWL, Agent076.IsCPWL, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hf, m, g, hg, hloc⟩
    refine ⟨hf, m, g, fun i => (affineFn_iff_affineScalar (g i)).mp (hg i), fun x => ?_⟩
    obtain ⟨i, U, hU, hEq⟩ := hloc x
    exact ⟨i, (eventuallyEq_iff_exists_eqOn f (g i) x).mpr ⟨U, hU, hEq⟩⟩
  · rintro ⟨hf, m, g, hg, hloc⟩
    refine ⟨hf, m, g, fun i => (affineFn_iff_affineScalar (g i)).mpr (hg i), fun x => ?_⟩
    obtain ⟨i, hEq⟩ := hloc x
    obtain ⟨U, hU, hEqOn⟩ := (eventuallyEq_iff_exists_eqOn f (g i) x).mp hEq
    exact ⟨i, U, hU, hEqOn⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent075.depthBound n = Agent076.depthBound n := rfl

-- Missing: the padding lemma (`x = ReLU x - ReLU (-x)` realizes the identity
-- on an extra hidden layer), which is needed to turn Agent076's "at most k"
-- reading of `ReLUn` into Agent075's "exactly k" reading. Neither agent file
-- proves it, and it is a genuine multi-step induction, not a one-line fact.
theorem relun (n k : ℕ) : Agent075.ReLUn n k = Agent076.ReLUn n k := by
  sorry

-- Same missing padding lemma as `relun`: after rewriting both sides with
-- `cpwl` and `depth`, `statement` reduces to
-- `Agent075.ReLUn n (depthBound n) = Agent076.ReLUn n (depthBound n)` for
-- every `n`, i.e. exactly the content of `relun`.
theorem statement :
    (∀ n, 3 ≤ n → Agent075.CPWL n = Agent075.ReLUn n (Agent075.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent076.CPWL n = Agent076.ReLUn n (Agent076.depthBound n)) := by
  sorry

end Bridge_075_076

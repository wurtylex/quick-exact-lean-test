namespace Bridge_096_097

/-- Both `Agent096.depthBound` and `Agent097.depthBound` are the *identical*
formula `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1` (compare lines 90-91 of `Thm2_096.lean`
and 69-70 of `Thm2_097.lean`), so the two definitions are definitionally equal
and no hypothesis on `n` is even needed. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) :
    Agent096.depthBound n = Agent097.depthBound n := rfl

/-- Both `CPWL` predicates are the same "continuous, and every point has a
neighborhood on which `f` agrees with one of finitely many affine
functionals" condition. `Agent096` packages each affine functional as an
`AffMap n 1` (a matrix `A : Matrix (Fin 1) (Fin n) ℝ` together with a bias
`c : Fin 1 → ℝ`, evaluated as `A.mulVec x + c`), while `Agent097` packages the
same data directly as a row `A : Fin n → ℝ` and a scalar `b : ℝ`, evaluated as
`∑ j, A j * x j + b`. These are the same functional under the obvious
identification `A096 0 j ↔ A097 j` and `c096 0 ↔ b097`, so we convert
pointwise. -/
theorem cpwl (n : ℕ) : Agent096.CPWL n = Agent097.CPWL n := by
  ext f
  simp only [Agent096.CPWL, Agent097.CPWL, Agent097.IsCPWL, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hf, m, g, hg⟩
    refine ⟨hf, m, fun i j => (g i).A 0 j, fun i => (g i).c 0, fun x => ?_⟩
    obtain ⟨i, hi⟩ := hg x
    refine ⟨i, ?_⟩
    filter_upwards [hi] with y hy
    rw [hy]
    simp only [Agent096.AffMap.eval, Pi.add_apply, Matrix.mulVec, dotProduct]
  · rintro ⟨hf, m, A, b, hAb⟩
    refine ⟨hf, m, fun i => ⟨fun _ j => A i j, fun _ => b i⟩, fun x => ?_⟩
    obtain ⟨i, hi⟩ := hAb x
    refine ⟨i, ?_⟩
    filter_upwards [hi] with y hy
    rw [hy]
    simp only [Agent096.AffMap.eval, Pi.add_apply, Matrix.mulVec, dotProduct]

/- `relun` left as `sorry`: `Agent096.ReLUn` is built on an *inductive*, typed
"chain of `AffMap`s" representation of ReLU networks (`ReLUNet`), while
`Agent097.ReLUn` is built on a *recursive Prop*-valued predicate
(`ComputesWithHiddenLayers`) peeling off layers one at a time. Both plausibly
describe the same "at most `k` hidden layers" class, but proving it requires
an induction establishing an equivalence between the two network encodings
(matching each `ReLUNet.step`/`ReLUNet.last` constructor against the
existential layer-by-layer unfolding of `ComputesWithHiddenLayers`), which is
well beyond a quick-win budget. -/
theorem relun (n k : ℕ) : Agent096.ReLUn n k = Agent097.ReLUn n k := sorry

/- `statement` left as `sorry`: it reduces to `relun` plus `depth` plus `cpwl`
via `congrArg`/`Eq.trans`, but since `relun` (the equality of the ReLU-network
classes at a fixed depth) is not established above, we cannot assemble the iff
here either without reproving that missing piece. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent096.CPWL n = Agent096.ReLUn n (Agent096.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent097.CPWL n = Agent097.ReLUn n (Agent097.depthBound n)) := sorry

end Bridge_096_097

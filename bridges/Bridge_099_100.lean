namespace Bridge_099_100

/-!
Agent099 and Agent100 use essentially the same skeleton: `relu`, `reluVec`,
an affine-map structure (`AffMap` vs `AffineTransform`), `CPWL` as
"continuous + finite family of affine pieces, locally agreeing everywhere",
and `depthBound = ⌈log_3(n-1)⌉ + 1`. The one real divergence is `ReLUn`:
Agent099 reads it as "at most k hidden layers" (∃ k' ≤ k, …) while Agent100
reads it as "exactly k hidden layers" (recursive `IsReLURepresentable`).
-/

/-- `IsAffineFn` (099, raw coefficient vector) and `IsAffineFun` (100, via a
1-output `AffineTransform`) describe the same set of functions: an
`AffineTransform n 1` is exactly a row vector `A 0 ·` plus a bias `bias 0`. -/
theorem aff_iff (n : ℕ) (g : (Fin n → ℝ) → ℝ) :
    Agent099.IsAffineFn n g ↔ Agent100.IsAffineFun n g := by
  constructor
  · rintro ⟨a, b, hab⟩
    refine ⟨⟨fun _ j => a j, fun _ => b⟩, ?_⟩
    intro x
    simp [Agent100.AffineTransform.toFun, Matrix.mulVec, Matrix.dotProduct, hab]
  · rintro ⟨T, hT⟩
    refine ⟨fun j => T.A 0 j, T.bias 0, ?_⟩
    intro x
    simpa [Agent100.AffineTransform.toFun, Matrix.mulVec, Matrix.dotProduct] using hT x

/-- Both `CPWL` definitions are literally
`Continuous f ∧ ∃ m g, (∀ i, <affine predicate> (g i)) ∧ ∀ x, ∃ i, f =ᶠ[𝓝 x] g i`,
differing only in the affine predicate, which `aff_iff` shows coincide. -/
theorem cpwl (n : ℕ) : Agent099.CPWL n = Agent100.CPWL n := by
  ext f
  unfold Agent099.CPWL Agent100.CPWL
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hf, m, g, hg, hloc⟩
    exact ⟨hf, m, g, fun i => (aff_iff n (g i)).mp (hg i), hloc⟩
  · rintro ⟨hf, m, g, hg, hloc⟩
    exact ⟨hf, m, g, fun i => (aff_iff n (g i)).mpr (hg i), hloc⟩

/-- Both agents encode the depth bound with the literally identical term
`⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1` (099 via `⌈·⌉₊` notation, 100 via the
spelled-out `Nat.ceil`, which are the same notation), so the two `depthBound`
functions are definitionally equal. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent099.depthBound n = Agent100.depthBound n := rfl

/-- SORRY: Agent099's `ReLUn n k` is "representable with *at most* `k` hidden
layers" (`∃ k' ≤ k, …`), while Agent100's is "representable with *exactly*
`k` hidden layers" (recursive `IsReLURepresentable`). These coincide only via
the padding lemma noted in the spec (`x ↦ relu x - relu (-x)` lets a layer
act as the identity, converting a `k'`-layer network into a `k`-layer one for
`k' ≤ k`), which neither agent's file proves and which is too long to prove
from scratch within this bridge's budget. -/
theorem relun (n k : ℕ) : Agent099.ReLUn n k = Agent100.ReLUn n k := by
  sorry

/-- SORRY: depends on `relun`, which is unresolved (see above); without
knowing whether `ReLUn` actually agrees at the bound `depthBound n`, the
biconditional between the two `theorem2` statements cannot be established
without appealing to the (sorry'd) `theorem2`s themselves, which is
disallowed. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent099.CPWL n = Agent099.ReLUn n (Agent099.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent100.CPWL n = Agent100.ReLUn n (Agent100.depthBound n)) := by
  sorry

end Bridge_099_100

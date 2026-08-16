namespace Bridge_066_067

/-!
## Summary

* `depthBound`: both agents write the *identical* term
  `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`. Definitionally equal, `rfl` closes it. **PROVED**.
* `ReLUn`: Agent066 reads "computed with `k` hidden layers" as *at most* `k`
  (`∃ k' ≤ k, ReLUComputable n k' f`); Agent067 reads it as *exactly* `k`
  (`Represents n k f`). These classes coincide only via the padding trick
  `x = ReLU x - ReLU (-x)` (turning a `k'`-layer net into an equivalent `k`-layer one for
  `k' ≤ k`), which neither file proves and which the spec explicitly flags as unproved
  by anyone. **SORRY**.
* `CPWL`: both agents use the *same* family — "continuous, and every point has a
  neighbourhood on which `f` agrees with one member of a fixed finite family of affine
  functions" — so there is no family-(a)-vs-(b) mismatch here. They differ only in how an
  "affine function" is packaged: Agent066 uses Mathlib's bundled
  `(Fin n → ℝ) →ᵃ[ℝ] ℝ`; Agent067 uses an explicit weight vector/bias pair
  `∑ j, w i j * y j + b i`. Bridging these requires decomposing a bundled affine map into
  `linear + constant` and then the linear part into `∑ j, y j * L (Pi.single j 1)` via a
  basis expansion of `Fin n → ℝ` — real Mathlib affine-space API that this short bridge
  does not chase down. **SORRY**.
* `statement`: would follow immediately from `cpwl`, `relun` and `depth` by rewriting one
  side into the other, but since `relun` (and `cpwl`) are open above, so is this.
  **SORRY**.
-/

/-! ### `depthBound` -/

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent066.depthBound n = Agent067.depthBound n := rfl

/-! ### `ReLUn` -/

-- Agent066's `ReLUn n k` is "at most `k` hidden layers", Agent067's is "exactly `k`".
-- These agree only via a padding lemma (any `k'`-layer network can be re-expressed with
-- `k' + 1` layers using an extra layer computing the identity via
-- `x = ReLU x - ReLU (-x)`, then induction on `k - k'`), which is not proved in either
-- source file and is not attempted here.
theorem relun (n k : ℕ) : Agent066.ReLUn n k = Agent067.ReLUn n k := by
  sorry

/-! ### `CPWL` -/

-- Same "local agreement with a finite affine family" definition on both sides, differing
-- only in how the affine pieces are represented (bundled `AffineMap` vs. explicit
-- weight/bias pair). Converting between the two representations needs the affine-map
-- decomposition `g y = g.linear y + g 0` together with a basis expansion of
-- `Fin n → ℝ` to turn `g.linear` into an explicit weighted sum; this is genuine Mathlib
-- affine-space API that a short bridge file should not gamble on getting right unchecked.
theorem cpwl (n : ℕ) : Agent066.CPWL n = Agent067.CPWL n := by
  sorry

/-! ### `statement` -/

-- Would follow from `cpwl`, `relun`, and `depth` by rewriting `CPWL n`, `ReLUn n _`, and
-- `depthBound n` on one side into the other; since `relun` and `cpwl` are open above,
-- this inherits their gap rather than being independently harder.
theorem statement :
    (∀ n, 3 ≤ n → Agent066.CPWL n = Agent066.ReLUn n (Agent066.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent067.CPWL n = Agent067.ReLUn n (Agent067.depthBound n)) := by
  sorry

end Bridge_066_067

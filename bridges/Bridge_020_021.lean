namespace Bridge_020_021

/-!
Link 020 → 021.

`Thm2_020.lean` has an upstream elaboration error of its own: in
`Agent020.AffineMap.eval` the expression `T.1.mulVec x + T.2` fails to
elaborate (`HAdd (Fin b → ℝ) (Vec b)` instance failure — `Vec b` is a plain,
non-`@[reducible]` `def`, and the `+` binop elaborator does not unfold it to
see that `Fin b → ℝ` and `Vec b` are the same type). Lean's error recovery
still adds `AffineMap.eval` to the environment at its declared type, but its
*value* becomes a synthetic `sorry` placeholder, so we have no mathematical
information whatsoever about what it computes on any input. Since
`Agent020.IsAffineFun`, `Agent020.CPWL`, and `Agent020.ReLUn` (via
`Agent020.ReLUNet.compute`) are all built directly on top of
`Agent020.AffineMap.eval`, none of them can be honestly related to
`Agent021`'s counterparts from here: we can neither construct a witness
affine map with known behaviour (to prove membership/equality) nor rule one
out (to prove non-membership/inequality). Separately, even setting the
opacity aside, `Agent020.CPWL` uses the "local agreement" reading of
piecewise-linearity (`∀ x, ∃ i, ∀ᶠ y in nhds x, f y = affines i y`) while
`Agent021.CPWL` uses a genuine finite polyhedral subdivision — on a connected
domain, local agreement with finitely many *genuinely* affine pieces forces
the whole function to be a single globally affine map (two affine functions
agreeing on a nonempty open set are equal everywhere, and the open sets
`{x | f =ᶠ[nhds x] affines i}` must then partition ℝⁿ), which would make
`Agent020.CPWL` strictly smaller than `Agent021.CPWL` (e.g. it would exclude
`fun x => max 0 (x 0)`, which is not affine near `0`). We cannot invoke this
argument formally, though, because `IsAffineFun` no longer provably picks out
genuinely affine functions once `AffineMap.eval` is opaque.

Only `depthBound` never touches `AffineMap`/`eval`, so `depth` is the one
obligation provable here.
-/

/-- `depthBound` never mentions `AffineMap`/`eval`, so it is unaffected by the
upstream elaboration bug: `Agent020` casts the truncated `n - 1 : ℕ` to `ℝ`,
`Agent021` subtracts `1` after casting `n` to `ℝ`; these agree once `n ≥ 1`
(in particular for `n ≥ 3`) by `Nat.cast_sub`. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent020.depthBound n = Agent021.depthBound n := by
  have h1n : (1 : ℕ) ≤ n := by omega
  have h1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub h1n, Nat.cast_one]
  unfold Agent020.depthBound Agent021.depthBound
  rw [h1]

-- `Agent020.CPWL` is built from `IsAffineFun`, which existentially
-- quantifies over `AffineMap.eval`-images; since `AffineMap.eval` elaborated
-- to an opaque `sorry` (see the note above), we have no information tying
-- `Agent020.CPWL` to any genuine affine/piecewise-affine structure, so
-- equality with `Agent021.CPWL` (an honest finite-polyhedral-subdivision
-- definition) can neither be proved nor refuted from the data available.
theorem cpwl (n : ℕ) : Agent020.CPWL n = Agent021.CPWL n := by
  sorry

-- Same blocker as `cpwl`: `Agent020.ReLUn` is defined via
-- `Agent020.ReLUNet.compute`, whose base case calls the opaque
-- `Agent020.AffineMap.eval`, so nothing can be proved about which functions
-- `Agent020.ReLUn n k` actually contains (nor, therefore, about how it
-- compares to `Agent021.ReLUn n k`, which additionally reads "at most k"
-- hidden layers rather than "exactly k").
theorem relun (n k : ℕ) : Agent020.ReLUn n k = Agent021.ReLUn n k := by
  sorry

-- Both directions of this iff would require knowing the truth value of
-- `Agent020`'s own `∀ n ≥ 3, CPWL n = ReLUn n (depthBound n)`, which is
-- inaccessible for the same reason as `cpwl`/`relun`: it is stated purely in
-- terms of `Agent020.CPWL`/`Agent020.ReLUn`, both of which are opaque because
-- of the broken `AffineMap.eval`, so the biconditional cannot be established
-- in either direction from the data available here.
theorem statement :
    (∀ n, 3 ≤ n → Agent020.CPWL n = Agent020.ReLUn n (Agent020.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent021.CPWL n = Agent021.ReLUn n (Agent021.depthBound n)) := by
  sorry

end Bridge_020_021

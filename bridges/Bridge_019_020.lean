namespace Bridge_019_020

/-!
## Comparison of Agent019 and Agent020

`depthBound` is the one obligation untouched by any elaboration issue: Agent019 writes
`⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1` directly on the real number `(n:ℝ) - 1`, while Agent020
first truncated-subtracts in `ℕ` and casts, `⌈Real.logb 3 (↑(n - 1))⌉₊ + 1`. For `n ≥ 3`
(in fact `n ≥ 1` suffices) `Nat.cast_sub` shows `(↑(n - 1) : ℝ) = (n:ℝ) - 1`, so the two
expressions coincide and `depth` is proved below.

The other three obligations are all blocked by a genuine elaboration error already
present in `Thm2_020.lean` (not introduced or fixable by us; we must not edit that file):

```
def AffineMap.eval {a b : ℕ} (T : AffineMap a b) (x : Vec a) : Vec b :=
  T.1.mulVec x + T.2
```

fails typeclass synthesis for `HAdd (Fin b → ℝ) (Vec b) _`: `Agent020.Vec b` is a plain
`def` wrapping `Fin b → ℝ`, and it does not unify with the `Pi`-type `HAdd` instance
during instance search. Lean's recovery keeps the *declared type* of `AffineMap.eval`
in the environment (so `Agent020.IsAffineFun`, `Agent020.CPWL`, `Agent020.ReLUNet`,
`Agent020.ReLUNet.compute`, and `Agent020.ReLUn` all still exist as terms of their
stated types and are nameable from here), but the *value* of `AffineMap.eval` is a stuck
term with no available defining equation. Concretely, we cannot prove
`AffineMap.eval T x = T.1.mulVec x + T.2` (or anything else about what `T.eval x`
computes to), which is exactly what would be needed to relate `Agent020.IsAffineFun`
(and hence `Agent020.CPWL`) to Agent019's concrete `∑ i, a i * x i + b` characterization,
or to relate `Agent020.ReLUn` (built from `ReLUNet.compute`, which calls `.eval`) to
Agent019's `ReLUNetwork`/`AffineMap'.apply` (which is *not* affected by this bug — the
error is entirely on Agent020's side). Since we can neither exhibit a witness with a
known value nor derive a contradiction from an unknown/stuck one, `cpwl`, `relun`, and
`statement` are each left as an honest `sorry`, with a one-line pointer to this root
cause immediately above the theorem.
-/

/-- Both sides reduce to `⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1` once Agent020's
`((n - 1 : ℕ) : ℝ)` is rewritten via `Nat.cast_sub` (valid since `1 ≤ n`). -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent019.depthBound n = Agent020.depthBound n := by
  have h1 : (1 : ℕ) ≤ n := by omega
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub h1, Nat.cast_one]
  unfold Agent019.depthBound Agent020.depthBound
  rw [hcast]

-- Blocked: `Agent020.IsAffineFun` (hence `Agent020.CPWL`) is defined through the stuck
-- `Agent020.AffineMap.eval`; we cannot show its witnesses compute Agent019's
-- `∑ i, a i * x i + b` form, nor exhibit a mismatch, since `.eval`'s value is unknown.
theorem cpwl (n : ℕ) : Agent019.CPWL n = Agent020.CPWL n := by
  sorry

-- Blocked: `Agent020.ReLUn` is built from `Agent020.ReLUNet.compute`, which calls the
-- stuck `Agent020.AffineMap.eval`; relating "at most k" (Agent019) to "exactly k"
-- (Agent020) also needs an unproved padding lemma (`x = ReLU x - ReLU (-x)`) on top of
-- that, and neither a proof nor a counterexample can be completed without a known value
-- for `.eval`.
theorem relun (n k : ℕ) : Agent019.ReLUn n k = Agent020.ReLUn n k := by
  sorry

-- Blocked: this would normally follow from `cpwl`, `relun`, `depth` by pointwise
-- rewriting (as in other bridges), but `cpwl`/`relun` are themselves blocked by the
-- `Agent020.AffineMap.eval` issue above; independently, both agents' own `theorem2` are
-- `sorry` in their source files, so neither side of this `Iff` is otherwise accessible.
theorem statement :
    (∀ n, 3 ≤ n → Agent019.CPWL n = Agent019.ReLUn n (Agent019.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent020.CPWL n = Agent020.ReLUn n (Agent020.depthBound n)) := by
  sorry

end Bridge_019_020

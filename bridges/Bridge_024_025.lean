namespace Bridge_024_025

/-!
Bridge between `Agent024` and `Agent025`'s formalizations of Theorem 2.

Comparing the two source files:

* `depthBound`: both are literally `⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1` — Agent024 spells the
  ceiling as `Nat.ceil (...)` and Agent025 as `⌈...⌉₊`, but `⌈x⌉₊` is notation for
  `Nat.ceil x`, so the two definitions are syntactically identical after unfolding.
* `CPWL`: both are "continuous, and locally near every point equal to one of finitely
  many affine functions." Agent024 packages each affine piece as its own `Affine n 1`
  structure (matrix `A : Matrix (Fin 1) (Fin n) ℝ` and bias `c : Fin 1 → ℝ`, evaluated via
  `Matrix.mulVec`); Agent025 packages each affine piece as a bare function `g i` together
  with a separate `IsAffine n (g i)` witness (coefficient vector `a : Fin n → ℝ` and
  constant `c : ℝ`, evaluated via an explicit `∑`). These are the same mathematical
  object (a `1 × n` matrix *is* a coefficient vector, `Matrix.mulVec` unfolds to the same
  `∑ j, A i j * x j` that Agent025 writes by hand), so `cpwl` is provable by translating
  finite families of pieces back and forth between the two encodings.
* `ReLUn`: Agent024 uses "**at most** `k` hidden layers" (`∃ k' ≤ k, NetComputes n k' f`);
  Agent025 uses "**exactly** `k` hidden layers" (`NetworkComputable n k f`). As
  BRIDGE_SPEC.md notes, these coincide only via a padding argument (`x = ReLU x - ReLU
  (-x)` lets one extra hidden layer simulate the identity, so a shallower network can
  always be padded out to exactly `k` layers), composed with a translation between
  Agent024's inductive `NetComputes` and Agent025's recursive `NetworkComputable` (which
  encode the *same* "exactly `k` layers" notion via different Lean mechanisms: an
  inductive predicate vs. a structurally recursive `def`). Both pieces are individually
  routine but their composition is substantial multi-lemma engineering that I was not
  able to complete reliably without a compiler in the time available; see the `sorry` at
  `relun` for the precise gap. `statement` inherits the same gap, since converting
  Agent024's instance of Theorem 2 into Agent025's requires equating
  `Agent024.ReLUn n (depthBound n)` with `Agent025.ReLUn n (depthBound n)`, i.e. exactly
  the unproved direction of `relun`.
-/

theorem cpwl (n : ℕ) : Agent024.CPWL n = Agent025.CPWL n := by
  ext f
  constructor
  · rintro ⟨hcont, N, pieces, hloc⟩
    refine ⟨hcont, N, fun i x => (pieces i).toFun x 0, fun i => ?_, fun x => hloc x⟩
    exact ⟨fun j => (pieces i).A 0 j, (pieces i).c 0, fun x => by
      simp [Agent024.Affine.toFun, Matrix.mulVec, dotProduct, Pi.add_apply]⟩
  · rintro ⟨hcont, m, g, hg, hloc⟩
    choose a c hac using hg
    refine ⟨hcont, m, fun i => ⟨Matrix.of (fun (_ : Fin 1) j => a i j), fun _ => c i⟩, fun x => ?_⟩
    obtain ⟨i, hi⟩ := hloc x
    refine ⟨i, ?_⟩
    filter_upwards [hi] with y hy
    rw [hy, hac i y]
    simp [Agent024.Affine.toFun, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.add_apply]

-- SORRY: Agent024.ReLUn n k is "∃ k' ≤ k, NetComputes n k' f" (at most k hidden layers);
-- Agent025.ReLUn n k is "NetworkComputable n k f" (exactly k hidden layers). These sets
-- are equal, but the proof needs (a) a translation lemma
-- `Agent024.NetComputes n k f ↔ Agent025.NetworkComputable n k f` between the two
-- "exactly k layers" encodings (one inductive, one a recursive `def`), and (b) a padding
-- lemma `NetworkComputable n k f → NetworkComputable n (k+1) f`, built by prepending a
-- width-`2n` identity-simulating hidden layer using `x = ReLU x - ReLU (-x)`. As
-- BRIDGE_SPEC.md flags, this padding lemma is not proved in any of the source files; I
-- was not able to assemble a reliable, uncompiled proof of the full composition in the
-- time available, and prefer an honest `sorry` here to a fragile, likely-broken term.
theorem relun (n k : ℕ) : Agent024.ReLUn n k = Agent025.ReLUn n k := by
  sorry

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent024.depthBound n = Agent025.depthBound n := by
  simp only [Agent024.depthBound, Agent025.depthBound]

-- SORRY: depends on `relun` (specifically, on `Agent024.ReLUn n (depthBound n) =
-- Agent025.ReLUn n (depthBound n)`, needed to convert Agent024's instance of Theorem 2
-- into Agent025's and vice versa), which is left `sorry` above for the reasons given
-- there.
theorem statement :
    (∀ n, 3 ≤ n → Agent024.CPWL n = Agent024.ReLUn n (Agent024.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent025.CPWL n = Agent025.ReLUn n (Agent025.depthBound n)) := by
  sorry

end Bridge_024_025

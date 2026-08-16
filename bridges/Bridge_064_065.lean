namespace Bridge_064_065

/-!
## Summary of the comparison

* `depthBound`: Agent064 casts `n - 1` (truncated ℕ subtraction) to `ℝ` before taking
  `logb`; Agent065 casts `n` to `ℝ` first and subtracts `1` in `ℝ`. For `n ≥ 3` (in fact
  for `n ≥ 1`) these coincide via `Nat.cast_sub`. **PROVED**.
* `CPWL`: both agents use the *same* style of definition — continuity plus a finite
  family of affine functions such that every point has a neighbourhood on which `f`
  agrees with one member of the family. Agent064 phrases the neighbourhood explicitly
  (`∃ U, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, …`); Agent065 phrases it via `∀ᶠ y in nhds x, …`.
  These are literally the same condition (`mem_nhds_iff` / `Filter.mem_of_superset`
  convert between them), and the finite family of affine coefficients on one side
  transports directly to the finite family of `IsAffineFun` witnesses on the other.
  **PROVED**.
* `ReLUn`: both agents use the "exactly `k` hidden layers" reading, but they encode the
  chain of affine layers very differently: Agent064 uses a `List Layer` (each layer
  self-describing its own `inDim`/`outDim`, evaluated by an auxiliary recursive
  `evalLayers` on dimension-tagged (`Σ'`) vectors, with mismatched dimensions producing a
  dummy `0`-dimensional value), while Agent065 uses a `ReLUNetwork n k` structure carrying
  a *total* function `dims : ℕ → ℕ` together with `dims_zero`/`dims_last` proofs and a
  dependently-typed `layer : (i : ℕ) → Affine (dims i) (dims (i+1))`. Converting between
  these requires (a) proving, by induction on the list, that the dimension chain forced by
  Agent064's success condition (`n = (L.get 0).inDim`, consecutive `outDim = inDim`,
  final `outDim = 1`) actually holds, (b) building a `dims : ℕ → ℕ` total function and
  filler data for indices past `k+1` for Agent065's structure, and (c) an accompanying
  induction matching `ReLUNetwork.forward i` against `evalLayers` on the list, all across
  `Fin.cast`/`▸`-rewritten vectors. This is a genuine and substantial piece of dependent-
  type bookkeeping (not a short rewrite), so it is left as `sorry` rather than risking an
  unverified, possibly-broken induction. **SORRY**.
* `statement`: reduces, after using `cpwl` and `depth`, to the single missing fact
  `Agent064.ReLUn n (Agent065.depthBound n) = Agent065.ReLUn n (Agent065.depthBound n)`,
  i.e. exactly the `relun` equivalence above at the specific depth. Since that has not
  been established, `statement` is left as `sorry` as well. **SORRY**.

Mathematically, Agent065's rendering is very slightly closer to the paper: its
`ReLUNetwork` structure carries an explicit dimension function `dims` mirroring the
paper's `d_0, d_1, …, d_{k+1}` sequence directly, whereas Agent064's list-of-self-
describing-layers encoding only recovers that sequence indirectly (and has to fall back
on a dummy value when dimensions do not chain). Both `CPWL` definitions are equally
faithful "local piecewise-affine" renderings.
-/

/-! ### `depthBound` -/

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent064.depthBound n = Agent065.depthBound n := by
  have h1 : (1 : ℕ) ≤ n := by omega
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub h1, Nat.cast_one]
  simp only [Agent064.depthBound, Agent065.depthBound, hcast]

/-! ### `CPWL` -/

theorem cpwl (n : ℕ) : Agent064.CPWL n = Agent065.CPWL n := by
  ext f
  constructor
  · rintro ⟨hcont, m, a, b, hloc⟩
    refine ⟨hcont, m, (fun i y => (∑ j, a i j * y j) + b i), fun i => ⟨a i, b i, fun _ => rfl⟩, ?_⟩
    intro x
    obtain ⟨i, U, hUopen, hxU, hUeq⟩ := hloc x
    exact ⟨i, Filter.mem_of_superset (hUopen.mem_nhds hxU) (fun y hy => hUeq y hy)⟩
  · rintro ⟨hcont, m, g, hg, hloc⟩
    unfold Agent065.IsAffineFun at hg
    choose a b hab using hg
    refine ⟨hcont, m, a, b, ?_⟩
    intro x
    obtain ⟨i, hev⟩ := hloc x
    have hmem : {y | f y = g i y} ∈ nhds x := hev
    obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp hmem
    exact ⟨i, U, hUopen, hxU, fun y hy => (hUsub hy).trans (hab i y)⟩

/-! ### `ReLUn` -/

-- Both agents use the "exactly `k` hidden layers" reading, but Agent064 encodes a
-- network as a `List Layer` of self-describing (inDim/outDim-tagged) affine maps
-- evaluated via `evalLayers` on `Σ'`-packaged vectors, while Agent065 encodes it as a
-- `ReLUNetwork n k` structure carrying a total `dims : ℕ → ℕ` function and a dependently
-- typed `layer` field. Bridging the two requires reconstructing, by induction on the
-- list, the dimension chain that Agent064's success hypothesis forces (since a mismatch
-- collapses `evalLayers` to a dummy `0`-dimensional value that can never equal the
-- required `1`-dimensional output), then building the matching `ReLUNetwork` (with
-- arbitrary filler data for indices beyond `k+1`) and an accompanying `Fin.cast`-laden
-- induction showing `ReLUNetwork.forward` tracks `evalLayers`. This is substantial
-- dependent-type engineering that risks being wrong without the ability to compile, so
-- it is left honest as `sorry` rather than faked.
theorem relun (n k : ℕ) : Agent064.ReLUn n k = Agent065.ReLUn n k := by
  sorry

/-! ### `statement` -/

-- Follows from `cpwl`, `depth`, and the specific instance
-- `Agent064.ReLUn n (Agent065.depthBound n) = Agent065.ReLUn n (Agent065.depthBound n)`
-- of `relun`, which was left `sorry` above for the reasons given there.
theorem statement :
    (∀ n, 3 ≤ n → Agent064.CPWL n = Agent064.ReLUn n (Agent064.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent065.CPWL n = Agent065.ReLUn n (Agent065.depthBound n)) := by
  sorry

end Bridge_064_065

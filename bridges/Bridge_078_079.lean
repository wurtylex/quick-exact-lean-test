namespace Bridge_078_079

/-
Both files are structurally very close: `CPWL` is a genuine polyhedral-subdivision-style
definition (continuous + finite family of affine pieces, locally agreeing with `f` at every
point) in both, `ReLUn n k` means "at most `k` hidden layers" in both, and `depthBound` is the
literal same expression `⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1` in both. The only real difference is
*how* `CPWL`'s "local agreement" is phrased (`∀ᶠ y in nhds x, …` in `Agent078` vs.
`∃ ε > 0, ∀ y, dist y x < ε → …` in `Agent079`) and *how* a ReLU network is encoded
(`ℕ`-indexed sequences with `width`/`A`/`b` functions in `Agent078` vs. an inductive
`ReLUNet` type built from genuine `Matrix (Fin b) (Fin a) ℝ` affine transformations in
`Agent079`).
-/

/-- `CPWL_078 n = CPWL_079 n`: the two "local agreement" phrasings are the standard
`Metric.eventually_nhds_iff` unfolding of `∀ᶠ y in nhds x, P y`, applied pointwise; the
`IsAffine` predicates are literally the same definition up to a bound-variable name, so they
match by `rfl`/defeq. -/
theorem cpwl (n : ℕ) : Agent078.CPWL n = Agent079.CPWL n := by
  ext f
  constructor
  · rintro ⟨hf, m, g, hg, hloc⟩
    refine ⟨hf, m, g, hg, fun x => ?_⟩
    obtain ⟨i, hi⟩ := hloc x
    exact ⟨i, Metric.eventually_nhds_iff.mp hi⟩
  · rintro ⟨hf, m, g, hg, hloc⟩
    refine ⟨hf, m, g, hg, fun x => ?_⟩
    obtain ⟨i, hi⟩ := hloc x
    exact ⟨i, Metric.eventually_nhds_iff.mpr hi⟩

/-- `depthBound` is the syntactically identical expression `⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1`
in both files, so the two `def`s agree by `rfl` (the `noncomputable` annotation on
`Agent079.depthBound` only affects code generation, not kernel reduction). -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent078.depthBound n = Agent079.depthBound n := rfl

/-- LEFT AS `sorry`. `Agent078.ReLUNetwork`/`netForward` represent a network as `ℕ → ℝ`
sequences together with `width : ℕ → ℕ` and matrices `A : ℕ → ℕ → ℕ → ℝ` indexed by bare
naturals (meaningful only below `width i`), whereas `Agent079.ReLUNet`/`eval` is an inductive
family built from genuine `Matrix (Fin b) (Fin a) ℝ` affine transformations. The two encodings
are isomorphic — both alternate an affine map and componentwise ReLU for exactly `k' + 1`
layers ending in a width-1 output — but proving `ReLUn n k` equal as *sets* requires an
explicit two-way translation between the representations, built by induction on the network
(`ReLUNetwork` → `ReLUNet` needs picking out the first `width 1` matrix rows/entries as a
genuine `Fin`-indexed `Matrix`; `ReLUNet` → `ReLUNetwork` needs padding matrix entries with
zeros outside the finite range and reproving `netForward` computes the same values as `eval`
by induction on the layer index). This is a substantial construction not attempted here. -/
theorem relun (n k : ℕ) : Agent078.ReLUn n k = Agent079.ReLUn n k := sorry

/-- LEFT AS `sorry`. This statement is equivalent (via `cpwl` and `depth`, both proved above)
to `Agent078.ReLUn n (Agent078.depthBound n) = Agent079.ReLUn n (Agent079.depthBound n)` for
every `n ≥ 3`, i.e. exactly the same network-representation gap left open in `relun` above,
just specialized to `k = depthBound n` rather than universally quantified over `k`. Since that
gap is not closed, this `iff` is not established either. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent078.CPWL n = Agent078.ReLUn n (Agent078.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent079.CPWL n = Agent079.ReLUn n (Agent079.depthBound n)) := sorry

end Bridge_078_079

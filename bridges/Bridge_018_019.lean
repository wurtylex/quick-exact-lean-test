namespace Bridge_018_019

/-!
# Bridge between `Agent018` and `Agent019`

Both formalizations use essentially the *same* modelling choices for `CPWL` and
`depthBound`, differing only in superficial encoding:

* `depthBound` is defined by the *identical* expression
  `Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1` in both files.
* `CPWL n` in both files is `Continuous f` together with a finite family of scalar
  affine functions such that every point has a neighbourhood on which `f` agrees
  with (at least) one of them. `Agent018` bundles each affine function as a
  `ScalarAffine` structure with an explicit `.eval`; `Agent019` instead uses bare
  functions `(Fin n → ℝ) → ℝ` together with a separate `IsAffineFun` predicate.
  These two encodings describe the same set of functions.
* `ReLUn n k` in both files is "representable by a network with *at most* `k`
  hidden layers", but the underlying network types are genuinely different data
  structures: `Agent018.ReLUNet` is an inductive alternating-composition type,
  while `Agent019.ReLUNetwork` is a structure carrying an explicit `widths : ℕ → ℕ`
  function together with per-layer affine maps indexed against that function. They
  almost certainly describe the same set of representable functions (both are just
  "chains of affine maps interleaved with ReLU, free choice of intermediate
  dimensions"), but proving this requires constructing an explicit
  dimension-matching translation between the two network types, transporting terms
  along the `widths`/`width_zero`/`width_last` proof obligations at every layer.
  That is a substantial dependent-type construction that cannot be checked by
  compiling in this environment, so honesty here takes priority over a
  plausible-looking but unverified proof.
-/

/-- Both files define `depthBound` by the identical expression
`Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1`, so the two functions are definitionally
equal after unfolding. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent018.depthBound n = Agent019.depthBound n := by
  simp only [Agent018.depthBound, Agent019.depthBound]

/-- Both `CPWL` definitions say: `f` is continuous and there is a finite family of
scalar affine functions such that every point has a neighbourhood on which `f`
agrees with one of them. `Agent018` packages each affine piece as a `ScalarAffine`
record; `Agent019` uses a bare function together with an `IsAffineFun` witness. The
two encodings are interchangeable: turn a `ScalarAffine` into its `.eval` function
(trivially affine), or, conversely, use the `IsAffineFun` witness (via choice) to
build a `ScalarAffine` with the same values. The "eventually" neighbourhood
condition and the "there is a `U ∈ nhds x`" phrasing are interchangeable via
`Filter.eventually_iff_exists_mem`. -/
theorem cpwl (n : ℕ) : Agent018.CPWL n = Agent019.CPWL n := by
  ext f
  constructor
  · rintro ⟨hf, m, g, hg⟩
    refine ⟨hf, m, fun j => (g j).eval, fun j => ⟨(g j).a, (g j).b, fun x => rfl⟩, ?_⟩
    intro x
    obtain ⟨i, hi⟩ := hg x
    obtain ⟨U, hU, hUf⟩ := Filter.eventually_iff_exists_mem.mp hi
    exact ⟨i, U, hU, hUf⟩
  · rintro ⟨hf, m, g, hAff, hloc⟩
    refine ⟨hf, m, fun j => ⟨(hAff j).choose, (hAff j).choose_spec.choose⟩, ?_⟩
    intro x
    obtain ⟨j, U, hU, hUf⟩ := hloc x
    refine ⟨j, ?_⟩
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨U, hU, fun y hy => ?_⟩
    rw [hUf y hy]
    exact (hAff j).choose_spec.choose_spec y

/-- SORRY: `Agent018.ReLUn n k` and `Agent019.ReLUn n k` both mean "representable by
a chain of affine maps interleaved with ReLU, with at most `k` ReLU layers and free
choice of intermediate dimensions", but via two different concrete network types
(`ReLUNet`, an inductive type, vs `ReLUNetwork`, a structure carrying an explicit
`widths` function). They are almost certainly equal as sets, but the proof requires
building an explicit translation between the two network representations that
matches every intermediate layer width and transports the layer maps along the
`width_zero`/`width_last` proof fields at each step of the recursion — a delicate,
lengthy dependent-type construction that is not safe to commit to without being
able to compile-check it in this environment. -/
theorem relun (n k : ℕ) : Agent018.ReLUn n k = Agent019.ReLUn n k := by
  sorry

/-- SORRY: once `cpwl` and `depth` are available, the only missing ingredient to
derive `statement` is `relun` specialised at `k = depthBound n` (to rewrite
`Agent018.ReLUn n (depthBound n)` into `Agent019.ReLUn n (depthBound n)`), so this
inherits exactly the gap left open in `relun` above. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent018.CPWL n = Agent018.ReLUn n (Agent018.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent019.CPWL n = Agent019.ReLUn n (Agent019.depthBound n)) := by
  sorry

end Bridge_018_019

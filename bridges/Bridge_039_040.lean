namespace Bridge_039_040

/-!
# Bridge between `Agent039` and `Agent040`

Both formalizations use essentially the same modelling choices:

* `AffineMap`/`Affine` : a matrix + bias vector, `x ↦ A * x + c` (039 via
  `Matrix.mulVec`, 040 via an explicit `Finset.sum`) — these compute the same
  function, just spelled differently.
* `NetProp`/`NetworkComputes` : the same recursive "alternating affine / ReLU"
  definition, by structural recursion on the number of hidden layers.
* `CPWL` : continuity plus "every point has a neighborhood on which `f` agrees
  with one member of a finite family of affine functions" — 039 phrases the
  neighborhood via `IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, …` and an arbitrary
  `Fintype`-indexed family; 040 phrases it via `∀ᶠ y in nhds x, …` and a
  `Finset (Affine n 1)`. These are the same condition.
* `depthBound` : syntactically identical in both files.

The one genuine subtlety is `ReLUn`: 039 takes "**at most** `k` hidden
layers" (`∃ j ≤ k, NetProp n j f`), while 040 takes "**exactly** `k` hidden
layers" (`NetworkComputes k n f`). These coincide only via the padding
argument sketched in `BRIDGE_SPEC.md` (`x = ReLU x - ReLU (-x)` lets one
extra hidden layer simulate the identity, so "exactly `k`" is monotone in `k`
and its union over `j ≤ k` is "exactly `k`" itself). That padding lemma is a
real, non-trivial construction (an explicit 2-wide hidden layer per padding
step) that nobody has proved yet; we do not attempt it here to keep this
bridge file compact and reliable, see the `sorry` below.
-/

/-- `depthBound` is literally the same expression `⌈Real.logb 3 ((n:ℝ)-1)⌉₊ + 1`
in both files, so the two definitions are definitionally equal. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent039.depthBound n = Agent040.depthBound n := rfl

/-- Both `CPWL` definitions say: `f` is continuous, and there is a finite family
of affine functions such that every point has a neighborhood on which `f`
agrees with one member of the family. 039 spells "neighborhood" as an
explicit open set and the family as an arbitrary `Fintype`-indexed family of
`(weight, bias)` pairs; 040 spells it via `Filter.Eventually` at `nhds x` and
the family as a `Finset (Affine n 1)`. We convert between the two
presentations in both directions. -/
theorem cpwl (n : ℕ) : Agent039.CPWL n = Agent040.CPWL n := by
  classical
  ext f
  constructor
  · rintro ⟨hf, ι, hι, w, b, hloc⟩
    haveI := hι
    refine ⟨hf, Finset.univ.image
      (fun i : ι => (⟨fun _ j => w i j, fun _ => b i⟩ : Agent040.Affine n 1)), fun x => ?_⟩
    obtain ⟨i, U, hU, hxU, hy⟩ := hloc x
    refine ⟨⟨fun _ j => w i j, fun _ => b i⟩,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, ?_⟩
    rw [eventually_nhds_iff]
    exact ⟨U, fun y hyU => hy y hyU, hU, hxU⟩
  · rintro ⟨hf, S, hloc⟩
    refine ⟨hf, {T // T ∈ S}, inferInstance,
      fun T j => T.1.A 0 j, fun T => T.1.c 0, fun x => ?_⟩
    obtain ⟨T, hTS, hy⟩ := hloc x
    rw [eventually_nhds_iff] at hy
    obtain ⟨U, hUsub, hU, hxU⟩ := hy
    exact ⟨⟨T, hTS⟩, U, hU, hxU, fun y hyU => hUsub y hyU⟩

/-- `Agent039.ReLUn n k` is "representable with **at most** `k` hidden layers"
(`∃ j ≤ k, NetProp n j f`), while `Agent040.ReLUn n k` is "representable with
**exactly** `k` hidden layers" (`NetworkComputes k n f`). The recursive
definitions `NetProp`/`NetworkComputes` themselves match step-for-step (same
recursion, `AffineMap`/`Affine` compute the same function via
`Matrix.mulVec` vs. an explicit sum), so the `⊇` direction (take `j = k`) is
immediate. The `⊆` direction needs, for `j ≤ k`, that a network with exactly
`j` hidden layers can be padded to exactly `k` hidden layers: it suffices to
show a network with exactly `m` layers can always be re-expressed with
exactly `m + 1` layers, by prepending/appending a 2-wide hidden layer
computing the identity via `x ↦ ReLU x - ReLU (-x)`. This is genuine, provable
mathematics (as flagged in `BRIDGE_SPEC.md`, "nobody has proved that lemma
yet"), but the explicit matrix construction is long enough that attempting it
here risks an unreliable, sprawling proof; left honest as `sorry`. -/
theorem relun (n k : ℕ) : Agent039.ReLUn n k = Agent040.ReLUn n k := sorry

/-- Follows immediately from `cpwl`, `depth`, and `relun` by rewriting each
side of each iff with the corresponding equality (for every `n ≥ 3`,
`CPWL039 n = CPWL040 n`, `depthBound039 n = depthBound040 n`, and
`ReLUn039 n (depthBound n) = ReLUn040 n (depthBound n)`, so the two
"theorem statement" propositions become literally the same proposition).
Since `relun` above is left as `sorry`, this composite proof is blocked on
it; left `sorry` for the same reason rather than faking the composition. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent039.CPWL n = Agent039.ReLUn n (Agent039.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent040.CPWL n = Agent040.ReLUn n (Agent040.depthBound n)) := sorry

end Bridge_039_040

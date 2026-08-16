# Formalizing Theorem 2 of *Better Neural Network Expressivity: Subdividing the Simplex*

arXiv:2505.14338 Bakaev, Brunck, Hertrich, Stade, Yehudayoff.

> **Theorem 2.** *For n ≥ 3, we have* CPWL<sub>n</sub> = ReLU<sub>n, ⌈log₃(n−1)⌉+1</sub>.

100 agents each wrote an independent Lean 4 + Mathlib formalization of the statement
(proof left as `sorry`), defining `relu`, componentwise ReLU, affine maps, the
alternating-composition network semantics, `ReLUn n k`, `CPWL n` and the depth bound from
scratch. No shared definitions, and no agent saw another agent's file.

## Exact matches the only pairs that are literally the same statement

| agents | shared reading |
|---|---|
| `004`, `018` | local agreement (nhds / eventually), at most k |
| `010`, `024` | local agreement (nhds / eventually), at most k |
| `016`, `070` | local agreement (nhds / eventually), at most k |
| `035`, `096` | local agreement (nhds / eventually), at most k |
| `044`, `097` | local agreement (nhds / eventually), at most k |
| `045`, `048` | local agreement (nhds / eventually), at most k |
| `059`, `062` | polyhedral / covering subdivision, at most k |

## Layout

| | what it is |
|---|---|
| [`formalizations/`](formalizations/) | the 100 independent formalizations, `Thm2_001.lean` … `Thm2_100.lean` |
| [`star/`](star/README.md) | the comparison. Every file is proved equal to, or refuted against, one [reference](star/Reference.lean) — so verdicts **compose** into a partition instead of a chain |
| [`proptest/`](proptest/README.md) | the cheap check. `depthBound` is the one ingredient with observable outputs, so it can be property-tested by evaluation — no agents, no proof search |

## Results

| experiment | approach | result |
|---|---|---|
| [`star/`](star/README.md) | prove-or-refute **all 97** elaborating files against one reference | **28 provably the same theorem, 64 provably different, 5 open.** `depth` 97/97. **50 files carry a sorry-free proof that their own Theorem 2 is false** |
| [`proptest/`](proptest/README.md) | evaluate `depthBound` at 10 sample points against an independently computed value | **100/100** at every point, across three different spellings of the definition |

The two agree on `depthBound` by different methods — one by evaluation, one by
proof — which is the only overlap between them.

## Building

```sh
lake exe cache get     # restores the revisions pinned in lake-manifest.json
lake env lean -DmaxErrors=1000000 star/StarAll.lean > star/star.log 2>&1
```

`-DmaxErrors` matters: the in-file `set_option maxErrors` is not honoured, and
the default cap of 100 halts the run before the reporting command executes.
The `leanOptions` in `lakefile.toml` are mirrored from the project the
experiments were originally compiled against — `relaxedAutoImplicit = false` in
particular affects elaboration, so changing it can change which files compile.

## Verdict

The 100 formalizations are **not** all the same theorem, and this is machine-proved in
both directions, not inferred.

* **28** are provably the same theorem as the reference — and therefore as each other,
  transitively, with no pairwise comparison ever run.
* **64** are provably a *different* theorem.
* **50 of those 64 carry a sorry-free proof that their own Theorem 2 is false** — a
  verdict that depends on no unproved theorem at all.
* **5** are genuinely open (below).
* **3** (`020`, `027`, `084`) do not elaborate and were excluded.

The depth bound `⌈log₃(n−1)⌉+1` is unanimous: 97/97 proved identical to the reference,
across three different spellings (`Nat.clog`, `⌈Real.logb⌉₊`, and both cast conventions).

The fault line is `CPWL`. Files defining it by *neighbourhood agreement* state something
strictly stronger than CPWL: on connected `ℝⁿ` that condition forces **global
affineness**, so their Theorem 2 is false, witness `x ↦ max 0 (x 0)`. Crucially this
family is invisible to grep — it appears in at least four spellings (`∀ᶠ y in nhds x`,
`f =ᶠ[nhds x] g i`, `∃ ε > 0, ∀ y, dist y x < ε → …`, `∃ U, IsOpen U ∧ x ∈ U ∧ …`), and
**eight files' own doc comments claim "polyhedral subdivision" while the definition
underneath is neighbourhood agreement**. Only reading the definitions found them.

The 5 open files split into two real mathematical gaps, not proof-search failures:
`054`, `068`, `083`, `095` cover `ℝⁿ` by *closed convex* sets, and `041` uses pointwise
selection (`∀ x, ∃ j, f x = g j x`). Both directions' easy inclusion is proved; the
converse needs a hyperplane-arrangement refinement that is not in Mathlib.

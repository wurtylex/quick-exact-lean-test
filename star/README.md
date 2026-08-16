# Star comparison — 20 formalizations against one reference

Each of the sampled formalizations is compared against
[`Reference.lean`](Reference.lean) rather than against its neighbour.  The
verdicts therefore **compose**: two files proved equal to `Ref` are equal to
each other, and a proved-equal file and a refuted file are provably different.
Nothing depends on anything else, so a failed comparison costs one cell rather
than disconnecting a chain.

Verdicts are read from each declaration's axiom set, so a `sorry` — including
one laundered through another `sorry`-ed theorem — cannot be reported as a
proof.  `ERROR` means the declaration did not elaborate.

## Verdicts

| file | family | `cpwl` | `relun` | `depth` | `statement` | own thm false | errors |
|---|---|---|---|---|---|---|---:|
| `001` | polyhedral subdivision | PROVED | SORRY | PROVED | SORRY | MISSING |  |
| `002` | pointwise affine selection | REFUTED | SORRY | PROVED | SORRY | MISSING |  |
| `003` | local agreement (nhds / forall-eventually) | REFUTED | PROVED | PROVED | SORRY_NE | PROVED |  |
| `004` | local agreement (nhds / forall-eventually) | REFUTED | PROVED | PROVED | SORRY | MISSING |  |
| `005` | pointwise affine selection | REFUTED | PROVED | PROVED | SORRY_NE | PROVED |  |
| `006` | local agreement (nhds / forall-eventually) | REFUTED | PROVED | PROVED | SORRY_NE | PROVED |  |
| `007` | pointwise affine selection | REFUTED | SORRY | PROVED | SORRY | PROVED |  |
| `008` | polyhedral subdivision | PROVED | PROVED | PROVED | PROVED | MISSING |  |
| `009` | polyhedral + local | REFUTED | PROVED | PROVED | SORRY | PROVED |  |
| `010` | local agreement (nhds / forall-eventually) | REFUTED | PROVED | PROVED | SORRY | PROVED |  |
| `011` | polyhedral + local | REFUTED | PROVED | PROVED | SORRY | PROVED |  |
| `012` | local agreement (nhds / forall-eventually) | REFUTED | PROVED | PROVED | SORRY_NE | PROVED |  |
| `013` | pointwise affine selection | REFUTED | PROVED | PROVED | SORRY | PROVED |  |
| `014` | polyhedral subdivision | PROVED | SORRY | PROVED | SORRY | MISSING |  |
| `015` | polyhedral subdivision | REFUTED | SORRY | PROVED | SORRY_NE | PROVED |  |
| `016` | local agreement (nhds / forall-eventually) | REFUTED | PROVED | PROVED | SORRY | MISSING |  |
| `017` | local agreement (nhds / forall-eventually) | REFUTED | PROVED | PROVED | SORRY_NE | PROVED |  |
| `018` | local agreement (nhds / forall-eventually) | REFUTED | PROVED | PROVED | SORRY_NE | PROVED |  |
| `019` | local agreement (nhds / forall-eventually) | REFUTED | SORRY | PROVED | SORRY_NE | PROVED |  |
| `021` | polyhedral subdivision | PROVED | PROVED | PROVED | PROVED | MISSING |  |
| `022` | local agreement (nhds / forall-eventually) | REFUTED | PROVED | PROVED | SORRY | PROVED |  |
| `023` | pointwise affine selection | REFUTED | PROVED | PROVED | SORRY_NE | PROVED |  |
| `024` | local agreement (nhds / forall-eventually) | REFUTED | PROVED | PROVED | SORRY_NE | PROVED |  |
| `025` | local agreement (nhds / forall-eventually) | REFUTED | SORRY | PROVED | SORRY | PROVED |  |
| `026` | polyhedral subdivision | PROVED | PROVED | PROVED | PROVED | MISSING |  |
| `028` | local agreement (nhds / forall-eventually) | REFUTED | PROVED | PROVED | SORRY_NE | PROVED |  |
| `029` | polyhedral subdivision | PROVED | SORRY | PROVED | SORRY | MISSING |  |
| `030` | polyhedral subdivision | PROVED | PROVED | PROVED | PROVED | MISSING |  |
| `031` | pointwise affine selection | REFUTED | PROVED | PROVED | SORRY | MISSING |  |
| `032` | polyhedral subdivision | PROVED | PROVED | PROVED | PROVED | MISSING |  |
| `033` | pointwise affine selection | REFUTED | PROVED | PROVED | SORRY | PROVED |  |
| `034` | polyhedral subdivision | PROVED | PROVED | PROVED | PROVED | MISSING |  |
| `035` | local agreement (nhds / forall-eventually) | REFUTED | PROVED | PROVED | SORRY | PROVED |  |
| `036` | local agreement (nhds / forall-eventually) | REFUTED | PROVED | PROVED | SORRY | MISSING |  |
| `037` | polyhedral subdivision | PROVED | PROVED | PROVED | PROVED | MISSING |  |
| `038` | pointwise affine selection | REFUTED | SORRY | PROVED | SORRY | PROVED |  |
| `039` | pointwise affine selection | REFUTED | PROVED | PROVED | SORRY | PROVED |  |
| `040` | local agreement (nhds / forall-eventually) | REFUTED | SORRY | PROVED | SORRY | PROVED |  |
| `041` | pointwise affine selection | SORRY | SORRY | PROVED | SORRY | MISSING |  |
| `042` | polyhedral subdivision | PROVED | SORRY | PROVED | SORRY | MISSING |  |
| `043` | pointwise affine selection | REFUTED | PROVED | PROVED | SORRY_NE | PROVED |  |
| `044` | local agreement (nhds / forall-eventually) | REFUTED | PROVED | PROVED | SORRY_NE | PROVED |  |
| `045` | local agreement (nhds / forall-eventually) | REFUTED | PROVED | PROVED | SORRY | MISSING |  |
| `046` | polyhedral subdivision | PROVED | PROVED | PROVED | PROVED | MISSING |  |
| `047` | local agreement (nhds / forall-eventually) | REFUTED | SORRY | PROVED | SORRY | PROVED |  |
| `048` | polyhedral + local | REFUTED | PROVED | PROVED | SORRY_NE | PROVED |  |
| `049` | polyhedral subdivision | PROVED | PROVED | PROVED | PROVED | MISSING |  |
| `050` | polyhedral subdivision | PROVED | PROVED | PROVED | PROVED | MISSING |  |
| `051` | pointwise affine selection | REFUTED | SORRY | PROVED | SORRY_NE | PROVED |  |
| `052` | polyhedral subdivision | PROVED | SORRY | PROVED | SORRY | MISSING |  |
| `053` | polyhedral subdivision | REFUTED | PROVED | PROVED | SORRY_NE | PROVED |  |
| `054` | polyhedral subdivision | SORRY | PROVED | PROVED | SORRY | MISSING |  |
| `055` | local agreement (nhds / forall-eventually) | REFUTED | PROVED | PROVED | SORRY_NE | PROVED |  |
| `056` | polyhedral + local | REFUTED | PROVED | PROVED | SORRY | PROVED |  |
| `057` | polyhedral subdivision | PROVED | PROVED | PROVED | PROVED | MISSING |  |
| `058` | local agreement (nhds / forall-eventually) | REFUTED | SORRY | PROVED | SORRY | MISSING |  |
| `059` | polyhedral subdivision | PROVED | PROVED | PROVED | PROVED | MISSING |  |
| `060` | pointwise affine selection | REFUTED | PROVED | PROVED | SORRY | MISSING |  |
| `061` | polyhedral + local | REFUTED | PROVED | PROVED | SORRY | PROVED |  |
| `062` | polyhedral subdivision | PROVED | PROVED | PROVED | PROVED | MISSING |  |
| `063` | polyhedral subdivision | PROVED | PROVED | PROVED | PROVED | MISSING |  |
| `064` | pointwise affine selection | REFUTED | SORRY | PROVED | SORRY_NE | PROVED |  |
| `065` | local agreement (nhds / forall-eventually) | REFUTED | SORRY | PROVED | SORRY_NE | PROVED |  |
| `066` | local agreement (nhds / forall-eventually) | REFUTED | PROVED | PROVED | SORRY | PROVED |  |
| `067` | local agreement (nhds / forall-eventually) | REFUTED | SORRY | PROVED | SORRY | PROVED |  |
| `068` | polyhedral subdivision | SORRY | SORRY | PROVED | SORRY | MISSING |  |
| `069` | local agreement (nhds / forall-eventually) | REFUTED | PROVED | PROVED | SORRY | MISSING |  |
| `070` | polyhedral + local | REFUTED | PROVED | PROVED | SORRY | MISSING |  |
| `071` | local agreement (nhds / forall-eventually) | REFUTED | SORRY | PROVED | SORRY | SORRY | 2 |
| `072` | polyhedral subdivision | PROVED | PROVED | PROVED | PROVED | MISSING |  |
| `073` | local agreement (nhds / forall-eventually) | REFUTED | SORRY | PROVED | SORRY_NE | PROVED |  |
| `074` | polyhedral subdivision | PROVED | PROVED | PROVED | PROVED | MISSING |  |
| `075` | local agreement (nhds / forall-eventually) | REFUTED | SORRY | PROVED | SORRY_NE | SORRY | 1 |
| `076` | polyhedral + local | REFUTED | SORRY | PROVED | SORRY | PROVED | 1 |
| `077` | pointwise affine selection | REFUTED | PROVED | PROVED | SORRY_NE | PROVED |  |
| `078` | local agreement (nhds / forall-eventually) | REFUTED | SORRY | PROVED | SORRY | PROVED |  |
| `079` | polyhedral subdivision | REFUTED | SORRY | PROVED | SORRY_NE | PROVED | 1 |
| `080` | local agreement (nhds / forall-eventually) | REFUTED | SORRY | PROVED | SORRY | PROVED |  |
| `081` | polyhedral subdivision | PROVED | PROVED | PROVED | PROVED | MISSING |  |
| `082` | local agreement (nhds / forall-eventually) | REFUTED | PROVED | PROVED | SORRY | MISSING |  |
| `083` | polyhedral subdivision | SORRY | PROVED | PROVED | SORRY | MISSING |  |
| `085` | local agreement (nhds / forall-eventually) | REFUTED | SORRY | PROVED | SORRY | PROVED |  |
| `086` | polyhedral subdivision | PROVED | PROVED | PROVED | PROVED | MISSING |  |
| `087` | polyhedral + local | REFUTED | SORRY | PROVED | SORRY | PROVED |  |
| `088` | polyhedral subdivision | PROVED | PROVED | PROVED | PROVED | MISSING |  |
| `089` | polyhedral + local | REFUTED | PROVED | PROVED | SORRY_NE | PROVED |  |
| `090` | polyhedral subdivision | PROVED | PROVED | PROVED | PROVED | MISSING |  |
| `091` | polyhedral subdivision | PROVED | PROVED | PROVED | PROVED | MISSING |  |
| `092` | local agreement (nhds / forall-eventually) | REFUTED | SORRY | PROVED | SORRY_NE | PROVED |  |
| `093` | polyhedral subdivision | PROVED | SORRY | PROVED | SORRY | MISSING | 12 |
| `094` | polyhedral + local | REFUTED | PROVED | PROVED | SORRY | PROVED |  |
| `095` | polyhedral subdivision | SORRY | PROVED | PROVED | SORRY | MISSING | 1 |
| `096` | local agreement (nhds / forall-eventually) | REFUTED | PROVED | PROVED | SORRY_NE | PROVED |  |
| `097` | local agreement (nhds / forall-eventually) | REFUTED | PROVED | PROVED | SORRY_NE | PROVED |  |
| `098` | polyhedral subdivision | PROVED | PROVED | PROVED | PROVED | MISSING |  |
| `099` | local agreement (nhds / forall-eventually) | REFUTED | PROVED | PROVED | SORRY | PROVED |  |
| `100` | polyhedral + local | REFUTED | SORRY | PROVED | SORRY | MISSING |  |

| obligation | PROVED | REFUTED | SORRY | ERROR / other |
|---|---:|---:|---:|---:|
| `cpwl` | 28 | 64 | 5 | 0 |
| `relun` | 65 | 0 | 32 | 0 |
| `depth` | 97 | 0 | 0 | 0 |
| `statement` | 22 | 0 | 48 | 27 |
| `ownfalse` | 50 | 0 | 2 | 45 |

## The partition

Classified by `cpwl`, the obligation that carries the mathematical content.

**Same theorem as the reference — 28 of 97**

`001`, `008`, `014`, `021`, `026`, `029`, `030`, `032`, `034`, `037`, `042`, `046`, `049`, `050`, `052`, `057`, `059`, `062`, `063`, `072`, `074`, `081`, `086`, `088`, `090`, `091`, `093`, `098`

These 28 are equal to each other too, transitively, without any
pairwise comparison having been run.

**Provably a different theorem — 64 of 97**

`002`, `003`, `004`, `005`, `006`, `007`, `009`, `010`, `011`, `012`, `013`, `015`, `016`, `017`, `018`, `019`, `022`, `023`, `024`, `025`, `028`, `031`, `033`, `035`, `036`, `038`, `039`, `040`, `043`, `044`, `045`, `047`, `048`, `051`, `053`, `055`, `056`, `058`, `060`, `061`, `064`, `065`, `066`, `067`, `069`, `070`, `071`, `073`, `075`, `076`, `077`, `078`, `079`, `080`, `082`, `085`, `087`, `089`, `092`, `094`, `096`, `097`, `099`, `100`

by family: 36× local agreement (nhds / forall-eventually), 14× pointwise affine selection, 11× polyhedral + local, 3× polyhedral subdivision

**Undecided — 5 of 97**

`041`, `054`, `068`, `083`, `095`

An honest `sorry` or a failed proof, not a verdict: these are neither
known-equal nor known-different.

So at least **two** distinct theorems are present among the 97
sampled files, and the split is machine-proved in both directions.

## Files proved to state a *false* theorem

Stronger than "differs from the reference": these carry a direct proof
that their own Theorem 2 is false, with no dependence on the unproved
`Ref.theorem2`.

`003`, `005`, `006`, `007`, `009`, `010`, `011`, `012`, `013`, `015`, `017`, `018`, `019`, `022`, `023`, `024`, `025`, `028`, `033`, `035`, `038`, `039`, `040`, `043`, `044`, `047`, `048`, `051`, `053`, `055`, `056`, `061`, `064`, `065`, `066`, `067`, `073`, `076`, `077`, `078`, `079`, `080`, `085`, `087`, `089`, `092`, `094`, `096`, `097`, `099`

## Side results

* `depthBound`: 97/97 proved identical to the reference's
  `⌈log₃(n−1)⌉+1`, consistent with the earlier property test finding all 100
  agree at every sample point.
* `relun`: 65/97 proved, 0 refuted.  The gap
  is the *exactly k* vs *at most k* reading of hidden-layer count, which needs
  the padding identity `x = relu x − relu (−x)` to close.

## Comparisons that failed to elaborate — 6 / 97

* **`071`** — The argument
* **`075`** — Tactic `simp` failed with a nested error:
* **`076`** — unsolved goals
* **`079`** — unsolved goals
* **`093`** — 3 provided, but 1 expected
* **`095`** — linarith failed to find a contradiction


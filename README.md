# Formalizing Theorem 2 of *Better Neural Network Expressivity: Subdividing the Simplex*

arXiv:2505.14338 Bakaev, Brunck, Hertrich, Stade, Yehudayoff.

> **Theorem 2.** *For n ≥ 3, we have* CPWL<sub>n</sub> = ReLU<sub>n, ⌈log₃(n−1)⌉+1</sub>.

100 agents each wrote an **independent** Lean 4 + Mathlib formalization of the *statement*
(proof left as `sorry`), defining `relu`, componentwise ReLU, affine maps, the
alternating-composition network semantics, `ReLUn n k`, `CPWL n` and the depth bound from
scratch. No shared definitions, and no agent saw another agent's file.

---

## 1. Type check

### ❌ Faulty (3)

These do not elaborate as written:

* **`020`** — `failed to synthesize instance HAdd (Fin b → ℝ) (Vec b) ?m` — mixes its `Vec b` abbreviation with the raw pi type in the affine-map body.
* **`027`** — `elaboration function for Mathlib.Tactic.subscriptTerm has not been implemented` — wrote `*ᵥ` in a position where the subscript notation does not elaborate.
* **`084`** — `failed to synthesize instance Membership ?m (Polyhedron n)` — uses `x ∈ P` on its own `Polyhedron` structure without a `Membership` instance.

### ⚠️ Cosmetically broken (25)

Every one of these fails only with *“failed to compile definition, consider marking it as
`noncomputable`, because it depends on `Real.instFloorRing`”* on their `depthBound`
definition. Adding the `noncomputable` keyword fixes them; the statement of `theorem2` is
unaffected and elaborates correctly, so they are counted as usable below.

`005`, `010`, `011`, `015`, `024`, `030`, `037`, `040`, `041`, `043`, `046`, `047`, `055`, `062`, `069`, `071`, `078`, `081`, `083`, `087`, `088`, `089`, `092`, `094`, `098`

### ✅ Clean (72)

Everything else: `001`, `002`, `003`, `004`, `006`, `007`, `008`, `009`, `012`, `013`, `014`, `016`, `017`, `018`, `019`, `021`, `022`, `023`, `025`, `026`, `028`, `029`, `031`, `032`, `033`, `034`, `035`, `036`, `038`, `039`, `042`, `044`, `045`, `048`, `049`, `050`, `051`, `052`, `053`, `054`, `056`, `057`, `058`, `059`, `060`, `061`, `063`, `064`, `065`, `066`, `067`, `068`, `070`, `072`, `073`, `074`, `075`, `076`, `077`, `079`, `080`, `082`, `085`, `086`, `090`, `091`, `093`, `095`, `096`, `097`, `099`, `100`

---

## 2. Which ones agree?

Method: for each agent, delta-expand every constant defined in that agent's own namespace,
erase binder names, and render the resulting statement canonically. Two files are reported as
*the same* only if their fully-unfolded statements are structurally identical modulo naming.

**90 distinct statements among the 97 usable files.**

### Exact matches — the only pairs that are literally the same statement

| agents | shared reading |
|---|---|
| `004`, `018` | local agreement (nhds / eventually), at most k |
| `010`, `024` | local agreement (nhds / eventually), at most k |
| `016`, `070` | local agreement (nhds / eventually), at most k |
| `035`, `096` | local agreement (nhds / eventually), at most k |
| `044`, `097` | local agreement (nhds / eventually), at most k |
| `045`, `048` | local agreement (nhds / eventually), at most k |
| `059`, `062` | polyhedral / covering subdivision, at most k |

All other 83 files are structurally unique.

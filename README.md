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

# Comparison

Every formalization is compared against an agent written [`star/Reference.lean`](star/Reference.lean), not against each other.

The reference reads Theorem 2 as

```lean
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) : CPWL n = ReLUn n (depthBound n) := sorry

def IsCPWL (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  Continuous f ∧
    ∃ (m : ℕ) (P : Fin m → Set (Fin n → ℝ)) (g : Fin m → ((Fin n → ℝ) → ℝ)),
      (∀ i, IsPolyhedron n (P i)) ∧ (∀ i, IsAffine (g i)) ∧
        (⋃ i, P i) = Set.univ ∧ ∀ i, ∀ x ∈ P i, f x = g i x

def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) := {f | ∃ j ≤ k, ComputedBy n j f}

noncomputable def depthBound (n : ℕ) : ℕ := ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1
```

## Agree: 28 of 97

Proved equal to the reference, hence to each other.

`001`, `008`, `014`, `021`, `026`, `029`, `030`, `032`, `034`, `037`, `042`, `046`, `049`, `050`
`052`, `057`, `059`, `062`, `063`, `072`, `074`, `081`, `086`, `088`, `090`, `091`, `093`, `098`

## Disagree: 64 of 97

Proved to state a different theorem. All carry a sorry-free refutation.

`002`, `003`, `004`, `005`, `006`, `007`, `009`, `010`, `011`, `012`, `013`, `015`, `016`, `017`
`018`, `019`, `022`, `023`, `024`, `025`, `028`, `031`, `033`, `035`, `036`, `038`, `039`, `040`
`043`, `044`, `045`, `047`, `048`, `051`, `053`, `055`, `056`, `058`, `060`, `061`, `064`, `065`
`066`, `067`, `069`, `070`, `071`, `073`, `075`, `076`, `077`, `078`, `079`, `080`, `082`, `085`
`087`, `089`, `092`, `094`, `096`, `097`, `099`, `100`

## Open: 5 of 97

`041`, `054`, `068`, `083`, `095`

## Excluded: 3 of 100

`020`, `027`, `084` do not elaborate, so no comparison is meaningful.

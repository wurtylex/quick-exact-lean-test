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


# Task: Formalize Theorem 2 of arXiv:2505.14338 in Lean 4 + Mathlib

You are one of 100 independent agents doing this task. **Do not read any other agent's
file.** Do not read any other file in the `formalizations/` directory except this SPEC.
Produce your own independent formalization.

## Source material (verbatim from the paper)

Paper: *Better Neural Network Expressivity: Subdividing the Simplex* — Egor Bakaev,
Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff (arXiv:2505.14338v3).

From Section 1 (Introduction):

> Neural networks with rectified linear unit (ReLU) activations are among the most common
> models in modern machine learning. A ReLU *network* with *depth* k + 1 is defined via
> k + 1 affine transformations T^(i) : R^{n_{i-1}} → R^{n_i} for i = 1, ..., k + 1. It
> *computes* the function defined as alternating composition
>
>     T^(k+1) ∘ ReLU ∘ T^(k) ∘ ... ∘ ReLU ∘ T^(2) ∘ ReLU ∘ T^(1)
>
> of the affine transformations with component-wise applications of the ReLU function
> ReLU(x) = max{0, x}. We say that the network has k *hidden layers*. Alternatively, ReLU
> networks can be defined as directed acyclic graphs of neurons, each of which computes a
> function x ↦ ReLU(b + Σ_i a_i x_i).
>
> Functions represented by ReLU networks are *continuous and piecewise linear* (CPWL), and
> every such function on R^n can be computed by a ReLU network. [...]
>
> Denote by CPWL_n the space of CPWL functions f : R^n → R and by ReLU_{n,k} the subset of
> CPWL_n representable with k hidden layers. An important CPWL function for understanding
> neural network depth is the MAX_n function defined by
>
>     MAX_n(x) = MAX_n(x_1, ..., x_n) = max{x_1, ..., x_n}.

From Section 1.1 (Our Contribution):

> **Theorem 1.** *For n ≥ 1, we have* MAX_{3^n + 2} ∈ ReLU_{n+1}.
>
> By the discussion above, this implies that every CPWL function defined on R^n can be
> represented with ⌈log_3(n − 1)⌉ + 1 hidden layers.
>
> **Theorem 2.** *For n ≥ 3, we have* CPWL_n = ReLU_{n, ⌈log_3(n−1)⌉ + 1}.

(Note: n_i in the network definition are the layer widths; n_0 = n is the input dimension
and the output dimension n_{k+1} = 1 since these are real-valued functions. Also
"depth k+1" = "k hidden layers". `log_3` is the real logarithm to base 3 and `⌈·⌉` is the
ceiling; `n − 1` is a natural number ≥ 2 here.)

## What to write

Write **exactly one** Lean 4 file at:

    /Users/panda/Desktop/Lean/quick-test/formalizations/Thm2_NNN.lean

where `NNN` is your assigned three-digit agent index (given in your prompt, zero-padded).

Structure of the file:

```lean
import Mathlib

namespace AgentNNN

/- your definitions here -/

theorem theorem2 ... := sorry

end AgentNNN
```

Hard requirements:

1. `import Mathlib` on the first line. Nothing else imported.
2. Everything wrapped in `namespace AgentNNN ... end AgentNNN` matching your index
   (e.g. agent 007 uses `namespace Agent007`).
3. You **must actually define** every notion the statement depends on. At minimum:
   - `relu` (the function `max 0 ·` on `ℝ`), and its componentwise application to vectors;
   - what an affine transformation `ℝ^a → ℝ^b` is (you may use Mathlib's affine maps, or
     define it concretely as `x ↦ A * x + b` — your choice, but be explicit);
   - what it means for a function `ℝ^n → ℝ` to be **computed / represented by a ReLU
     network with k hidden layers** — i.e. the alternating composition above;
   - `ReLUn n k`, the set of functions `ℝ^n → ℝ` representable with `k` hidden layers;
   - `CPWL n`, the set of continuous piecewise linear functions `ℝ^n → ℝ`. Give a real
     mathematical definition (continuity + a genuine piecewise-linearity condition, e.g.
     a finite polyhedral subdivision on each piece of which `f` is affine, or a finite
     family of affine functions that `f` locally agrees with). Do **not** define CPWL as
     "representable by some ReLU network" and do **not** define it via a max-of-affine
     normal form — that would make the theorem trivially true or assume the result.
   - the depth bound `⌈log_3 (n − 1)⌉ + 1` — define it explicitly (real `Real.logb 3`
     with `Nat.ceil`, or `Nat.clog 3`, your choice — but if you use `Nat.clog`, make sure
     it really equals the intended ceiling of the real log).
   - Optionally also define `MAX n` if you want it, but it is not required by Theorem 2.
4. The final theorem must be named `theorem2` and must be the statement of Theorem 2:
   for all `n ≥ 3`, `CPWL n = ReLUn n (⌈log_3 (n-1)⌉ + 1)` (as sets/subsets of
   `(ℝ^n → ℝ)`, or however your encoding expresses set equality).
5. The proof is `sorry`. **Do not attempt to prove it.** Only the statement matters.
6. No `axiom`, no `@[simp]` hacks, no `Classical.choice`-based cheats that change meaning.
   Auxiliary `def`s and `abbrev`s are fine. Extra lemmas are NOT wanted — one theorem only.
7. Choose your own encoding of `ℝ^n`: `Fin n → ℝ`, `EuclideanSpace ℝ (Fin n)`, or
   `Matrix (Fin n) ... ` — whatever you think is most faithful. This is a real modelling
   choice and different agents are expected to choose differently.

## Important

- Aim for the most **faithful** formalization you can, not the easiest one.
- Be careful about the off-by-one between "depth" and "hidden layers".
- Be careful whether `ReLU_{n,k}` should be *exactly* `k` hidden layers or *at most* `k`.
  Think about which reading makes Theorem 2 true and state your choice.
- **Do not run `lake build` or `lean`** — a central process will type-check all 100 files
  afterwards. Just write the file.
- Do not create any other files.
- When done, reply with a 3-5 line summary of the key modelling choices you made
  (vector encoding, CPWL definition style, exactly-k vs at-most-k, log encoding).

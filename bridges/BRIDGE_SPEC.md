# Task: bridge two independent formalizations of Theorem 2 (arXiv:2505.14338)

You are one of 99 agents. Each of us owns **one consecutive link** in the chain
`001 → 002 → 003 → … → 100`. Your link is given in your prompt as `<I> → <J>`.

100 agents previously wrote independent Lean 4 + Mathlib formalizations of

> **Theorem 2.** For n ≥ 3, `CPWL_n = ReLU_{n, ⌈log₃(n−1)⌉+1}`.

Each lives in its own namespace `Agent<NNN>` and defines, among other things,
`CPWL : ℕ → Set ((Fin n → ℝ) → ℝ)`, `ReLUn : ℕ → ℕ → Set (…)`, and
`depthBound : ℕ → ℕ`. All 100 chose different encodings.

Your job: decide, **with a Lean proof**, whether `Agent<I>` and `Agent<J>` say the
same thing — and prove it, or prove that they do not.

## Read these two files first

    /Users/panda/Desktop/Lean/quick-test/formalizations/Thm2_<I>.lean
    /Users/panda/Desktop/Lean/quick-test/formalizations/Thm2_<J>.lean

Read **only** those two plus this spec. Do not read other agents' formalizations
and do not read other agents' bridge files.

## Write exactly one file

    /Users/panda/Desktop/Lean/quick-test/harness/bridges/Bridge_<I>_<J>.lean

It is **spliced into a larger file** in which `import Mathlib` has already
happened and both `Agent<I>` and `Agent<J>` are already fully elaborated and in
scope. Therefore:

* **No `import` lines.** They will be stripped anyway.
* Everything you write must sit inside `namespace Bridge_<I>_<J> … end Bridge_<I>_<J>`.
* Refer to the two formalizations by their full names, e.g. `Agent<I>.CPWL`.
* Never edit `Thm2_<I>.lean` / `Thm2_<J>.lean`. Treat them as fixed.

## The four obligations

Use **exactly** these declaration names — a machine checks for them and inspects
their axioms, so self-reported claims are worthless and misnaming loses you credit.

```lean
namespace Bridge_<I>_<J>

theorem cpwl  (n : ℕ)        : Agent<I>.CPWL n = Agent<J>.CPWL n := …
theorem relun (n k : ℕ)      : Agent<I>.ReLUn n k = Agent<J>.ReLUn n k := …
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent<I>.depthBound n = Agent<J>.depthBound n := …
theorem statement :
    (∀ n, 3 ≤ n → Agent<I>.CPWL n = Agent<I>.ReLUn n (Agent<I>.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent<J>.CPWL n = Agent<J>.ReLUn n (Agent<J>.depthBound n)) := …

end Bridge_<I>_<J>
```

For each of the four, do **one** of these three things:

1. **Prove it.** Best outcome.
2. **Refute it.** If the two definitions genuinely differ, *delete that theorem* and
   instead prove the negation, named with an `_ne` suffix and exactly this shape:
   ```lean
   theorem cpwl_ne      : ∃ n, Agent<I>.CPWL n ≠ Agent<J>.CPWL n := …
   theorem relun_ne     : ∃ n k, Agent<I>.ReLUn n k ≠ Agent<J>.ReLUn n k := …
   theorem depth_ne     : ∃ n, 3 ≤ n ∧ Agent<I>.depthBound n ≠ Agent<J>.depthBound n := …
   theorem statement_ne : ¬ ((∀ n, 3 ≤ n → Agent<I>.CPWL n = Agent<I>.ReLUn n (Agent<I>.depthBound n)) ↔
                             (∀ n, 3 ≤ n → Agent<J>.CPWL n = Agent<J>.ReLUn n (Agent<J>.depthBound n))) := …
   ```
   A refutation is a *real result*, as valuable as a proof. Do not fake one.
3. **Leave it `sorry`.** Only if you cannot do either. Put a comment immediately
   above saying precisely what is missing and why (one or two sentences).

Auxiliary lemmas are welcome — name them anything **other** than the eight names
above, and keep them inside your namespace.

## What you will probably find

These are the axes on which the 100 formalizations differ. Expect your two files to
differ on one or more of them:

* **`depthBound`** — most wrote `⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1`; some wrote
  `⌈Real.logb 3 (↑(n - 1) : ℝ)⌉₊ + 1` (truncated ℕ-subtraction, then cast); one used
  `Nat.clog 3 (n - 1) + 1`. The first two agree for `n ≥ 3` — `Nat.cast_sub` and
  friends should close it. Whether `Nat.clog` matches is a genuine question; check
  `Nat.clog` against `Nat.ceil (Real.logb …)` carefully rather than assuming.
* **`ReLUn`** — "at most `k` hidden layers" (`∃ k' ≤ k, …`) vs. "exactly `k`". These
  coincide only via a padding argument (`x = ReLU x - ReLU (-x)` lets a layer act as
  the identity). Nobody has proved that lemma; if you need it, prove it.
* **`CPWL`** — three families:
  (a) *polyhedral subdivision*: a finite cover of `ℝⁿ` by polyhedra with `f` affine
      on each;
  (b) *local agreement*: `∀ x, ∃ i, ∀ᶠ y in nhds x, f y = g i y` (or the same with a
      metric ball);
  (c) other.
  **Look hard at (b).** It says `f` is *locally affine at every point*. Think about
  what that forces on a connected domain, and about whether `x ↦ max 0 (x 0)`
  satisfies it near `0`. If your two files are on different sides of this, the honest
  answer is very likely a refutation, and it is likely much easier to prove than the
  corresponding equality would be. Work it out yourself — do not take this paragraph
  as established.

## Rules

* **Do not run `lake`, `lean`, or any build.** All 99 bridges are checked together in
  a single Lean process afterwards; running your own build wastes ~5 minutes per
  invocation and will not be needed. Write careful Lean and rely on the batch check.
* Because you cannot compile, prefer robust tactics (`ext`, `constructor`, `intro`,
  `simp only [...]`, `exact`, `rcases`, `refine`) and explicit term proofs over long
  fragile `simp`/`aesop` chains. `Set.ext` + `Iff` reasoning is usually the way in.
* No `axiom` declarations, no `native_decide`, no `@[implemented_by]`, no editing the
  agent files, no other files.
* Prefer an honest `sorry` with a precise comment to a bogus proof.

## Report back

Finish with 4–8 lines: for each of the four obligations say PROVED / REFUTED / SORRY,
and give the one-sentence mathematical reason. State plainly which of the two
formalizations you think is the more faithful rendering of Theorem 2, and why.

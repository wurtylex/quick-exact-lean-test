# Star comparison — spec

You are comparing **one** formalization of Theorem 2 against the **reference**
formalization, and writing the result as a Lean 4 + Mathlib file.

Read exactly two files:

* `/Users/panda/Desktop/Lean/quick-test/star/Reference.lean` — namespace `Ref`
* `/Users/panda/Desktop/Lean/quick-test/formalizations/Thm2_NNN.lean` — namespace `AgentNNN`

Write exactly one file:
`/Users/panda/Desktop/Lean/quick-test/star/comparisons/Star_NNN.lean`

## Hard rules

* **Do not run `lake` or `lean`.** Do not edit any file other than your own.
  Your file will be batch-compiled with the other 19; you will get the compiler
  errors back and one chance to fix them.
* No `import` lines — your file is spliced into a larger one that already has
  `import Mathlib`.
* No `axiom`, no `native_decide`, no `@[implemented_by]`.
* Everything inside `namespace Star_NNN` … `end Star_NNN`.
* **Budget: at most 150 lines.** Write it in one `Write` call. Do not go
  exploring Mathlib.

## The four obligations

Use these names exactly. Prove what you can; `sorry` the rest **honestly**,
with a one-line comment saying why.

```lean
namespace Star_NNN

theorem cpwl (n : ℕ) : AgentNNN.CPWL n = Ref.CPWL n := sorry
theorem relun (n k : ℕ) : AgentNNN.ReLUn n k = Ref.ReLUn n k := sorry
theorem depth (n : ℕ) (hn : 3 ≤ n) : AgentNNN.depthBound n = Ref.depthBound n := sorry
theorem statement :
    (∀ n, 3 ≤ n → AgentNNN.CPWL n = AgentNNN.ReLUn n (AgentNNN.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_NNN
```

If a claim is **false**, do not leave it as `sorry` — refute it. Use these exact
names and shapes instead of (or in addition to) the positive form:

```lean
theorem cpwl_ne : ∃ n, AgentNNN.CPWL n ≠ Ref.CPWL n := ...
theorem relun_ne : ∃ n k, AgentNNN.ReLUn n k ≠ Ref.ReLUn n k := ...
theorem depth_ne : ∃ n, 3 ≤ n ∧ AgentNNN.depthBound n ≠ Ref.depthBound n := ...
theorem statement_ne : ¬ ((∀ n, 3 ≤ n → AgentNNN.CPWL n = AgentNNN.ReLUn n (AgentNNN.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n))) := ...
```

### The bonus obligation — try this whenever you refute `cpwl`

If you refute `cpwl`, the file almost certainly states a **false** theorem, and
you can usually prove that outright — which is a much stronger result than
"differs from the reference", because it needs no reference theorem at all:

```lean
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → AgentNNN.CPWL n = AgentNNN.ReLUn n (AgentNNN.depthBound n)) := ...
```

Recipe (this is how `043` did it): at `n = 3`, exhibit a function that is in
`AgentNNN.ReLUn 3 (depthBound 3)` but not in `AgentNNN.CPWL 3`. Relu of a
coordinate works — it is a one-hidden-layer network, so it is in `ReLUn`, and the
neighbourhood-agreement `CPWL` rejects it by the kink argument below.

Name it exactly `agent_side_false`, at the top level of `namespace Star_NNN`,
not nested inside another proof. It is probed separately.

A verdict is machine-read from each declaration's **axiom set**, so a `sorry`
laundered through another `sorry`-ed theorem is detected and rejected.

**In particular: do not prove `statement` by invoking `AgentNNN.theorem2` or
`Ref.theorem2`.** Both are `sorry`-ed; routing through them proves nothing.

## What is already known (use it, don't rediscover it)

**`depth` is provable for every file.** All 100 formalizations define the same
function, in one of three shapes. The bridge is
`Real.natCeil_logb_natCast (b n : ℕ) : ⌈Real.logb b ↑n⌉₊ = Nat.clog b n`.
Note its `b` is a *cast* `↑(3:ℕ)`, while every file writes the real numeral `3`,
so you must rewrite with `((3:ℕ):ℝ) = (3:ℝ)` first. `((n:ℝ) - 1)` and
`(((n-1:ℕ)):ℝ)` agree for `n ≥ 1`, which `hn` gives you.

**The `CPWL`-by-neighbourhood-agreement family is refutable.** If the file
defines CPWL as `∀ x, ∃ i, ∀ᶠ y in nhds x, f y = g i y` with `g` a finite family
of affine functions, that condition forces `f` to be **globally affine** on
connected `ℝⁿ` — it is strictly stronger than CPWL, so `cpwl` is *false* and you
should prove `cpwl_ne`.

Witness: `f = fun x => max 0 (x 0)` at `n = 1`.
* `f ∈ Ref.CPWL 1`: take the cover `P 0 = {x | x 0 ≤ 0}` with `g 0 = 0` and
  `P 1 = {x | -x 0 ≤ 0}` with `g 1 = fun x => x 0`. Both are halfspaces, they
  cover `ℝ`, and `f` agrees with the stated affine map on each.
* `f ∉ AgentNNN.CPWL 1`: at `x = 0`, agreement on a neighbourhood gives `ε > 0`
  with `max 0 y = a*y + b` for all `|y| < ε`. Then `y = 0` gives `b = 0`,
  `y = ε/2` gives `a = 1`, and `y = -ε/2` gives `0 = -ε/2`, contradiction.

**`relun` is genuinely hard** when the file says *exactly* `k` hidden layers and
the reference says *at most* `k`. These denote the same set, but only via the
padding identity `x = relu x - relu (-x)`, which is a real theorem. An honest
`sorry` here is expected and fine — do not fake it.

## Style

Match the surrounding Lean: `theorem`/`lemma` with doc comments where the
statement is not obvious, no `example`, no commented-out attempts. If you prove
something interesting on the way, keep it as a named private lemma above the
obligation that uses it.

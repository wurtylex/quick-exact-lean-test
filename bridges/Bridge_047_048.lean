namespace Bridge_047_048

/-!
Agent047 and Agent048 are extremely close formalizations: `CPWL`, `IsAffineFun`, and
`depthBound` are literally the same expressions (up to a `Finset.univ.sum` vs `∑`
notation difference, and an explicit vs implicit `n` argument, neither of which changes
the underlying proposition). `ReLUn` also agrees in *spirit* ("at most `k` hidden
layers"), but the two agents build up their `k`-hidden-layer network relations with
opposite recursion directions:

* Agent047's `NetComputes` is defined by recursion that appends the *new last* hidden
  layer on the output side at each step: a `(k+1)`-layer network is a `k`-layer network
  `g` followed by `ReLU` and one more affine map.
* Agent048's `Computes` is defined by recursion that peels off the *first* affine layer
  on the input side at each step: a `(k+1)`-layer network is one affine map and a `ReLU`
  followed by a `k`-layer network.

These two recursions describe the same class of functions (any chain of `k+2` affine
maps interleaved with ReLU can be split from either end), but proving that requires a
genuine reassociation argument: essentially a "cons vs. snoc" duality for chains of
affine+ReLU layers, proved by a double induction that peels one layer at a time off the
*other* end of an already-built network. This is exactly the kind of delicate
construction the task instructions flag as better left honest than forced through
without the ability to compile-check it, so `relun` (and `statement`, which depends on
it) are left as `sorry` below with this explanation.
-/

/-- `CPWL` is the identical predicate in both files: continuous, and at every point
locally equal to one of finitely many affine functions, where "affine" is also the
identical predicate in both files (`Finset.univ.sum` and `∑` are the same notation, and
the explicit/implicit `n` argument does not change the resulting proposition). -/
theorem cpwl (n : ℕ) : Agent047.CPWL n = Agent048.CPWL n := by
  ext f
  constructor
  · rintro ⟨hc, m, g, hg, hloc⟩
    exact ⟨hc, m, g, hg, hloc⟩
  · rintro ⟨hc, m, g, hg, hloc⟩
    exact ⟨hc, m, g, hg, hloc⟩

/-- Both agents define `depthBound n` by the literally identical expression
`⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`, so the two functions are definitionally equal and
`hn` is not even needed. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent047.depthBound n = Agent048.depthBound n := rfl

/-- Agent047's `ReLUn n k` is built from `NetComputes`, whose recursion appends a new
final affine+ReLU layer on the *output* side (`k+1`-layer net = `k`-layer net `g`, then
`ReLU`, then one more affine map). Agent048's `ReLUn n k` is built from `Computes`,
whose recursion peels the *first* affine+ReLU layer off the *input* side (`k+1`-layer
net = one affine map, then `ReLU`, then a `k`-layer net). These two recursive
definitions describe the same set of functions (a chain of `k + 2` affine maps
interleaved with `k + 1` ReLUs can equivalently be decomposed from either end), but
proving `Agent047.ReLUn n k = Agent048.ReLUn n k` requires a reassociation lemma
("peel a layer off the other end of an already-built network") proved by its own
nested induction on the layer count, in both directions. I was not able to carry out
and compile-check that double induction safely here, so this is left honest rather
than risking a subtly wrong term/tactic proof. -/
theorem relun (n k : ℕ) : Agent047.ReLUn n k = Agent048.ReLUn n k := by
  sorry

/-- This is a direct corollary of `cpwl`, `relun`, and `depth`: rewriting each agent's
internal statement `CPWL n = ReLUn n (depthBound n)` along those three equalities turns
one side into the other. Since `relun` above is left as `sorry` (the genuine difficulty
is the `NetComputes`-vs-`Computes` reassociation, not anything specific to this
`statement` wrapper), this inherits the same gap rather than compounding a new one. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent047.CPWL n = Agent047.ReLUn n (Agent047.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent048.CPWL n = Agent048.ReLUn n (Agent048.depthBound n)) := by
  sorry

end Bridge_047_048

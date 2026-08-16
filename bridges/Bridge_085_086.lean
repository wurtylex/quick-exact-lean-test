namespace Bridge_085_086

/-!
Bridge between `Agent085` and `Agent086`'s formalizations of Theorem 2.

Both agents use the same "exactly `k` hidden layers" recursive network definition
(`Computes` vs `NetComputes`) and the *identical* real-number formula for
`depthBound`, so `depth` is a genuine `rfl`.

They diverge on the other two axes flagged in BRIDGE_SPEC.md:

* `ReLUn n k` : Agent085 reads it as *exactly* `k` hidden layers (`Computes n k f`);
  Agent086 reads it as *at most* `k` hidden layers (`∃ k' ≤ k, NetComputes k' n 1 f`).
  These coincide only via the ReLU padding trick `x = relu x - relu (-x)`, which
  neither agent proves and which is not attempted here.
* `CPWL n` : Agent085 uses "local agreement in a full two-sided neighbourhood of
  every point" (`∀ x, ∃ i, ∀ᶠ y in nhds x, f y = affine_i y`); Agent086 uses a
  genuine finite polyhedral subdivision. As BRIDGE_SPEC.md's hint anticipates,
  Agent085's reading is almost certainly too strong: on a connected domain, two-
  sided local agreement with one member of a *finite* family of affine functions
  at every point forces `f` to be globally affine (e.g. `x ↦ max 0 (x 0)` fails at
  `x = 0`, since no single affine function agrees with it on a full neighbourhood
  of `0` from both sides). That would make `cpwl` false in general. We did not
  formalize the ε/δ neighbourhood-extraction argument needed to nail this down
  rigorously without a compiler in the loop, so it is left `sorry` rather than
  risking a subtly broken proof.
-/

/-- **depth.** Both agents write `depthBound n := Nat.ceil (Real.logb 3 ((n:ℝ) - 1)) + 1`
verbatim, so the two definitions are definitionally equal. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent085.depthBound n = Agent086.depthBound n := rfl

/-- **cpwl.** Agent085's `CPWL` requires literal equality with one affine function from a
*finite* family on a full two-sided neighbourhood of every point; on the connected domain
`Fin n → ℝ` this plausibly collapses to the globally-affine functions only (a two-sided
neighbourhood argument at a "kink" point such as `x ↦ max 0 (x 0)` near `0` should refute
membership), whereas Agent086's polyhedral-subdivision `CPWL` genuinely contains such
piecewise-affine functions. We believe the sets differ (this should be a `cpwl_ne`, not a
`cpwl`), but proving non-membership rigorously needs a δ/ε extraction from the `∀ᶠ` filter
that we did not want to gamble on without being able to compile-check it; left `sorry`. -/
theorem cpwl (n : ℕ) : Agent085.CPWL n = Agent086.CPWL n := by
  sorry

/-- **relun.** Agent085.ReLUn n k is "exactly k hidden layers"; Agent086.ReLUn n k is "at
most k hidden layers" (a union over k' ≤ k). These sets are equal only via the standard but
unproved-by-either-agent padding lemma: any network with k' < k layers can be extended to
exactly k layers by inserting identity layers realized as `x = relu x - relu (-x)` on a
doubled hidden dimension. Constructing that padding lemma in general (for arbitrary
intermediate functions, not just a specific example) is real work neither file supplies;
left `sorry` rather than fake it. -/
theorem relun (n k : ℕ) : Agent085.ReLUn n k = Agent086.ReLUn n k := by
  sorry

/-- **statement.** Resolving this iff would require knowing the truth value of each agent's
own (unproved) Theorem 2 statement under their own definitions. We have reason to believe
Agent085's left-hand side is actually *false* (`CPWL_085` is too restrictive, see `cpwl`
above, while `ReLUn_085 n (depthBound n)` contains genuinely non-affine functions such as
nested-ReLU networks for any `depthBound n ≥ 1`), but Agent086's right-hand side is
essentially the paper's actual Theorem 2 for a faithful encoding, whose truth we cannot
settle here. Since neither side is nailed down, and we are barred from routing through
either agent's `theorem2`, this is left `sorry`. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent085.CPWL n = Agent085.ReLUn n (Agent085.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent086.CPWL n = Agent086.ReLUn n (Agent086.depthBound n)) := by
  sorry

end Bridge_085_086

namespace Bridge_029_030

/-
Comparison of the two formalizations.

* `depthBound`: both agents write literally the same term
  `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1` (`Nat.ceil` is exactly the `⌈·⌉₊` notation), so
  the two `depthBound`s are definitionally equal. Proved unconditionally.

* `CPWL`: both agents give a genuine polyhedral-subdivision definition (continuity plus
  a finite cover of `ℝⁿ` by polyhedra on which `f` is affine). They differ only in
  packaging: Agent029's `IsPolyhedron` writes a polyhedron directly as
  `{x | ∀ i, ⟨a i, x⟩ ≤ b i}` and folds the affine witness into the same existential as
  the covering set (`IsAffineOn`), while Agent030's `IsPolyhedron` writes it as an
  intersection `⋂ j, H j` of separately-packaged halfspaces and factors the affine
  witness out into an explicit function `g`. These packagings are interchangeable, so
  `CPWL` is proved equal via an auxiliary `isPolyhedron_iff` lemma plus repackaging the
  affine witnesses.

* `ReLUn`: Agent029 uses *exactly* `k` hidden layers, built from a `Fin`-indexed
  `Network` structure whose forward pass folds over `List.finRange (k+1)` using
  `ℕ`-indexed matrices/vectors (`Affine.eval` sums only the first `a` coordinates).
  Agent030 uses *at most* `k` hidden layers (`∃ k' ≤ k, ComputesWithHiddenLayers …`),
  built from a completely different structural recursion on `k` with `Fin`/`Matrix`
  affine maps. These two representable-function classes are genuinely equal
  mathematically (via the padding trick flagged in the spec: `x = ReLU x - ReLU (-x)`
  lets one hidden layer simulate the identity, so a `k'`-hidden-layer network can always
  be padded out to exactly `k ≥ k'` hidden layers without changing the function). But
  proving this in Lean needs two substantial, currently nonexistent pieces: (1) a
  translation lemma between `Network` (fold over `ℕ`-indexed sequences) and
  `ComputesWithHiddenLayers` (structural recursion on `Fin`-indexed affine maps), and
  (2) the padding lemma itself, built out of that translation. Neither exists in either
  source file or in Mathlib, and getting the translation right (matching `foldl` over
  `List.finRange` to a `Nat`-recursive predicate, with the `ℕ`-vs-`Fin` bookkeeping in
  `Affine.eval`'s "sum only the first `a` coordinates" convention) is a genuine
  formalization project on its own, not something safely dischargeable without being
  able to compile-check it. Left as `sorry`; see the comment directly above `relun`.

* `statement`: even granting `cpwl` and `depth`, closing this obligation needs
  `Agent029.ReLUn n (depthBound n) = Agent030.ReLUn n (depthBound n)` for *every*
  `n ≥ 3` — i.e. exactly the unresolved `relun` gap above (restricted to the values
  `k = depthBound n`, which range over infinitely many `k`, so this is no easier than
  the general statement). Left as `sorry`; see the comment above `statement`.

Overall: Agent030's `ReLUn` (the "at most k" / monotone-in-`k` reading, justified
explicitly in its own header comment as the reading under which Theorem 2 is a true
equality) is the more faithful rendering of Theorem 2 as an *equality* of sets — with
Agent029's "exactly k" reading, `CPWL n = ReLUn n (depthBound n)` can only be true at
all if the padding trick is invoked implicitly, which Agent029's statement of the
theorem does not acknowledge. Both `CPWL` definitions are equally faithful genuine
polyhedral-subdivision renderings.
-/

/-- A polyhedron in Agent029's sense (`{x | ∀ i, ⟨a i, x⟩ ≤ b i}`) is the same thing as
a polyhedron in Agent030's sense (an intersection of separately-packaged halfspaces). -/
private lemma isPolyhedron_iff {n : ℕ} (S : Set (Fin n → ℝ)) :
    Agent029.IsPolyhedron S ↔ Agent030.IsPolyhedron n S := by
  constructor
  · rintro ⟨m, a, b, hS⟩
    refine ⟨m, fun i => {x : Fin n → ℝ | (∑ j, a i j * x j) ≤ b i}, fun i => ⟨a i, b i, rfl⟩, ?_⟩
    rw [hS]
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
  · rintro ⟨l, H, hH, hS⟩
    choose a b hab using hH
    refine ⟨l, a, b, ?_⟩
    rw [hS]
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq, hab]

theorem cpwl (n : ℕ) : Agent029.CPWL n = Agent030.CPWL n := by
  ext f
  constructor
  · rintro ⟨hcont, m, P, hP, hcov, haff⟩
    choose w c hwc using haff
    exact ⟨hcont, m, P, fun i x => (∑ j, w i j * x j) + c i,
      fun i => (isPolyhedron_iff (P i)).mp (hP i),
      fun i => ⟨w i, c i, fun x => rfl⟩,
      hcov,
      fun i x hx => hwc i x hx⟩
  · rintro ⟨hcont, m, P, g, hP, hg, hcov, hfg⟩
    choose a c hac using hg
    exact ⟨hcont, m, P,
      fun i => (isPolyhedron_iff (P i)).mpr (hP i),
      hcov,
      fun i => ⟨a i, c i, fun x hx => (hfg i x hx).trans (hac i x)⟩⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent029.depthBound n = Agent030.depthBound n := by
  simp only [Agent029.depthBound, Agent030.depthBound]

/- `Agent029.ReLUn n k` means "computed by a `Network` with *exactly* `k` hidden
layers" (a `Fin`-indexed fold over `ℕ`-indexed matrices/vectors). `Agent030.ReLUn n k`
means "computed by `ComputesWithHiddenLayers n k' f` for some `k' ≤ k`" (a completely
different `Fin`/`Matrix`-based structural recursion on `k`). These classes are equal as
sets — the "at most k' ≤ k" ⊆ "exactly k" direction is exactly the padding argument
flagged in the spec (`x = ReLU x - ReLU (-x)` turns one extra hidden layer into an
identity, so any network with fewer than `k` hidden layers can be padded up to exactly
`k`) — but proving it requires (1) a translation lemma between the two entirely
different network representations (`Network`'s `List.finRange`-fold over `ℕ`-indexed
sequences vs. `ComputesWithHiddenLayers`'s `Nat`-recursion over `Fin`/`Matrix` affine
maps) and (2) the padding lemma itself built on top of that translation. Neither exists
in the source files or in Mathlib; constructing both correctly, with no ability to
compile-check the result, is a substantial standalone formalization project that is not
safely dischargeable here. -/
theorem relun (n k : ℕ) : Agent029.ReLUn n k = Agent030.ReLUn n k := sorry

/- Depends on the same gap as `relun` above: even with `cpwl` and `depth` in hand,
closing this iff needs `Agent029.ReLUn n (depthBound n) = Agent030.ReLUn n (depthBound n)`
for every `n ≥ 3` (an unbounded family of instances of the unresolved `relun`
equivalence, so restricting to `k = depthBound n` buys no simplification). -/
theorem statement :
    (∀ n, 3 ≤ n → Agent029.CPWL n = Agent029.ReLUn n (Agent029.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent030.CPWL n = Agent030.ReLUn n (Agent030.depthBound n)) := sorry

end Bridge_029_030

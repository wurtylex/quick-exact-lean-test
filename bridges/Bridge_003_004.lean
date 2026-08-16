namespace Bridge_003_004

/-!
## Comparison of Agent003 and Agent004

The two formalizations are structurally very close:

* `CPWL` — both use the "local agreement with a finite family of affine pieces"
  characterization: `Continuous f` and a finite family such that every point has a
  neighborhood on which `f` agrees with one member of the family. Agent003 encodes an
  affine piece as an arbitrary function together with an `IsAffineFun` existential
  witness; Agent004 bundles the witness data into a `structure AffFunctional`. These
  are in bijective correspondence (via `Classical.choice`/`choose`), so `cpwl` is proved
  below.
* `ReLUn` — both mean "at most `k` hidden layers". Agent003 encodes "exactly `k`
  hidden layers" as a `Set`-valued structural recursion `ReLUnExact`, using a bare
  product type `AffineMap a b := Matrix (Fin b) (Fin a) ℝ × (Fin b → ℝ)` for affine
  maps. Agent004 encodes the same alternating composition as an inductive family of
  *terms* `ReLUNet n k` (with `AffMap` a structure with the same two fields), evaluated
  by `ReLUNet.eval`. These describe exactly the same functions layer by layer; the
  auxiliary lemma `reluNet_equiv` below establishes this by induction on the depth `k`,
  converting between the product-type `AffineMap`/`Set`-recursion presentation and the
  structure/inductive-family presentation. `relun` then follows.
* `depthBound` — both are *literally* the same term `⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1`
  (Agent004 just writes it with the `⌈·⌉₊` notation for `Nat.ceil`), so `depth` is `rfl`.
* `statement` — follows immediately by rewriting through the three pointwise
  equalities above.

So all four obligations are provable, and the two formalizations say the same thing.
-/

/-- Conversion, by induction on the hidden-layer count `k`, between Agent003's
`Set`-recursion presentation of "exactly `k` hidden layers" and Agent004's
inductive-family-of-terms presentation. The two use different (but field-for-field
identical) encodings of affine maps, `Agent003.AffineMap` (a bare product type) and
`Agent004.AffMap` (a two-field structure); we convert between them with the evident
bijection `T ↦ ⟨T.1, T.2⟩` / `T ↦ (T.A, T.c)`, under which `eval` matches up
definitionally. -/
private lemma reluNet_equiv : ∀ (k n : ℕ),
    Agent003.ReLUnExact n k
      = {f : (Fin n → ℝ) → ℝ | ∃ net : Agent004.ReLUNet n k, f = net.eval} := by
  intro k
  induction k with
  | zero =>
      intro n
      ext f
      constructor
      · rintro ⟨T, hT⟩
        exact ⟨Agent004.ReLUNet.last ⟨T.1, T.2⟩, hT⟩
      · rintro ⟨net, hnet⟩
        cases net with
        | last T =>
          exact ⟨(T.A, T.c), hnet⟩
  | succ k ih =>
      intro n
      ext f
      constructor
      · rintro ⟨m, T, g, hg, hf⟩
        rw [ih m] at hg
        obtain ⟨rest, hrest⟩ := hg
        refine ⟨Agent004.ReLUNet.step ⟨T.1, T.2⟩ rest, ?_⟩
        subst hf
        subst hrest
        funext x
        rfl
      · rintro ⟨net, hnet⟩
        cases net with
        | step m T' rest =>
          refine ⟨m, (T'.A, T'.c), rest.eval, ?_, hnet⟩
          rw [ih m]
          exact ⟨rest, rfl⟩

theorem cpwl (n : ℕ) : Agent003.CPWL n = Agent004.CPWL n := by
  ext f
  constructor
  · rintro ⟨hf, m, g, hg, hloc⟩
    choose a c hac using hg
    refine ⟨hf, m, fun i => ⟨a i, c i⟩, ?_⟩
    intro x
    obtain ⟨i, hi⟩ := hloc x
    refine ⟨i, ?_⟩
    filter_upwards [hi] with y hy
    rw [hy]
    exact hac i y
  · rintro ⟨hf, m, g, hloc⟩
    refine ⟨hf, m, fun i => (g i).eval, fun i => ⟨(g i).a, (g i).c, fun x => rfl⟩, ?_⟩
    intro x
    obtain ⟨i, hi⟩ := hloc x
    exact ⟨i, hi⟩

theorem relun (n k : ℕ) : Agent003.ReLUn n k = Agent004.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨j, hj, hf⟩
    rw [reluNet_equiv j n] at hf
    obtain ⟨net, hnet⟩ := hf
    exact ⟨j, hj, net, hnet⟩
  · rintro ⟨j, hj, net, hnet⟩
    refine ⟨j, hj, ?_⟩
    rw [reluNet_equiv j n]
    exact ⟨net, hnet⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent003.depthBound n = Agent004.depthBound n := rfl

theorem statement :
    (∀ n, 3 ≤ n → Agent003.CPWL n = Agent003.ReLUn n (Agent003.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent004.CPWL n = Agent004.ReLUn n (Agent004.depthBound n)) := by
  constructor
  · intro h n hn
    rw [← cpwl n, ← depth n hn, ← relun n (Agent003.depthBound n)]
    exact h n hn
  · intro h n hn
    rw [cpwl n, depth n hn, relun n (Agent004.depthBound n)]
    exact h n hn

end Bridge_003_004

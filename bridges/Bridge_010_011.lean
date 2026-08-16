namespace Bridge_010_011

/-!
## Comparison of Agent010 and Agent011

These two formalizations are structurally almost identical. Both:

* encode `ℝ^n` as `Fin n → ℝ`;
* encode an affine map `ℝ^a → ℝ^b` as a `(A, c)` pair (`Matrix (Fin b) (Fin a) ℝ`
  and `Fin b → ℝ`) acting as `x ↦ A.mulVec x + c` (`Agent010.AffineMap` /
  `Agent011.Layer`, `Agent010.AffineMap.eval` / `Agent011.Layer.apply`);
* encode a `k`-hidden-layer ReLU network as a chain of `k + 1` such affine maps
  with `reluVec` interleaved — Agent010 as a `Prop`-valued recursive relation
  `NetComputes`, Agent011 as an inductive `Type` of literal layer-chains
  `NetLayers` together with an `eval` function. These describe exactly the same
  networks; the bridge below is a term-level converter between `AffineMap`s and
  `Layer`s, lifted by induction on the layer count to a converter between
  `NetComputes` witnesses and `NetLayers` terms.
* take `ReLUn n k` to mean "at most `k` hidden layers" (`∃ k' ≤ k, ...`);
* take `depthBound n` to be *literally* the same expression
  `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1` (`Nat.ceil` is exactly the notation `⌈·⌉₊`),
  so `depth` below is `rfl`;
* take `CPWL n` to be "continuous, and locally (near every point) equal to one
  of finitely many affine functions": Agent010 phrases "affine function" as
  `AffineMap n 1` evaluated at its unique output coordinate and "locally equal"
  as `∀ᶠ y in nhds x, f y = …`; Agent011 phrases "affine function" as the
  explicit witness formula `∑ a i * x i + b` (`IsAffineFun`) and "locally
  equal" as `∃ U ∈ nhds x, EqOn f (g i) U`. These are the same mathematical
  content in different packaging, so `cpwl` below is a genuine equality, proved
  by translating one packaging into the other in both directions.

Since all four underlying notions agree, all four bridge obligations are
proved (no refutations, no `sorry`s are needed for this pair).
-/

/-- Convert an `Agent010.AffineMap` to the corresponding `Agent011.Layer`: both are
literally the same `(A, c)` pair, just packaged in a differently-named structure. -/
def toLayer {a b : ℕ} (T : Agent010.AffineMap a b) : Agent011.Layer a b :=
  ⟨T.A, T.c⟩

/-- Convert an `Agent011.Layer` to the corresponding `Agent010.AffineMap`. -/
def toAffineMap {a b : ℕ} (L : Agent011.Layer a b) : Agent010.AffineMap a b :=
  ⟨L.A, L.c⟩

theorem toLayer_apply {a b : ℕ} (T : Agent010.AffineMap a b) (x : Fin a → ℝ) :
    (toLayer T).apply x = T.eval x := rfl

theorem toAffineMap_eval {a b : ℕ} (L : Agent011.Layer a b) (x : Fin a → ℝ) :
    (toAffineMap L).eval x = L.apply x := rfl

/-- `Agent010.NetComputes` (a `Prop` defined by recursion on the hidden-layer count)
and `Agent011.NetLayers` (an inductive `Type` of literal layer-chains, with an `eval`
function) describe exactly the same networks. Proved by induction on the layer count,
converting affine maps back and forth with `toLayer` / `toAffineMap`. -/
theorem netComputes_iff_netLayers :
    ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
      Agent010.NetComputes n k f ↔ ∃ net : Agent011.NetLayers n k, f = net.eval := by
  intro k
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨T, hT⟩
      refine ⟨Agent011.NetLayers.last (toLayer T), ?_⟩
      funext x
      show f x = (toLayer T).apply x 0
      rw [hT, toLayer_apply]
    · rintro ⟨net, hnet⟩
      cases net with
      | last L =>
        refine ⟨toAffineMap L, fun x => ?_⟩
        rw [hnet]
        show L.apply x 0 = (toAffineMap L).eval x 0
        rw [toAffineMap_eval]
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, T, g, hg, hf⟩
      obtain ⟨net, hnet⟩ := (ih m g).mp hg
      refine ⟨Agent011.NetLayers.cons (toLayer T) net, ?_⟩
      funext x
      have hx : f x = g (Agent010.reluVec (T.eval x)) := by rw [hf]
      rw [hx]
      show g (Agent010.reluVec (T.eval x)) = net.eval (Agent011.reluVec ((toLayer T).apply x))
      rw [toLayer_apply, hnet]
    · rintro ⟨net, hnet⟩
      cases net with
      | cons L rest =>
        refine ⟨_, toAffineMap L, rest.eval, (ih _ rest.eval).mpr ⟨rest, rfl⟩, ?_⟩
        funext x
        rw [hnet]
        show rest.eval (Agent011.reluVec (L.apply x))
            = rest.eval (Agent011.reluVec ((toAffineMap L).eval x))
        rw [toAffineMap_eval]

theorem relun (n k : ℕ) : Agent010.ReLUn n k = Agent011.ReLUn n k := by
  ext f
  simp only [Agent010.ReLUn, Agent011.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k', hk', hf⟩
    exact ⟨k', hk', (netComputes_iff_netLayers k' n f).mp hf⟩
  · rintro ⟨k', hk', net, hf⟩
    exact ⟨k', hk', (netComputes_iff_netLayers k' n f).mpr ⟨net, hf⟩⟩

/-- Both agents write `depthBound` as *literally* the same term
`⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1` (`Nat.ceil x` is exactly the notation `⌈x⌉₊`),
so this holds unconditionally, without even using `hn`. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent010.depthBound n = Agent011.depthBound n := rfl

/-- `Agent010.CPWL` and `Agent011.CPWL` are both "continuous, and near every point
locally equal to one of finitely many affine functions"; they differ only in how
"affine function" and "locally equal" are spelled out. We translate an
`AffineMap n 1`-based family into an `IsAffineFun`-based family and back, and
`Filter.eventually_iff_exists_mem` to bridge `∀ᶠ` and `∃ U ∈ nhds x, EqOn …`. -/
theorem cpwl (n : ℕ) : Agent010.CPWL n = Agent011.CPWL n := by
  ext f
  simp only [Agent010.CPWL, Agent011.CPWL, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hf, m, φ, hφ⟩
    refine ⟨hf, m, fun i x => (φ i).eval x 0, ?_, ?_⟩
    · intro i
      refine ⟨fun j => (φ i).A 0 j, (φ i).c 0, fun x => ?_⟩
      show (φ i).eval x 0 = (∑ j : Fin n, (φ i).A 0 j * x j) + (φ i).c 0
      rfl
    · intro x
      obtain ⟨i, hi⟩ := hφ x
      refine ⟨i, ?_⟩
      rw [Filter.eventually_iff_exists_mem] at hi
      obtain ⟨U, hU, hUeq⟩ := hi
      exact ⟨U, hU, fun y hy => hUeq y hy⟩
  · rintro ⟨hf, m, g, hg, hcov⟩
    choose a b hab using hg
    refine ⟨hf, m,
      fun i => (⟨fun _ j => a i j, fun _ => b i⟩ : Agent010.AffineMap n 1), ?_⟩
    intro x
    obtain ⟨i, U, hU, hUeq⟩ := hcov x
    refine ⟨i, ?_⟩
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨U, hU, fun y hy => ?_⟩
    have hy' : f y = g i y := hUeq hy
    show f y = (∑ j : Fin n, a i j * y j) + b i
    rw [hy', hab i y]

theorem statement :
    (∀ n, 3 ≤ n → Agent010.CPWL n = Agent010.ReLUn n (Agent010.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent011.CPWL n = Agent011.ReLUn n (Agent011.depthBound n)) := by
  constructor
  · intro h n hn
    calc Agent011.CPWL n = Agent010.CPWL n := (cpwl n).symm
      _ = Agent010.ReLUn n (Agent010.depthBound n) := h n hn
      _ = Agent011.ReLUn n (Agent010.depthBound n) := relun n (Agent010.depthBound n)
      _ = Agent011.ReLUn n (Agent011.depthBound n) := by rw [depth n hn]
  · intro h n hn
    calc Agent010.CPWL n = Agent011.CPWL n := cpwl n
      _ = Agent011.ReLUn n (Agent011.depthBound n) := h n hn
      _ = Agent011.ReLUn n (Agent010.depthBound n) := by rw [depth n hn]
      _ = Agent010.ReLUn n (Agent010.depthBound n) := (relun n (Agent010.depthBound n)).symm

end Bridge_010_011

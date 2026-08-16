namespace Bridge_012_013

/-!
## Comparison of `Agent012` and `Agent013`

Both formalizations turn out to make essentially the *same* modelling choices:

* `depthBound n := ⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1` — literally the same expression in
  both files (`⌈x⌉₊` is notation for `Nat.ceil x`).
* `ReLUn n k` is "at most `k` hidden layers", built from a `k`-indexed recursive
  predicate for "exactly `k` hidden layers" (`IsReLUNetExact` in `Agent012`,
  `IsReLURep` in `Agent013`). The two recursive predicates differ only in *bundling*:
  `Agent012` carries a separate matrix `A` and bias vector around, `Agent013` bundles
  them into a structure `AffineMap`, and `Agent012`'s base case states affinity via a
  bare existential (`IsAffine`) while `Agent013`'s base case bundles it into an
  `AffineMap n 1` evaluated at index `0`. These are interconvertible.
* `CPWL n` is "continuous, and at every point `x` there is a neighbourhood of `x` and
  a member of a fixed finite family of affine functions that agrees with `f` there" in
  both files; `Agent012` phrases the neighbourhood via `Filter.EventuallyEq (nhds x)`,
  `Agent013` phrases it via an explicit `ε`-ball. `Metric.eventually_nhds_iff`
  converts between the two.

So all four obligations below are provable equalities/iffs, not refutations.
-/

/-- An `Agent013.AffineMap n 1`, evaluated at the (unique) output coordinate `0`, is
given by the dot product of row `0` of its matrix with the input, plus its bias at `0`.
This is the bridge between `Agent013`'s bundled `AffineMap` and `Agent012`'s bare
`∃ a b, ...` style of affine function. -/
theorem affine_eval_eq {n : ℕ} (T : Agent013.AffineMap n 1) (x : Fin n → ℝ) :
    (T.eval x) 0 = (∑ j, T.A 0 j * x j) + T.c 0 := by
  simp [Agent013.AffineMap.eval, Matrix.mulVec, dotProduct, Pi.add_apply]

/-- `Agent012.reluVec` and `Agent013.reluVec` are the same function (both componentwise
`max 0 ·`), just defined independently in each namespace. -/
theorem reluVec_eq {m : ℕ} (x : Fin m → ℝ) : Agent012.reluVec x = Agent013.reluVec x := by
  funext i
  simp [Agent012.reluVec, Agent012.relu, Agent013.reluVec, Agent013.relu]

/-- `Filter.EventuallyEq (nhds x) f g`, as used by `Agent012.CPWL`, is the same
statement as `Agent013`'s explicit `∃ ε > 0, ∀ y, dist y x < ε → f y = g y`, via the
standard metric-space characterisation of `nhds`. -/
theorem nhds_iff_ball {n : ℕ} (f g : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    Filter.EventuallyEq (nhds x) f g ↔ ∃ ε > 0, ∀ y : Fin n → ℝ, dist y x < ε → f y = g y :=
  Metric.eventually_nhds_iff

/-- `Agent012.IsReLUNetExact n k f` and `Agent013.IsReLURep n k f` agree for every
`k`: both say `f` is computed by an alternating composition of `k + 1` affine maps and
`k` componentwise-ReLUs, the only difference being that `Agent013` bundles each affine
map's matrix and bias into a structure. Proved by induction on `k`. -/
theorem relu_rep_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent012.IsReLUNetExact n k f ↔ Agent013.IsReLURep n k f := by
  intro k
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨a, b, hab⟩
      refine ⟨⟨fun _ j => a j, fun _ => b⟩, ?_⟩
      funext x
      rw [hab x, affine_eval_eq]
    · rintro ⟨T, hT⟩
      refine ⟨fun j => T.A 0 j, T.c 0, fun x => ?_⟩
      have hx : f x = T.eval x 0 := congrFun hT x
      rw [hx, affine_eval_eq]
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, A, bias, g, hg, hfx⟩
      refine ⟨m, ⟨A, bias⟩, g, (ih m g).mp hg, ?_⟩
      funext x
      rw [hfx x, reluVec_eq]
    · rintro ⟨m, T, g, hg, hfx⟩
      refine ⟨m, T.A, T.c, g, (ih m g).mpr hg, fun x => ?_⟩
      have hx : f x = g (Agent013.reluVec (T.eval x)) := congrFun hfx x
      rw [hx, reluVec_eq]

theorem cpwl (n : ℕ) : Agent012.CPWL n = Agent013.CPWL n := by
  ext f
  constructor
  · rintro ⟨hf, m, g, hg_affine, hloc⟩
    choose a b hab using hg_affine
    have h : Fin m → Agent013.AffineMap n 1 := fun i => ⟨fun _ j => a i j, fun _ => b i⟩
    refine ⟨hf, m, h, fun x => ?_⟩
    obtain ⟨i, hi⟩ := hloc x
    obtain ⟨ε, hε, hball⟩ := (nhds_iff_ball f (g i) x).mp hi
    refine ⟨i, ε, hε, fun y hy => ?_⟩
    have e1 : f y = g i y := hball y hy
    have e2 : g i y = ∑ j, a i j * y j + b i := hab i y
    have e3 : (h i).eval y 0 = ∑ j, a i j * y j + b i := affine_eval_eq (h i) y
    rw [e1, e2, e3]
  · rintro ⟨hf, r, g, hloc⟩
    have g' : Fin r → ((Fin n → ℝ) → ℝ) := fun i y => (g i).eval y 0
    have hg'_affine : ∀ i, Agent012.IsAffine (g' i) :=
      fun i => ⟨fun j => (g i).A 0 j, (g i).c 0, fun x => affine_eval_eq (g i) x⟩
    refine ⟨hf, r, g', hg'_affine, fun x => ?_⟩
    obtain ⟨i, ε, hε, hball⟩ := hloc x
    exact ⟨i, (nhds_iff_ball f (g' i) x).mpr ⟨ε, hε, hball⟩⟩

theorem relun (n k : ℕ) : Agent012.ReLUn n k = Agent013.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨j, hjk, hf⟩
    exact ⟨j, hjk, (relu_rep_iff j n f).mp hf⟩
  · rintro ⟨j, hjk, hf⟩
    exact ⟨j, hjk, (relu_rep_iff j n f).mpr hf⟩

/-- The two `depthBound`s are the literally identical expression
`⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1` (`⌈x⌉₊` being notation for `Nat.ceil x`), so they
agree for every `n`, in particular for `n` with `3 ≤ n`. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent012.depthBound n = Agent013.depthBound n := rfl

theorem statement :
    (∀ n, 3 ≤ n → Agent012.CPWL n = Agent012.ReLUn n (Agent012.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent013.CPWL n = Agent013.ReLUn n (Agent013.depthBound n)) := by
  constructor
  · intro h n hn
    have e1 := h n hn
    rw [cpwl n, relun n (Agent012.depthBound n), depth n hn] at e1
    exact e1
  · intro h n hn
    have e1 := h n hn
    rw [← cpwl n, ← depth n hn, ← relun n (Agent012.depthBound n)] at e1
    exact e1

end Bridge_012_013

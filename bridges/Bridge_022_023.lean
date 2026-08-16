namespace Bridge_022_023

/-!
Agent022 and Agent023 turn out to have made essentially the *same* modelling choices:

* Both encode an affine map `ℝ^a → ℝ^b` as a matrix `A` plus bias `c`, evaluated as
  `x ↦ A.mulVec x + c` (`Agent022.AffineMap'` / `Agent023.AffineMap`, `.apply` / `.eval`).
* Both encode "computed by a ReLU network with exactly `k` hidden layers" by the same
  recursion (`k = 0`: a single affine map; `k+1`: an affine map, then componentwise ReLU,
  then a `k`-hidden-layer network), and both take `ReLUn n k` to be the union over `j ≤ k`
  ("at most `k` hidden layers").
* Both encode `CPWL n` as: continuous, and covered by finitely many affine functions such
  that every point has a neighbourhood on which `f` agrees with one of them.
* Both write `depthBound n` as `Nat.ceil (Real.logb 3 ((n:ℝ) - 1)) + 1` (Agent023 uses the
  `⌈⌉₊` notation for the same function `Nat.ceil`).

So the two formalizations are provably identical on all four fronts; the work below is
purely bookkeeping to bridge the different (but isomorphic) auxiliary types.
-/

/-- `Agent022.relu` and `Agent023.relu` are both `fun x => max 0 x`, so they agree
(the `noncomputable` annotation on Agent023's copy doesn't affect the term). -/
private lemma relu_agree (x : ℝ) : Agent022.relu x = Agent023.relu x := rfl

/-- `Agent022.reluVec` and `Agent023.reluVec` are both componentwise `max 0`, so they
agree on every input. -/
private lemma reluVec_agree {m : ℕ} (y : Fin m → ℝ) :
    Agent022.reluVec y = Agent023.reluVec y := rfl

/-- Converting an `Agent022.AffineMap'` into an `Agent023.AffineMap` with the same
matrix/bias preserves evaluation: both `.apply`/`.eval` compute `A.mulVec x + c`. -/
private lemma apply_eval_agree {a b : ℕ} (T : Agent022.AffineMap' a b) (x : Fin a → ℝ) :
    T.apply x = Agent023.AffineMap.eval (⟨T.A, T.c⟩ : Agent023.AffineMap a b) x := rfl

/-- `Agent022.ExactReLUComputable k n f` and `Agent023.IsReLUNetworkFunc k n f` are the
same recursive "computed by a ReLU network with exactly `k` hidden layers" predicate, up
to converting between the two (structurally identical) affine-map types. Proved by
induction on `k`. -/
private lemma relun_aux :
    ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
      Agent022.ExactReLUComputable k n f ↔ Agent023.IsReLUNetworkFunc k n f := by
  intro k
  induction k with
  | zero =>
      intro n f
      constructor
      · rintro ⟨w, b, hw⟩
        exact ⟨w, b, funext hw⟩
      · rintro ⟨a, b, hab⟩
        refine ⟨a, b, ?_⟩
        intro x
        rw [hab]
  | succ k ih =>
      intro n f
      constructor
      · rintro ⟨m, T, g, hg, hf⟩
        refine ⟨m, ⟨T.A, T.c⟩, g, (ih m g).mp hg, ?_⟩
        funext x
        have hx : f x = g (Agent022.reluVec (T.apply x)) := by rw [hf]
        rw [hx, apply_eval_agree, reluVec_agree]
      · rintro ⟨m, T, g, hg, hf⟩
        refine ⟨m, ⟨T.A, T.c⟩, g, (ih m g).mpr hg, ?_⟩
        funext x
        have hx : f x = g (Agent023.reluVec (Agent023.AffineMap.eval T x)) := by rw [hf]
        rw [hx, apply_eval_agree, reluVec_agree]

theorem cpwl (n : ℕ) : Agent022.CPWL n = Agent023.CPWL n := by
  ext f
  constructor
  · rintro ⟨hf, m, w, b, hloc⟩
    refine ⟨hf, m, (fun i (y : Fin n → ℝ) => (∑ j, w i j * y j) + b i),
      (fun i => ⟨w i, b i, rfl⟩), ?_⟩
    intro x
    obtain ⟨i, U, hU, hUx⟩ := hloc x
    obtain ⟨t, htU, htO, hxt⟩ := mem_nhds_iff.mp hU
    exact ⟨i, t, htO, hxt, fun y hy => hUx y (htU hy)⟩
  · rintro ⟨hf, m, g, hg, hloc⟩
    simp only [Agent023.IsAffineFun] at hg
    choose w b hwb using hg
    refine ⟨hf, m, w, b, ?_⟩
    intro x
    obtain ⟨j, U, hUO, hxU, hUf⟩ := hloc x
    refine ⟨j, U, hUO.mem_nhds hxU, ?_⟩
    intro y hy
    have h1 : f y = g j y := hUf y hy
    rw [h1, hwb j]

theorem relun (n k : ℕ) : Agent022.ReLUn n k = Agent023.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (relun_aux j n f).mp hf⟩
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (relun_aux j n f).mpr hf⟩

/-- Both agents write `depthBound n` as `Nat.ceil (Real.logb 3 ((n:ℝ) - 1)) + 1`
(`⌈·⌉₊` is notation for `Nat.ceil`), so the two definitions are syntactically the same
term and agree by `rfl`, without even needing `hn`. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent022.depthBound n = Agent023.depthBound n := rfl

theorem statement :
    (∀ n, 3 ≤ n → Agent022.CPWL n = Agent022.ReLUn n (Agent022.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent023.CPWL n = Agent023.ReLUn n (Agent023.depthBound n)) := by
  constructor
  · intro h n hn
    have h1 := h n hn
    rw [cpwl n, relun n (Agent022.depthBound n), depth n hn] at h1
    exact h1
  · intro h n hn
    have h1 := h n hn
    rw [← depth n hn, ← relun n (Agent022.depthBound n), ← cpwl n] at h1
    exact h1

end Bridge_022_023

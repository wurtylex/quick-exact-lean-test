namespace Bridge_009_010

/-!
`Agent009` and `Agent010` use essentially isomorphic encodings:

* Both define `ReLUn n k` as "at most `k` hidden layers" (`∃ k' ≤ k, …`), with the
  underlying "exactly `k'`" predicate built by the same alternating
  `affine → componentwise-ReLU → …` recursion. `Agent009` spells an affine map
  `ℝ^a → ℝ^b` as a bare existential `∃ A c, ∀ x i, T x i = (∑ j, A i j * x j) + c i`
  (`IsAffineMap`) and an affine functional `ℝ^n → ℝ` as `IsAffineFunctional`
  (an existential weight vector + scalar bias). `Agent010` bundles the same data
  into a structure `AffineMap` with an `eval` function built from `Matrix.mulVec`.
  These are literally the same mathematical objects under a different wrapper, so
  we build two conversion lemmas (`isAffineMap_iff`, `isAffineFunctional_iff`) and
  then transport the whole recursion by induction on the hidden-layer count.
* Both define `CPWL n` via the *same* "local agreement" reading: `f` continuous and,
  at every point, eventually (in `nhds x`) equal to one of finitely many globally
  fixed affine functionals. They differ only in how an "affine functional" is
  packaged (`IsAffineFunctional` vs. `AffineMap n 1`), so the same conversion lemma
  bridges `CPWL` too.
* `depthBound` differs only in *where* the `ℕ`-to-`ℝ` cast happens: `Agent009` casts
  `n - 1` (truncated `ℕ` subtraction) to `ℝ`, `Agent010` computes `(n : ℝ) - 1`
  directly. These agree whenever `n ≥ 1`, in particular for `n ≥ 3`.

Consequently all four obligations are provable.
-/

/-- Converting between `Agent009`'s existential-witness affine maps and `Agent010`'s
bundled `AffineMap` structure. -/
private lemma isAffineMap_iff (n m : ℕ) (T : (Fin n → ℝ) → (Fin m → ℝ)) :
    Agent009.IsAffineMap n m T ↔ ∃ S : Agent010.AffineMap n m, ∀ x, T x = S.eval x := by
  constructor
  · rintro ⟨A, c, hT⟩
    refine ⟨⟨A, c⟩, fun x => ?_⟩
    funext i
    rw [hT x i]
    simp [Agent010.AffineMap.eval, Matrix.mulVec, dotProduct, Pi.add_apply]
  · rintro ⟨S, hT⟩
    refine ⟨S.A, S.c, fun x i => ?_⟩
    rw [hT x]
    simp [Agent010.AffineMap.eval, Matrix.mulVec, dotProduct, Pi.add_apply]

/-- Converting between `Agent009`'s existential-witness affine functionals and
`Agent010`'s bundled `AffineMap n 1`. -/
private lemma isAffineFunctional_iff (n : ℕ) (f : (Fin n → ℝ) → ℝ) :
    Agent009.IsAffineFunctional n f ↔ ∃ T : Agent010.AffineMap n 1, ∀ x, f x = T.eval x 0 := by
  constructor
  · rintro ⟨a, c, hf⟩
    refine ⟨⟨(fun _ j => a j), fun _ => c⟩, fun x => ?_⟩
    rw [hf x]
    simp [Agent010.AffineMap.eval, Matrix.mulVec, dotProduct, Pi.add_apply]
  · rintro ⟨T, hf⟩
    refine ⟨fun j => T.A 0 j, T.c 0, fun x => ?_⟩
    rw [hf x]
    simp [Agent010.AffineMap.eval, Matrix.mulVec, dotProduct, Pi.add_apply]

/-- The "exactly `k` hidden layers" predicates of `Agent009` and `Agent010` agree,
for every hidden width `n` and every function `f`. Proved by induction on `k`,
transporting affine-map witnesses via `isAffineMap_iff` / `isAffineFunctional_iff`
at each layer; the `ReLU` layers themselves (`Agent009.reluVec`, `Agent010.reluVec`)
are definitionally equal (`max 0 (x i)` either directly or through `Agent010.relu`),
so no separate lemma is needed for them. -/
private lemma computes_iff :
    ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
      Agent009.ComputesWithHiddenLayers k n f ↔ Agent010.NetComputes n k f := by
  intro k
  induction k with
  | zero => intro n f; exact isAffineFunctional_iff n f
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, T, g, hT, hg, hf⟩
      obtain ⟨S, hS⟩ := (isAffineMap_iff n m T).mp hT
      exact ⟨m, S, g, (ih m g).mp hg, by funext x; rw [hf x, hS x]⟩
    · rintro ⟨m, T, g, hg, hf⟩
      have hT : Agent009.IsAffineMap n m T.eval :=
        (isAffineMap_iff n m T.eval).mpr ⟨T, fun x => rfl⟩
      exact ⟨m, T.eval, g, hT, (ih m g).mpr hg, fun x => by rw [hf]⟩

theorem cpwl (n : ℕ) : Agent009.CPWL n = Agent010.CPWL n := by
  ext f
  constructor
  · rintro ⟨hfc, m, g, hg, hloc⟩
    have hg' : ∀ i, ∃ T : Agent010.AffineMap n 1, ∀ x, g i x = T.eval x 0 :=
      fun i => (isAffineFunctional_iff n (g i)).mp (hg i)
    choose φ hφ using hg'
    refine ⟨hfc, m, φ, fun x => ?_⟩
    obtain ⟨i, hi⟩ := hloc x
    refine ⟨i, ?_⟩
    filter_upwards [hi] with y hy
    rw [hy]
    exact hφ i y
  · rintro ⟨hfc, m, φ, hloc⟩
    refine ⟨hfc, m, fun i x => (φ i).eval x 0, fun i => ?_, hloc⟩
    exact (isAffineFunctional_iff n _).mpr ⟨φ i, fun x => rfl⟩

theorem relun (n k : ℕ) : Agent009.ReLUn n k = Agent010.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨k', hk', hf⟩
    exact ⟨k', hk', (computes_iff k' n f).mp hf⟩
  · rintro ⟨k', hk', hf⟩
    exact ⟨k', hk', (computes_iff k' n f).mpr hf⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent009.depthBound n = Agent010.depthBound n := by
  have h1n : (1 : ℕ) ≤ n := by omega
  have h1 : (↑(n - 1) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub h1n, Nat.cast_one]
  unfold Agent009.depthBound Agent010.depthBound
  rw [h1]

theorem statement :
    (∀ n, 3 ≤ n → Agent009.CPWL n = Agent009.ReLUn n (Agent009.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent010.CPWL n = Agent010.ReLUn n (Agent010.depthBound n)) := by
  constructor
  · intro h n hn
    rw [← cpwl n, h n hn, relun n (Agent009.depthBound n), depth n hn]
  · intro h n hn
    rw [cpwl n, h n hn, ← depth n hn, ← relun n (Agent009.depthBound n)]

end Bridge_009_010

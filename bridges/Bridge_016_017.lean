namespace Bridge_016_017

/-!
Agent016 and Agent017 turn out to have made essentially the same modelling
choices, presented with slightly different plumbing:

* Both read `ReLUn n k` as "at most `k` hidden layers" (an outer
  `∃ k' ≤ k, …` wrapped around an "exactly `k`" notion), and both encode
  "exactly `k` hidden layers" via the same alternating affine/ReLU
  composition, using matrix-based affine maps (`Agent016.AffineT`, a raw
  pair `(A, c)`, vs. `Agent017.Aff`, a two-field structure `⟨A, c⟩`),
  evaluated the same way `A.mulVec x + c`. Agent016 packages "exactly k" as
  an inductive `Prop` (`ComputesHidden`), Agent017 as a `Prop`-valued
  function defined by recursion on `k` (`ComputesWithLayers`). These agree,
  proved by induction on `k`, converting affine maps back and forth via
  `toAff`/`toAffineT`.
* Both read `CPWL n` as "continuous and, at every point, locally agrees with
  one member of a finite family of scalar affine functions" (case (b) in the
  spec): Agent016 stores the family as arbitrary functions satisfying
  `IsAffineFun`, phrased via `∀ᶠ y in nhds x, f y = g i y`; Agent017 stores
  the family as `Fin N → Aff n 1`, phrased via an explicit `U ∈ nhds x`.
  These interchange via `Filter.eventually_iff_exists_mem` together with a
  translation between `IsAffineFun` and `Aff n 1`.
* Both define `depthBound` via `Nat.ceil (Real.logb 3 ·)`, differing only in
  whether the subtraction `n - 1` happens in `ℝ` after casting (Agent016) or
  in `ℕ` before casting (Agent017); these agree via `Nat.cast_sub` for
  `n ≥ 1`.

So, unlike the "different sides of local-agreement-vs-something-else"
scenario flagged in the spec, both agents landed on the same side of every
axis, and all four obligations are provable.
-/

/-- Convert an `Agent016` affine map (a raw pair) to the `Agent017` encoding
(a two-field structure with the same fields). -/
def toAff {a b : ℕ} (T : Agent016.AffineT a b) : Agent017.Aff a b :=
  ⟨T.1, T.2⟩

/-- Convert an `Agent017` affine map (a two-field structure) to the
`Agent016` encoding (a raw pair with the same components). -/
def toAffineT {a b : ℕ} (S : Agent017.Aff a b) : Agent016.AffineT a b :=
  (S.A, S.c)

/-- The key isomorphism: `Agent016`'s "exactly `k` hidden layers" inductive
predicate and `Agent017`'s "exactly `k` hidden layers" recursive predicate
describe the same functions, by induction on `k`, converting affine maps
back and forth via `toAff`/`toAffineT`. Both `relu`/`reluVec` pairs and both
`applyAffine`/`Aff.eval` pairs are definitionally the same formula, so the
conversions themselves are transparent (`rfl`). -/
theorem computes_iff (n k : ℕ) (f : (Fin n → ℝ) → ℝ) :
    Agent016.ComputesHidden n k f ↔ Agent017.ComputesWithLayers n k f := by
  induction k generalizing n f with
  | zero =>
      constructor
      · intro h
        cases h with
        | zero T => exact ⟨toAff T, fun x => rfl⟩
      · rintro ⟨T, hT⟩
        have hf : f = fun x => Agent016.applyAffine (toAffineT T) x 0 := by
          funext x; exact hT x
        rw [hf]
        exact Agent016.ComputesHidden.zero (toAffineT T)
  | succ k ih =>
      constructor
      · intro h
        cases h with
        | succ T hg => exact ⟨_, toAff T, _, (ih _ _).mp hg, fun x => rfl⟩
      · rintro ⟨m, T, g, hg, hf⟩
        have hf' : f = fun x =>
            g (Agent016.reluVec (Agent016.applyAffine (toAffineT T) x)) := by
          funext x; exact hf x
        rw [hf']
        exact Agent016.ComputesHidden.succ (toAffineT T) ((ih m g).mpr hg)

theorem relun (n k : ℕ) : Agent016.ReLUn n k = Agent017.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨k', hk', hc⟩
    exact ⟨k', hk', (computes_iff n k' f).mp hc⟩
  · rintro ⟨k', hk', hc⟩
    exact ⟨k', hk', (computes_iff n k' f).mpr hc⟩

/-- Build an `Agent017`-style scalar affine map `ℝ^n → ℝ` out of an explicit
coefficient vector and constant, matching `Agent016.IsAffineFun`'s shape. -/
def affOfCoeffs {n : ℕ} (a : Fin n → ℝ) (c : ℝ) : Agent017.Aff n 1 :=
  ⟨fun _ j => a j, fun _ => c⟩

theorem affOfCoeffs_eval {n : ℕ} (a : Fin n → ℝ) (c : ℝ) (x : Fin n → ℝ) :
    (affOfCoeffs a c).eval x 0 = (∑ j, a j * x j) + c := by
  simp [affOfCoeffs, Agent017.Aff.eval, Matrix.mulVec, dotProduct]

/-- `Agent016`'s `IsAffineFun` and `Agent017`'s `Aff n 1` (evaluated at its
single output coordinate) describe the same scalar affine functions. -/
theorem isAffineFun_iff {n : ℕ} (g : (Fin n → ℝ) → ℝ) :
    Agent016.IsAffineFun g ↔ ∃ T : Agent017.Aff n 1, ∀ x, g x = (T.eval x) 0 := by
  constructor
  · rintro ⟨a, c, ha⟩
    exact ⟨affOfCoeffs a c, fun x => by rw [ha x, affOfCoeffs_eval]⟩
  · rintro ⟨T, hT⟩
    refine ⟨fun j => T.A 0 j, T.c 0, fun x => ?_⟩
    rw [hT x]
    simp [Agent017.Aff.eval, Matrix.mulVec, dotProduct]

theorem cpwl (n : ℕ) : Agent016.CPWL n = Agent017.CPWL n := by
  ext f
  constructor
  · rintro ⟨hfc, m, g, hg_aff, hloc⟩
    choose G hG using fun i => (isAffineFun_iff (g i)).mp (hg_aff i)
    refine ⟨hfc, m, G, fun x => ?_⟩
    obtain ⟨i, hi⟩ := hloc x
    obtain ⟨U, hU, hUy⟩ := (Filter.eventually_iff_exists_mem).mp hi
    refine ⟨U, i, hU, fun y hy => ?_⟩
    rw [hUy y hy, hG i y]
  · rintro ⟨hfc, N, g, hloc⟩
    refine ⟨hfc, N, fun i x => (g i).eval x 0,
      fun i => (isAffineFun_iff _).mpr ⟨g i, fun x => rfl⟩, fun x => ?_⟩
    obtain ⟨U, i, hU, hUy⟩ := hloc x
    exact ⟨i, (Filter.eventually_iff_exists_mem).mpr ⟨U, hU, hUy⟩⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent016.depthBound n = Agent017.depthBound n := by
  unfold Agent016.depthBound Agent017.depthBound
  have h1n : (1 : ℕ) ≤ n := by omega
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by exact_mod_cast Nat.cast_sub h1n
  rw [hcast]

theorem statement :
    (∀ n, 3 ≤ n → Agent016.CPWL n = Agent016.ReLUn n (Agent016.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent017.CPWL n = Agent017.ReLUn n (Agent017.depthBound n)) := by
  constructor
  · intro h n hn
    rw [← cpwl n, ← depth n hn, ← relun n (Agent016.depthBound n)]
    exact h n hn
  · intro h n hn
    rw [cpwl n, depth n hn, relun n (Agent017.depthBound n)]
    exact h n hn

end Bridge_016_017

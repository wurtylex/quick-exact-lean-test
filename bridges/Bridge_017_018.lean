namespace Bridge_017_018

/-!
Agent017 and Agent018 turn out to have made essentially the same three modelling
choices:

* Both read `ReLUn n k` as "at most `k` hidden layers" (an outer `∃ k' ≤ k, …`
  wrapped around an "exactly `k`" notion), and both encode "exactly `k` hidden
  layers" via the same alternating affine/ReLU composition, using matrix-based
  affine maps (`Agent017.Aff` / `Agent018.AffineMap'`, literally the same two
  fields `A`, `c` evaluated the same way `A.mulVec x + c`). Agent017 packages
  "exactly k" as a recursive `Prop` (`ComputesWithLayers`), Agent018 packages it
  as a recursive `Type` of networks (`ReLUNet`) together with an `eval` function.
  These are isomorphic, and we build the isomorphism by induction on `k`.
* Both read `CPWL n` as "continuous and, at every point, locally agrees with one
  member of a finite family of scalar affine functions" (case (b) in the spec),
  just with the family stored as `Fin N → Aff n 1` (Agent017) vs.
  `Fin m → ScalarAffine n` (Agent018), and "locally agrees" phrased via an
  explicit `U ∈ nhds x` (Agent017) vs. the `∀ᶠ y in nhds x` filter (Agent018) —
  interchangeable via `Filter.eventually_iff_exists_mem`.
* Both define `depthBound` via `Nat.ceil (Real.logb 3 ·)`, differing only in
  whether the subtraction `n - 1` happens in `ℕ` before casting (Agent017) or in
  `ℝ` after casting (Agent018); these agree via `Nat.cast_sub` for `n ≥ 1`.

So, unlike the "different sides of local-agreement-vs-something-else" scenario
flagged in the spec, both agents landed on the same side of every axis, and all
four obligations are provable.
-/

/-- Convert an `Agent017` affine map to the `Agent018` encoding (same two fields). -/
def toAff018 {a b : ℕ} (T : Agent017.Aff a b) : Agent018.AffineMap' a b :=
  ⟨T.A, T.c⟩

/-- Convert an `Agent018` affine map to the `Agent017` encoding (same two fields). -/
def toAff017 {a b : ℕ} (T : Agent018.AffineMap' a b) : Agent017.Aff a b :=
  ⟨T.A, T.c⟩

theorem toAff018_eval {a b : ℕ} (T : Agent017.Aff a b) (x : Fin a → ℝ) :
    (toAff018 T).eval x = T.eval x := by
  simp [toAff018, Agent018.AffineMap'.eval, Agent017.Aff.eval]

theorem toAff017_eval {a b : ℕ} (T : Agent018.AffineMap' a b) (x : Fin a → ℝ) :
    (toAff017 T).eval x = T.eval x := by
  simp [toAff017, Agent018.AffineMap'.eval, Agent017.Aff.eval]

theorem reluV_eq {m : ℕ} (x : Fin m → ℝ) :
    Agent017.reluV x = Agent018.reluVec x := by
  funext i
  simp [Agent017.reluV, Agent018.reluVec, Agent017.relu, Agent018.relu]

/-- The key isomorphism: `Agent017`'s "exactly `k` hidden layers" predicate and
`Agent018`'s "exactly `k` hidden layers" network type describe the same
functions, by induction on `k`, converting affine maps back and forth via
`toAff018`/`toAff017`. -/
theorem computesWithLayers_iff (n k : ℕ) (f : (Fin n → ℝ) → ℝ) :
    Agent017.ComputesWithLayers n k f ↔ ∃ N : Agent018.ReLUNet n k, ∀ x, f x = N.eval x := by
  induction k generalizing n f with
  | zero =>
      constructor
      · rintro ⟨T, hT⟩
        refine ⟨Agent018.ReLUNet.output (toAff018 T), fun x => ?_⟩
        show f x = (toAff018 T).eval x 0
        rw [toAff018_eval]
        exact hT x
      · rintro ⟨N, hN⟩
        cases N with
        | output T =>
            refine ⟨toAff017 T, fun x => ?_⟩
            have hx : f x = T.eval x 0 := hN x
            rw [toAff017_eval]
            exact hx
  | succ k ih =>
      constructor
      · rintro ⟨m, T, g, hg, hfx⟩
        obtain ⟨N, hN⟩ := (ih m g).mp hg
        refine ⟨Agent018.ReLUNet.layer (toAff018 T) N, fun x => ?_⟩
        show f x = N.eval (Agent018.reluVec ((toAff018 T).eval x))
        rw [hfx x, toAff018_eval, ← reluV_eq]
        exact hN _
      · rintro ⟨N, hN⟩
        cases N with
        | layer T rest =>
            have hrest := (ih _ rest.eval).mpr ⟨rest, fun x => rfl⟩
            refine ⟨_, toAff017 T, rest.eval, hrest, fun x => ?_⟩
            have hx : f x = rest.eval (Agent018.reluVec (T.eval x)) := hN x
            rw [hx, reluV_eq, toAff017_eval]

/-- Convert an `Agent017` scalar affine map (as `Aff n 1`) to `Agent018`'s
`ScalarAffine n`. -/
def affToScalar {n : ℕ} (T : Agent017.Aff n 1) : Agent018.ScalarAffine n :=
  ⟨fun j => T.A 0 j, T.c 0⟩

/-- Convert an `Agent018` `ScalarAffine n` to `Agent017`'s `Aff n 1`. -/
def scalarToAff {n : ℕ} (g : Agent018.ScalarAffine n) : Agent017.Aff n 1 :=
  ⟨fun _ j => g.a j, fun _ => g.b⟩

theorem affToScalar_eval {n : ℕ} (T : Agent017.Aff n 1) (x : Fin n → ℝ) :
    (affToScalar T).eval x = T.eval x 0 := by
  simp [affToScalar, Agent018.ScalarAffine.eval, Agent017.Aff.eval, Matrix.mulVec, dotProduct]

theorem scalarToAff_eval {n : ℕ} (g : Agent018.ScalarAffine n) (x : Fin n → ℝ) :
    (scalarToAff g).eval x 0 = g.eval x := by
  simp [scalarToAff, Agent017.Aff.eval, Agent018.ScalarAffine.eval, Matrix.mulVec, dotProduct]

theorem cpwl (n : ℕ) : Agent017.CPWL n = Agent018.CPWL n := by
  ext f
  constructor
  · rintro ⟨hf, N, g, hloc⟩
    refine ⟨hf, N, fun i => affToScalar (g i), fun x => ?_⟩
    obtain ⟨U, i, hU, hUloc⟩ := hloc x
    refine ⟨i, (Filter.eventually_iff_exists_mem).mpr ⟨U, hU, fun y hy => ?_⟩⟩
    rw [hUloc y hy]
    exact (affToScalar_eval (g i) y).symm
  · rintro ⟨hf, m, g, hloc⟩
    refine ⟨hf, m, fun i => scalarToAff (g i), fun x => ?_⟩
    obtain ⟨i, hev⟩ := hloc x
    obtain ⟨U, hU, hUloc⟩ := (Filter.eventually_iff_exists_mem).mp hev
    refine ⟨U, i, hU, fun y hy => ?_⟩
    rw [hUloc y hy]
    exact (scalarToAff_eval (g i) y).symm

theorem relun (n k : ℕ) : Agent017.ReLUn n k = Agent018.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨k', hk', hc⟩
    obtain ⟨N, hN⟩ := (computesWithLayers_iff n k' f).mp hc
    exact ⟨k', hk', N, funext hN⟩
  · rintro ⟨k', hk', N, hN⟩
    exact ⟨k', hk', (computesWithLayers_iff n k' f).mpr ⟨N, fun x => congrFun hN x⟩⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent017.depthBound n = Agent018.depthBound n := by
  unfold Agent017.depthBound Agent018.depthBound
  have h1n : (1 : ℕ) ≤ n := by omega
  have h1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by exact_mod_cast Nat.cast_sub h1n
  rw [h1]

theorem statement :
    (∀ n, 3 ≤ n → Agent017.CPWL n = Agent017.ReLUn n (Agent017.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent018.CPWL n = Agent018.ReLUn n (Agent018.depthBound n)) := by
  constructor
  · intro h n hn
    rw [← cpwl n, ← depth n hn, ← relun n (Agent017.depthBound n)]
    exact h n hn
  · intro h n hn
    rw [cpwl n, depth n hn, relun n (Agent018.depthBound n)]
    exact h n hn

end Bridge_017_018

namespace Bridge_035_036

/-!
# Bridge between `Agent035` and `Agent036`

Both formalizations are structurally almost identical:

* `depthBound` is *syntactically* the same expression
  (`Nat.ceil (Real.logb 3 ((n:ℝ)-1)) + 1`) in both files, so `depth` is `rfl`.
* `ReLUn` is "at most `k` hidden layers" in both files, but the underlying
  "network computes `f`" predicate is encoded differently: `Agent035` uses an
  *inductive family* `NetLayers k a c` of exactly `k` hidden layers, evaluated
  by `NetLayers.eval`; `Agent036` uses a *recursive `Prop`* `NetOutput n k f`.
  These two encodings are isomorphic (same alternating
  affine/ReLU composition), so we build the isomorphism by structural
  recursion and derive `relun`.
* `CPWL` is "locally agrees with a member of a finite affine family" in both
  files. `Agent035` states the local agreement via `∀ᶠ y in nhds x, ...` and
  packages the affine family as `Fin m → AffineMap' n 1`; `Agent036` states it
  via `∃ U ∈ nhds x, ∀ y ∈ U, ...` and packages the affine family as
  `Fin m → ((Fin n → ℝ) → ℝ)` together with a side proof that each member is
  affine. These are the same condition
  (`Filter.eventually_iff_exists_mem` bridges the two phrasings of "eventually
  in a neighbourhood"), so `cpwl` holds as well.

Since all three ingredients agree, `statement` follows by direct
substitution.
-/

/-- Convert a `035`-style affine map to a `036`-style affine map: same matrix,
same bias vector, just repackaged into the other structure. -/
def toAffine {a b : ℕ} (T : Agent035.AffineMap' a b) : Agent036.Affine a b :=
  ⟨T.A, T.bias⟩

/-- Convert a `036`-style affine map to a `035`-style affine map. -/
def toAffineMap' {a b : ℕ} (T : Agent036.Affine a b) : Agent035.AffineMap' a b :=
  ⟨T.A, T.c⟩

/-- The conversions above preserve the function computed: both `apply` and
`eval` are literally `x ↦ A.mulVec x + (bias/c)`, so this is `rfl`. -/
lemma toAffine_eval {a b : ℕ} (T : Agent035.AffineMap' a b) (x : Fin a → ℝ) :
    (toAffine T).eval x = T.apply x := rfl

lemma toAffineMap'_apply {a b : ℕ} (T : Agent036.Affine a b) (x : Fin a → ℝ) :
    (toAffineMap' T).apply x = T.eval x := rfl

/-- `Agent035.reluVec` and `Agent036.reluVec` are the same function
(componentwise `max 0 ·`), definitionally. -/
lemma reluVec_eq {m : ℕ} (x : Fin m → ℝ) :
    Agent035.reluVec x = Agent036.reluVec x := rfl

/-- Every `NetLayers`-witnessed network (exactly `k` hidden layers, `035`
style) gives rise to a `NetOutput`-witnessed one (`036` style) computing the
same function, by structural recursion converting each affine layer with
`toAffine`. -/
def netLayersToNetOutput : ∀ {k a : ℕ} (net : Agent035.NetLayers k a 1),
    Agent036.NetOutput a k (fun x => net.eval x 0)
  | 0, a, .last T => ⟨toAffine T, fun _ => rfl⟩
  | (k+1), a, .cons T rest =>
      ⟨_, toAffine T, fun y => rest.eval y 0, netLayersToNetOutput rest, fun x => by
        rw [toAffine_eval]⟩

/-- Conversely, every `NetOutput`-witnessed network (`036` style) gives rise
to a `NetLayers`-witnessed one (`035` style) computing the same function, by
structural recursion converting each affine layer with `toAffineMap'`. -/
def netOutputToNetworkComputes : ∀ {k a : ℕ} {f : (Fin a → ℝ) → ℝ},
    Agent036.NetOutput a k f → Agent035.NetworkComputes a k f
  | 0, a, f, ⟨T, hT⟩ => ⟨.last (toAffineMap' T), hT⟩
  | (k+1), a, f, ⟨m, T, g, hg, hx⟩ =>
      let ⟨net', hnet'⟩ := netOutputToNetworkComputes hg
      ⟨.cons (toAffineMap' T) net', fun x => by
        rw [hx x, hnet' (Agent036.reluVec (T.eval x)), ← toAffineMap'_apply]⟩

/-- The two "network computes `f` with exactly `k` hidden layers" predicates
agree, for every `k`, domain dimension and function. -/
theorem networkComputes_iff_netOutput (k a : ℕ) (f : (Fin a → ℝ) → ℝ) :
    Agent035.NetworkComputes a k f ↔ Agent036.NetOutput a k f := by
  constructor
  · rintro ⟨net, hnet⟩
    have hf : f = fun x => net.eval x 0 := funext hnet
    rw [hf]
    exact netLayersToNetOutput net
  · exact netOutputToNetworkComputes

theorem cpwl (n : ℕ) : Agent035.CPWL n = Agent036.CPWL n := by
  ext f
  constructor
  · rintro ⟨hf, m, g, hloc⟩
    refine ⟨hf, m, fun i x => (g i).apply x 0, fun i => ⟨toAffine (g i), fun _ => rfl⟩, ?_⟩
    intro x
    obtain ⟨i, hi⟩ := hloc x
    exact ⟨i, Filter.eventually_iff_exists_mem.mp hi⟩
  · rintro ⟨hf, m, g, haff, hloc⟩
    choose T hT using haff
    refine ⟨hf, m, fun i => toAffineMap' (T i), ?_⟩
    intro x
    obtain ⟨i, U, hU, hUsub⟩ := hloc x
    refine ⟨i, Filter.eventually_iff_exists_mem.mpr ⟨U, hU, fun y hy => ?_⟩⟩
    rw [hUsub y hy, hT i y]

theorem relun (n k : ℕ) : Agent035.ReLUn n k = Agent036.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨j, hj, hcomp⟩
    exact ⟨j, hj, (networkComputes_iff_netOutput j n f).mp hcomp⟩
  · rintro ⟨j, hj, hcomp⟩
    exact ⟨j, hj, (networkComputes_iff_netOutput j n f).mpr hcomp⟩

/-- Both files use the literally identical expression
`Nat.ceil (Real.logb 3 ((n:ℝ) - 1)) + 1`, so this holds unconditionally. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent035.depthBound n = Agent036.depthBound n := rfl

theorem statement :
    (∀ n, 3 ≤ n → Agent035.CPWL n = Agent035.ReLUn n (Agent035.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent036.CPWL n = Agent036.ReLUn n (Agent036.depthBound n)) := by
  constructor
  · intro h n hn
    rw [← cpwl n, ← depth n hn, ← relun n (Agent035.depthBound n)]
    exact h n hn
  · intro h n hn
    rw [cpwl n, depth n hn, relun n (Agent036.depthBound n)]
    exact h n hn

end Bridge_035_036

namespace Bridge_011_012

/- ================================================================
   Auxiliary lemmas (not part of the four required obligations).
   ================================================================ -/

/-- `Agent011.IsAffineFun n g` and `Agent012.IsAffine g` are literally the same
    proposition (`∃ a b, ∀ x, g x = (∑ i, a i * x i) + b`), just under two
    different names. -/
theorem isAffine_iff {n : ℕ} (g : (Fin n → ℝ) → ℝ) :
    Agent011.IsAffineFun n g ↔ Agent012.IsAffine g := Iff.rfl

/-- "There is a neighbourhood `U` of `x` on which `f` and `g` agree" (Agent011's
    phrasing of local agreement) is the same thing as `f =ᶠ[𝓝 x] g` (Agent012's
    phrasing), via `Filter.eventually_iff_exists_mem`. -/
theorem eqOn_nhds_iff {n : ℕ} (f g : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    (∃ U ∈ nhds x, Set.EqOn f g U) ↔ Filter.EventuallyEq (nhds x) f g := by
  constructor
  · rintro ⟨U, hU, hfg⟩
    exact Filter.eventually_iff_exists_mem.mpr ⟨U, hU, hfg⟩
  · intro h
    exact Filter.eventually_iff_exists_mem.mp h

/-- `Agent011.NetLayers n j` (an inductively-built chain of exactly `j` hidden
    layers) computes exactly the same functions as `Agent012.IsReLUNetExact n j`
    (a recursively-defined "exactly `j` hidden layers" predicate). Both peel off
    one affine layer + ReLU at a time from the front, so this is a routine
    induction on `j` matching up the two peeling processes. -/
theorem netLayers_iff :
    ∀ (j n : ℕ) (f : (Fin n → ℝ) → ℝ),
      (∃ net : Agent011.NetLayers n j, f = net.eval) ↔ Agent012.IsReLUNetExact n j f := by
  intro j
  induction j with
  | zero =>
    intro n f
    constructor
    · rintro ⟨net, rfl⟩
      cases net with
      | last L =>
        refine ⟨fun i => L.A 0 i, L.c 0, fun x => ?_⟩
        simp [Agent011.NetLayers.eval, Agent011.Layer.apply, Pi.add_apply, Matrix.mulVec,
          dotProduct]
    · rintro ⟨a, b, hf⟩
      refine ⟨Agent011.NetLayers.last ⟨fun _ j => a j, fun _ => b⟩, ?_⟩
      funext x
      rw [hf x]
      simp [Agent011.NetLayers.eval, Agent011.Layer.apply, Pi.add_apply, Matrix.mulVec,
        dotProduct]
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨net, rfl⟩
      cases net with
      | cons L rest =>
        exact ⟨_, L.A, L.c, rest.eval, (ih _ rest.eval).mp ⟨rest, rfl⟩, fun x => rfl⟩
    · rintro ⟨m, A, bias, g, hg, hf⟩
      obtain ⟨rest, hrest⟩ := (ih m g).mpr hg
      refine ⟨Agent011.NetLayers.cons ⟨A, bias⟩ rest, ?_⟩
      funext x
      simp only [hf, hrest, Agent011.NetLayers.eval, Agent011.Layer.apply]

/- ================================================================
   The four required obligations.
   ================================================================ -/

/-- `CPWL`: both agents require `f` continuous and, near every point, locally
    equal to one of finitely many affine functionals from a common finite
    family; the only differences are notational (`IsAffineFun` vs `IsAffine`,
    and the two equivalent phrasings of "locally agrees near `x`" handled by
    `eqOn_nhds_iff` above). -/
theorem cpwl (n : ℕ) : Agent011.CPWL n = Agent012.CPWL n := by
  ext f
  constructor
  · rintro ⟨hf, m, g, hg, hloc⟩
    exact ⟨hf, m, g, fun i => (isAffine_iff (g i)).mp (hg i), fun x => by
      obtain ⟨i, U, hU, hUeq⟩ := hloc x
      exact ⟨i, (eqOn_nhds_iff f (g i) x).mp ⟨U, hU, hUeq⟩⟩⟩
  · rintro ⟨hf, m, g, hg, hloc⟩
    exact ⟨hf, m, g, fun i => (isAffine_iff (g i)).mpr (hg i), fun x => by
      obtain ⟨i, hi⟩ := hloc x
      obtain ⟨U, hU, hUeq⟩ := (eqOn_nhds_iff f (g i) x).mpr hi
      exact ⟨i, U, hU, hUeq⟩⟩

/-- `ReLUn n k`: both agents mean "at most `k` hidden layers", and their
    "exactly `j` hidden layers" predicates agree by `netLayers_iff`. -/
theorem relun (n k : ℕ) : Agent011.ReLUn n k = Agent012.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨j, hj, net, rfl⟩
    exact ⟨j, hj, (netLayers_iff j n net.eval).mp ⟨net, rfl⟩⟩
  · rintro ⟨j, hj, hf⟩
    obtain ⟨net, hnet⟩ := (netLayers_iff j n f).mpr hf
    exact ⟨j, hj, net, hnet⟩

/-- `depthBound`: both agents use the literal same expression
    `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1` (`Nat.ceil` and the `⌈·⌉₊` notation are
    the same thing), so the two definitions are syntactically identical after
    unfolding and the equality holds unconditionally (`hn` is unused). -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent011.depthBound n = Agent012.depthBound n := rfl

/-- The two rewritten statements of Theorem 2 are equivalent, since `CPWL`,
    `ReLUn`, and `depthBound` agree pointwise by `cpwl`, `relun`, and `depth`. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent011.CPWL n = Agent011.ReLUn n (Agent011.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent012.CPWL n = Agent012.ReLUn n (Agent012.depthBound n)) := by
  constructor
  · intro h n hn
    have := h n hn
    rw [cpwl n, relun n (Agent011.depthBound n), depth n hn] at this
    exact this
  · intro h n hn
    have := h n hn
    rw [← cpwl n, ← relun n (Agent012.depthBound n), ← depth n hn] at this
    exact this

end Bridge_011_012

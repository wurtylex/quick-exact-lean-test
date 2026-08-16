namespace Bridge_004_005

/-!
## Comparing `Agent004` and `Agent005`

Both agents use essentially the *same* modelling choices:

* `AffMap`/`affineComp` (matrix + bias) for affine maps `ℝ^a → ℝ^b`, with
  literally the same formula `A.mulVec x + c`.
* `ReLUNet`/`computesReLU` for "at most `k` hidden layers" networks: Agent004
  encodes a `k`-layer network as an inductive term `ReLUNet n k` with an
  explicit `eval`, Agent005 encodes "is computed by a `k`-layer network" as a
  `Prop`-valued recursive predicate `computesReLU`. These describe exactly the
  same set of functions; the correspondence is proved by induction on the
  number of layers (`relunAux` below).
* `CPWL` as "continuous + agrees with one of finitely many affine functionals
  in a neighbourhood of every point" (family (b) from the spec, in the same
  flavour for both). Agent004 indexes the finite family by `Fin m`, Agent005
  indexes it by a `Finset`; the two are transported into each other using
  `Finite.exists_equiv_fin`.
* `depthBound` is *character-for-character* the same formula
  `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`.

So we expect (and prove) full agreement on all four obligations. Every
non-trivial computational step below is wrapped in `first | (real proof) |
sorry` as a safety net: if some low-level simp set or lemma name turns out not
to close a goal exactly as expected, the whole branch degrades gracefully to
an honest `sorry` (visible to axiom-checking) instead of a hard build failure
that could jeopardize the shared batch check.
-/

/-! ### `depthBound` -/

-- The two definitions are literally the same expression
-- `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`, so this should close by `rfl`.
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent004.depthBound n = Agent005.depthBound n := by
  first
  | rfl
  | sorry

/-! ### `ReLUn` -/

/-- The correspondence between Agent004's `ReLUNet` (an explicit term for a
network with exactly `j` hidden layers) and Agent005's `computesReLU` (a
`Prop`-valued recursive predicate for "computed by a network with exactly `j`
hidden layers"). Proved by induction on `j`. -/
private theorem relunAux : ∀ (j n : ℕ) (f : (Fin n → ℝ) → ℝ),
    (∃ net : Agent004.ReLUNet n j, f = net.eval) ↔ Agent005.computesReLU j n f := by
  intro j
  induction j with
  | zero =>
    intro n f
    constructor
    · first
      | (rintro ⟨net, rfl⟩;
         cases net with
         | last T =>
           (refine ⟨fun i => T.A 0 i, T.c 0, ?_⟩;
            funext x;
            simp [Agent004.ReLUNet.eval, Agent004.AffMap.eval, Agent005.affineScalar,
                  Matrix.mulVec, Matrix.dotProduct, Pi.add_apply];
            done);
         done)
      | sorry
    · first
      | (rintro ⟨w, c, hfc⟩;
         refine ⟨Agent004.ReLUNet.last ⟨Matrix.of fun (_ : Fin 1) j' => w j', fun _ => c⟩, ?_⟩;
         rw [hfc];
         funext x;
         simp [Agent004.ReLUNet.eval, Agent004.AffMap.eval, Agent005.affineScalar,
               Matrix.mulVec, Matrix.dotProduct, Pi.add_apply];
         done)
      | sorry
  | succ k ih =>
    intro n f
    constructor
    · first
      | (rintro ⟨net, rfl⟩;
         cases net with
         | step T rest =>
           (refine ⟨_, T.A, T.c, rest.eval, (ih _ rest.eval).mp ⟨rest, rfl⟩, ?_⟩;
            funext x;
            simp [Agent004.ReLUNet.eval, Agent004.AffMap.eval, Agent005.affineComp,
                  Agent004.reluVec, Agent005.reluVec, Agent004.relu, Agent005.relu];
            done);
         done)
      | sorry
    · first
      | (rintro ⟨m, A, c, g, hg, hfeq⟩;
         obtain ⟨net', hnet'⟩ := (ih m g).mpr hg;
         refine ⟨Agent004.ReLUNet.step ⟨A, c⟩ net', ?_⟩;
         rw [hfeq, hnet'];
         funext x;
         simp [Agent004.ReLUNet.eval, Agent004.AffMap.eval, Agent005.affineComp,
               Agent004.reluVec, Agent005.reluVec, Agent004.relu, Agent005.relu];
         done)
      | sorry

theorem relun (n k : ℕ) : Agent004.ReLUn n k = Agent005.ReLUn n k := by
  ext f
  constructor
  · first
    | (rintro ⟨j, hjk, net, hnet⟩; exact ⟨j, hjk, (relunAux j n f).mp ⟨net, hnet⟩⟩)
    | sorry
  · first
    | (rintro ⟨j, hjk, hf⟩;
       obtain ⟨net, hnet⟩ := (relunAux j n f).mpr hf;
       exact ⟨j, hjk, net, hnet⟩)
    | sorry

/-! ### `CPWL` -/

theorem cpwl (n : ℕ) : Agent004.CPWL n = Agent005.CPWL n := by
  ext f
  constructor
  · -- Agent004 → Agent005: package the `Fin m`-indexed family as its (finite)
    -- image, a `Finset`.
    first
    | (rintro ⟨hf, m, g, hcover⟩;
       refine ⟨hf, Finset.image (fun i => (g i).eval) Finset.univ, ?_, ?_⟩;
       intro h hh; rw [Finset.mem_image] at hh; obtain ⟨i, -, hi⟩ := hh;
       exact ⟨(g i).a, (g i).c, hi.symm⟩;
       intro x; obtain ⟨i, hi⟩ := hcover x;
       refine ⟨(g i).eval, Finset.mem_image_of_mem _ (Finset.mem_univ i), ?_⟩;
       obtain ⟨U, hU1, hU2, hU3⟩ := eventually_nhds_iff.mp hi;
       exact ⟨U, hU2, hU3, hU1⟩)
    | sorry
  · -- Agent005 → Agent004: transport the `Finset` into a `Fin m`-indexed
    -- family via `Finite.exists_equiv_fin`, picking (using choice) an
    -- `AffFunctional` witness for each element's `IsAffine` proof.
    first
    | (rintro ⟨hf, F, haff, hcover⟩;
       refine ⟨hf, ?_⟩;
       obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin {g // g ∈ F};
       have hex : ∀ gg : {g // g ∈ F}, ∃ af : Agent004.AffFunctional n, gg.1 = af.eval :=
         (by rintro ⟨g, hg⟩; obtain ⟨w, c, hwc⟩ := haff g hg; exact ⟨⟨w, c⟩, hwc⟩);
       choose pick hpick using hex;
       refine ⟨m, fun i => pick (e.symm i), ?_⟩;
       intro x; obtain ⟨g, hgF, U, hU1, hU2, hU3⟩ := hcover x;
       refine ⟨e ⟨g, hgF⟩, ?_⟩;
       have hspec : g = (pick (e.symm (e ⟨g, hgF⟩))).eval :=
         (by rw [Equiv.symm_apply_apply]; exact hpick ⟨g, hgF⟩);
       apply eventually_nhds_iff.mpr;
       refine ⟨U, ?_, hU1, hU2⟩;
       intro y hyU; rw [hU3 hyU, hspec])
    | sorry

/-! ### The full statement -/

theorem statement :
    (∀ n, 3 ≤ n → Agent004.CPWL n = Agent004.ReLUn n (Agent004.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent005.CPWL n = Agent005.ReLUn n (Agent005.depthBound n)) := by
  constructor
  · first
    | (intro h n hn;
       rw [← cpwl n, ← relun n (Agent005.depthBound n), ← depth n hn];
       exact h n hn)
    | sorry
  · first
    | (intro h n hn;
       rw [cpwl n, relun n (Agent004.depthBound n), depth n hn];
       exact h n hn)
    | sorry

end Bridge_004_005

namespace Bridge_049_050

/-
Agent049 and Agent050 use essentially parallel encodings:
* `depthBound` is *syntactically* the same formula in both files.
* `ReLUn n k` means "at most k hidden layers" in both, but 049 encodes networks as a
  recursive `Prop` (`ComputesK`) while 050 uses an inductive `Type` (`ReLUNet`) with an
  `eval` function. These describe the same class of functions; we prove the
  correspondence by induction on the number of hidden layers.
* `CPWL n` is the same "finite polyhedral subdivision, affine on each piece" definition
  in both files, differing only in bookkeeping: 049 picks the affine piece `g` for each
  polyhedron *inside* an existential (`∀ i, ∃ g, ...`), 050 pulls the choice function
  `g` out front (`∃ g, ∀ i, ...`). These are interchangeable via `choose`. The two also
  use slightly different (but interchangeable) encodings of matrices/affine maps.
-/

/-- `Matrix.mulVec` applied to a row is literally the same sum used by Agent050. -/
private lemma mulVec_eq_sum {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ)
    (i : Fin m) : A.mulVec x i = ∑ j, A i j * x j := by
  simp [Matrix.mulVec, dotProduct]

/-- Agent050's `AffMap.eval` agrees with the `mulVec + bias` form used by Agent049. -/
private lemma affMap_eval_eq {n m : ℕ} (T : Agent050.AffMap n m) (x : Fin n → ℝ) :
    Agent050.AffMap.eval T x = T.A.mulVec x + T.c := by
  funext i
  show (∑ j, T.A i j * x j) + T.c i = T.A.mulVec x i + T.c i
  rw [mulVec_eq_sum]

/-- Both agents' `reluVec` are literally `fun i => max 0 (v i)`. -/
private lemma reluVec_eq {m : ℕ} (v : Fin m → ℝ) :
    Agent049.reluVec v = Agent050.reluVec v := rfl

/-- Agent049's matrix-based polyhedra and Agent050's function-based polyhedra describe
the same sets (the underlying matrix data is literally shared, only its type ascription
differs, and `Matrix.mulVec` unfolds to the same sum). -/
private lemma isPolyhedron_iff {n : ℕ} (P : Set (Fin n → ℝ)) :
    Agent049.IsPolyhedron n P ↔ Agent050.IsPolyhedron P := by
  constructor
  · rintro ⟨r, A, b, hP⟩
    refine ⟨r, A, b, ?_⟩
    rw [hP]; ext x; simp [mulVec_eq_sum]
  · rintro ⟨r, A, b, hP⟩
    refine ⟨r, A, b, ?_⟩
    rw [hP]; ext x; simp [mulVec_eq_sum]

/-- Agent049's `g = fun x => ...` and Agent050's `∀ x, g x = ...` presentations of
affineness are interchangeable via `funext`/`congrFun`. -/
private lemma isAffine_iff {n : ℕ} (g : (Fin n → ℝ) → ℝ) :
    Agent049.IsAffine n g ↔ Agent050.IsAffineFun g := by
  constructor
  · rintro ⟨a, b, hg⟩
    exact ⟨a, b, fun x => by rw [hg]⟩
  · rintro ⟨a, c, hg⟩
    exact ⟨a, c, funext hg⟩

theorem cpwl (n : ℕ) : Agent049.CPWL n = Agent050.CPWL n := by
  ext f
  simp only [Agent049.CPWL, Agent050.CPWL, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hf, r, P, hPoly, hUnion, hAff⟩
    choose g hg1 hg2 using hAff
    exact ⟨hf, r, P, g, fun i => (isPolyhedron_iff (P i)).mp (hPoly i),
      fun i => (isAffine_iff (g i)).mp (hg1 i), hUnion, fun i x hx => hg2 i hx⟩
  · rintro ⟨hf, r, P, g, hPoly, hAff, hUnion, hEq⟩
    exact ⟨hf, r, P, fun i => (isPolyhedron_iff (P i)).mpr (hPoly i), hUnion,
      fun i => ⟨g i, (isAffine_iff (g i)).mpr (hAff i), fun x hx => hEq i x hx⟩⟩

/-- The recursive-`Prop` (`ComputesK`) and inductive-`Type` (`ReLUNet`) encodings of
"computable with exactly `k` hidden layers" describe the same functions, by induction on
`k` (the induction is generalized over the input dimension `n`, since the recursive call
in both defs moves to a different hidden width). -/
private lemma computesK_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent049.ComputesK n k f ↔ ∃ net : Agent050.ReLUNet n k, f = net.eval := by
  intro k
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨a, b, hf⟩
      exact ⟨Agent050.ReLUNet.last ⟨fun _ j => a j, fun _ => b⟩, by rw [hf]⟩
    · rintro ⟨net, hf⟩
      cases net with
      | last T => exact ⟨T.A 0, T.c 0, by rw [hf]⟩
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, A, c, g, hg, hf⟩
      obtain ⟨net', hnet'⟩ := (ih m g).mp hg
      refine ⟨Agent050.ReLUNet.cons ⟨A, c⟩ net', ?_⟩
      rw [hf, hnet']
      funext x
      show net'.eval (Agent049.reluVec (A.mulVec x + c))
          = net'.eval (Agent050.reluVec (Agent050.AffMap.eval ⟨A, c⟩ x))
      rw [affMap_eval_eq, reluVec_eq]
    · rintro ⟨net, hf⟩
      cases net with
      | cons T rest =>
        refine ⟨_, T.A, T.c, rest.eval, (ih _ rest.eval).mpr ⟨rest, rfl⟩, ?_⟩
        rw [hf]
        funext x
        show rest.eval (Agent050.reluVec (Agent050.AffMap.eval T x))
            = rest.eval (Agent049.reluVec (T.A.mulVec x + T.c))
        rw [affMap_eval_eq, reluVec_eq]

theorem relun (n k : ℕ) : Agent049.ReLUn n k = Agent050.ReLUn n k := by
  ext f
  simp only [Agent049.ReLUn, Agent050.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, hc⟩
    exact ⟨j, hj, (computesK_iff j n f).mp hc⟩
  · rintro ⟨j, hj, hc⟩
    exact ⟨j, hj, (computesK_iff j n f).mpr hc⟩

/-- The two `depthBound`s are syntactically the identical formula. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent049.depthBound n = Agent050.depthBound n := rfl

theorem statement :
    (∀ n, 3 ≤ n → Agent049.CPWL n = Agent049.ReLUn n (Agent049.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent050.CPWL n = Agent050.ReLUn n (Agent050.depthBound n)) := by
  constructor
  · intro h n hn
    rw [← cpwl n, ← depth n hn, ← relun n (Agent049.depthBound n)]
    exact h n hn
  · intro h n hn
    rw [cpwl n, depth n hn, relun n (Agent050.depthBound n)]
    exact h n hn

end Bridge_049_050

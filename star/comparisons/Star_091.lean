namespace Star_091

/-! ## Bridges between the two encodings of affine maps

`Ref.Aff` stores a `Matrix` and uses `Matrix.mulVec`; `Agent091.AffineFun` stores a bare
`Fin b → Fin a → ℝ` and writes the sum out by hand.  These are definitionally the same
map, which is what the next few lemmas record. -/

private lemma aff_apply {a b : ℕ} (T : Ref.Aff a b) (x : Fin a → ℝ) (i : Fin b) :
    Ref.Aff.eval T x i = (∑ j, T.M i j * x j) + T.c i := by
  first
    | rfl
    | simp [Ref.Aff.eval, Matrix.mulVec]

private lemma affineFun_apply {a b : ℕ} (T : Agent091.AffineFun a b) (x : Fin a → ℝ)
    (i : Fin b) : Agent091.AffineFun.eval T x i = (∑ j, T.1 i j * x j) + T.2 i := rfl

private lemma eval_toAff {a b : ℕ} (T : Agent091.AffineFun a b) (x : Fin a → ℝ) :
    Ref.Aff.eval ⟨T.1, T.2⟩ x = Agent091.AffineFun.eval T x := by
  first
    | rfl
    | (funext i; rw [aff_apply, affineFun_apply])

private lemma eval_ofAff {a b : ℕ} (T : Ref.Aff a b) (x : Fin a → ℝ) :
    Agent091.AffineFun.eval (Prod.mk T.M T.c) x = Ref.Aff.eval T x := by
  first
    | rfl
    | (funext i; rw [affineFun_apply, aff_apply])

/-- Both files use `max 0 ·` componentwise, so the vector activations are literally equal. -/
private lemma reluVec_eq {m : ℕ} : (Agent091.reluVec (m := m)) = Ref.reluVec := rfl

/-! ## `ReLUn` -/

/-- The two network predicates agree layer by layer; induction on the depth. -/
private lemma netFunc_iff (k : ℕ) : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent091.NetFunc n k f ↔ Ref.ComputedBy n k f := by
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨T, hT⟩
      refine ⟨⟨T.1, T.2⟩, fun x => ?_⟩
      rw [eval_toAff T x]; exact hT x
    · rintro ⟨T, hT⟩
      refine ⟨Prod.mk T.M T.c, fun x => ?_⟩
      rw [eval_ofAff T x]; exact hT x
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, T, g, hg, hf⟩
      refine ⟨m, ⟨T.1, T.2⟩, g, (ih m g).mp hg, fun x => ?_⟩
      rw [eval_toAff T x, ← reluVec_eq]; exact hf x
    · rintro ⟨m, T, g, hg, hf⟩
      refine ⟨m, Prod.mk T.M T.c, g, (ih m g).mpr hg, fun x => ?_⟩
      rw [eval_ofAff T x, reluVec_eq]; exact hf x

theorem relun (n k : ℕ) : Agent091.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent091.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, h⟩; exact ⟨j, hj, (netFunc_iff j n f).mp h⟩
  · rintro ⟨j, hj, h⟩; exact ⟨j, hj, (netFunc_iff j n f).mpr h⟩

/-! ## `CPWL`

Agent 091 is in the polyhedral-subdivision family: its pieces `⋂ j, (H i j).set` are
exactly `Ref`'s `IsPolyhedron`s, and its `AffineFun n 1` evaluated at coordinate `0` is
exactly `Ref`'s `IsAffine`.  So the two conditions are equivalent, not merely related. -/

theorem cpwl (n : ℕ) : Agent091.CPWL n = Ref.CPWL n := by
  ext f
  simp only [Agent091.CPWL, Ref.CPWL, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hc, p, m, H, A, hcov, hagree⟩
    refine ⟨hc, p, fun i => ⋂ j, (H i j).set, fun i x => Agent091.AffineFun.eval (A i) x 0,
      ?_, ?_, hcov, ?_⟩
    · exact fun i => ⟨m i, fun j => (H i j).set, fun j => ⟨(H i j).c, (H i j).d, rfl⟩, rfl⟩
    · exact fun i => ⟨(A i).1 0, (A i).2 0, fun x => rfl⟩
    · intro i x hx
      exact hagree i x (Set.mem_iInter.mp hx)
  · rintro ⟨hc, N, P, g, hpoly, haff, hcov, hagree⟩
    simp only [Ref.IsPolyhedron] at hpoly
    simp only [Ref.IsAffine] at haff
    choose q Hs hHs hPeq using hpoly
    simp only [Ref.IsHalfspace] at hHs
    choose c d hcd using hHs
    choose a b hab using haff
    have hset : ∀ i j, (⟨c i j, d i j⟩ : Agent091.Halfspace n).set = Hs i j :=
      fun i j => (hcd i j).symm
    refine ⟨hc, N, q, fun i j => ⟨c i j, d i j⟩,
      fun i => Prod.mk (fun _ => a i) (fun _ => b i), ?_, ?_⟩
    · simp only [hset, ← hPeq]
      exact hcov
    · intro i x hx
      have hxP : x ∈ P i := by
        rw [hPeq i]
        exact Set.mem_iInter.mpr fun j => by rw [← hset i j]; exact hx j
      exact (hagree i x hxP).trans (hab i x)

/-! ## The depth bound

Agent 091 is the one file that writes the bound as `Nat.clog 3 (n-1) + 1` instead of
`⌈Real.logb 3 (n-1)⌉₊ + 1`, so this is exactly `Real.natCeil_logb_natCast`. -/

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent091.depthBound n = Ref.depthBound n := by
  have h1 : (1 : ℕ) ≤ n := le_trans (by norm_num) hn
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub h1, Nat.cast_one]
  have h3 : ((3 : ℕ) : ℝ) = (3 : ℝ) := by norm_num
  have key := Real.natCeil_logb_natCast 3 (n - 1)
  rw [h3, hcast] at key
  simp only [Agent091.depthBound, Ref.depthBound, ← key]

/-! ## The statement -/

theorem statement :
    (∀ n, 3 ≤ n → Agent091.CPWL n = Agent091.ReLUn n (Agent091.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
  constructor
  · intro h n hn
    rw [← cpwl n, ← relun n (Ref.depthBound n), ← depth n hn]
    exact h n hn
  · intro h n hn
    rw [cpwl n, relun n (Agent091.depthBound n), depth n hn]
    exact h n hn

end Star_091

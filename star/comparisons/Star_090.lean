namespace Star_090

open Agent090

/-! ### Affine functionals

Both files use literally the same predicate, so the translation is definitional. -/

private lemma isAffine_iff {n : ℕ} (g : (Fin n → ℝ) → ℝ) :
    Agent090.IsAffine g ↔ Ref.IsAffine g := Iff.rfl

/-! ### Polyhedra: `List (Halfspace n)` versus a finite intersection of halfspace sets -/

/-- The point set cut out by a list of halfspaces is a `Ref` polyhedron. -/
private lemma isPolyhedron_of_list {n : ℕ} (L : Polyhedron n) :
    Ref.IsPolyhedron n {x | L.mem x} := by
  refine ⟨L.length,
    fun i => {x | (∑ k, (L[i.1]'i.2).a k * x k) ≤ (L[i.1]'i.2).b},
    fun i => ⟨(L[i.1]'i.2).a, (L[i.1]'i.2).b, rfl⟩, ?_⟩
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iInter, Polyhedron.mem, Halfspace.mem]
  constructor
  · intro h i
    exact h _ (List.mem_iff_getElem.mpr ⟨i.1, i.2, rfl⟩)
  · intro h H hH
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hH
    exact h ⟨i, hi⟩

/-- Membership in a polyhedron built by `List.ofFn` is membership in every halfspace. -/
private lemma mem_ofFn_iff {n m : ℕ} (F : Fin m → Halfspace n) (x : Fin n → ℝ) :
    Agent090.Polyhedron.mem (List.ofFn F) x ↔ ∀ i, (F i).mem x := by
  show (∀ H ∈ List.ofFn F, Halfspace.mem H x) ↔ ∀ i, (F i).mem x
  constructor
  · intro h i
    exact h (F i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · intro h H hH
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hH
    exact h i

/-! ### The CPWL sets agree -/

/-- Both files define `CPWL` as "continuous, plus a finite polyhedral cover on each piece
of which `f` is affine"; the only difference is that `Agent090` encodes a polyhedron as a
list of halfspaces and the reference as a finite intersection of halfspace sets. -/
theorem cpwl (n : ℕ) : Agent090.CPWL n = Ref.CPWL n := by
  ext f
  simp only [Agent090.CPWL, Ref.CPWL, Ref.IsCPWL, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hc, m, P, g, hg, hcov, hagree⟩
    refine ⟨hc, m, fun j => {x | (P j).mem x}, g, fun j => isPolyhedron_of_list (P j),
      fun j => (isAffine_iff _).mp (hg j), ?_, hagree⟩
    exact Set.eq_univ_iff_forall.mpr fun x => Set.mem_iUnion.mpr (hcov x)
  · rintro ⟨hc, m, P, g, hP, hg, hcov, hagree⟩
    choose mm H hH hPeq using hP
    choose a b hab using hH
    have hmem : ∀ (j : Fin m) (x : Fin n → ℝ),
        Agent090.Polyhedron.mem
            (List.ofFn (fun i => ({ a := a j i, b := b j i } : Halfspace n))) x ↔ x ∈ P j := by
      intro j x
      rw [mem_ofFn_iff, hPeq j, Set.mem_iInter]
      refine forall_congr' fun i => ?_
      constructor
      · intro h; rw [hab j i]; exact h
      · intro h; rw [hab j i] at h; exact h
    refine ⟨hc, m, fun j => List.ofFn (fun i => ({ a := a j i, b := b j i } : Halfspace n)), g,
      fun j => (isAffine_iff _).mpr (hg j), ?_, ?_⟩
    · intro x
      have hx : x ∈ ⋃ i, P i := by rw [hcov]; exact Set.mem_univ x
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      exact ⟨j, (hmem j x).mpr hj⟩
    · intro j x hx
      exact hagree j x ((hmem j x).mp hx)

/-! ### The network classes agree -/

/-- `Agent090.Network n k` is exactly the data that `Ref.ComputedBy n k` quantifies over:
`Network n 0` has only the `output` constructor and `Network n (k+1)` only `cons`, matching
the two branches of `Ref.ComputedBy`. -/
private lemma computedBy_iff (n k : ℕ) (f : (Fin n → ℝ) → ℝ) :
    Ref.ComputedBy n k f ↔ ∃ N : Network n k, ∀ x, f x = N.eval x := by
  induction k generalizing n f with
  | zero =>
    simp only [Ref.ComputedBy]
    constructor
    · rintro ⟨T, hT⟩
      exact ⟨.output ⟨T.M, T.c⟩, fun x => hT x⟩
    · rintro ⟨N, hN⟩
      cases N with
      | output T => exact ⟨⟨T.A, T.c⟩, fun x => hN x⟩
  | succ k ih =>
    simp only [Ref.ComputedBy]
    constructor
    · rintro ⟨mm, T, g, hg, hf⟩
      obtain ⟨N, hN⟩ := (ih mm g).mp hg
      refine ⟨.cons ⟨T.M, T.c⟩ N, fun x => ?_⟩
      rw [hf x]
      exact hN _
    · rintro ⟨N, hN⟩
      cases N with
      | cons T rest =>
        exact ⟨_, ⟨T.A, T.c⟩, rest.eval, (ih _ _).mpr ⟨rest, fun _ => rfl⟩, fun x => hN x⟩

/-- Both files read `ReLU_{n,k}` as "**at most** `k` hidden layers", so no padding argument
is needed here. -/
theorem relun (n k : ℕ) : Agent090.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent090.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, N, hN⟩
    exact ⟨j, hj, (computedBy_iff n j f).mpr ⟨N, hN⟩⟩
  · rintro ⟨j, hj, h⟩
    obtain ⟨N, hN⟩ := (computedBy_iff n j f).mp h
    exact ⟨j, hj, N, hN⟩

/-! ### The depth bound -/

/-- Both files write the bound in the identical `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1` shape. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent090.depthBound n = Ref.depthBound n := rfl

/-! ### The statements agree -/

theorem statement :
    (∀ n, 3 ≤ n → Agent090.CPWL n = Agent090.ReLUn n (Agent090.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
  have e1 : ∀ n, Agent090.ReLUn n (Agent090.depthBound n) = Ref.ReLUn n (Ref.depthBound n) :=
    fun n => relun n (Agent090.depthBound n)
  exact ⟨fun h n hn => (cpwl n).symm.trans ((h n hn).trans (e1 n)),
         fun h n hn => (cpwl n).trans ((h n hn).trans (e1 n).symm)⟩

end Star_090

namespace Star_098

/-!
# Comparison of `Agent098` with `Ref`

`Agent098` is a faithful variant of the reference:

* `CPWL` is the honest finite **polyhedral subdivision** condition (continuity plus a
  finite polyhedral cover with an affine function on each piece).  The only differences
  from `Ref` are bookkeeping: polyhedra are packaged as `{x | ∀ i, ⟪A i, x⟫ ≤ b i}`
  instead of an intersection of halfspaces, affine pieces are a structure `AffineFn`
  instead of an existential, and the cover equation is stated as `univ = ⋃ i, S i`.
* `ReLUn` is **at most `k`** hidden layers, exactly as in `Ref`, so no padding argument
  is needed and `relun` is provable by a plain induction.
* `depthBound` is literally the same term.

Hence all four obligations are proved.
-/

/-! ### Networks -/

/-- The two "exactly `k` hidden layers" predicates agree: `Agent098.AffineTransform` and
`Ref.Aff` are the same data, and `Agent098.relu`/`Ref.relu` are the same function. -/
private lemma computedBy_iff :
    ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ), Agent098.ReLURepExact k n f ↔ Ref.ComputedBy n k f := by
  intro k
  induction k with
  | zero =>
      intro n f
      constructor
      · rintro ⟨T, hT⟩
        exact ⟨⟨T.A, T.bias⟩, hT⟩
      · rintro ⟨T, hT⟩
        exact ⟨⟨T.M, T.c⟩, hT⟩
  | succ k ih =>
      intro n f
      constructor
      · rintro ⟨m, T, g, hg, hf⟩
        exact ⟨m, ⟨T.A, T.bias⟩, g, (ih m g).1 hg, hf⟩
      · rintro ⟨m, T, g, hg, hf⟩
        exact ⟨m, ⟨T.M, T.c⟩, g, (ih m g).2 hg, hf⟩

theorem relun (n k : ℕ) : Agent098.ReLUn n k = Ref.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, (computedBy_iff j n f).1 h⟩
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, (computedBy_iff j n f).2 h⟩

/-! ### Polyhedra -/

/-- A set cut out by finitely many affine inequalities is an intersection of halfspaces. -/
private lemma polyhedron_of_agent {n : ℕ} {S : Set (Fin n → ℝ)}
    (h : Agent098.IsPolyhedron n S) : Ref.IsPolyhedron n S := by
  obtain ⟨m, A, b, hS⟩ := h
  refine ⟨m, fun j => {x | (∑ l, A j l * x l) ≤ b j}, fun j => ⟨A j, b j, rfl⟩, ?_⟩
  rw [hS]
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iInter]

/-- Conversely, a finite intersection of halfspaces is cut out by finitely many affine
inequalities. -/
private lemma polyhedron_of_ref {n : ℕ} {S : Set (Fin n → ℝ)}
    (h : Ref.IsPolyhedron n S) : Agent098.IsPolyhedron n S := by
  obtain ⟨m, H, hH, hS⟩ := h
  choose A b hAb using hH
  refine ⟨m, A, b, ?_⟩
  rw [hS]
  ext x
  simp only [Set.mem_iInter, hAb, Set.mem_setOf_eq]

/-! ### CPWL -/

theorem cpwl (n : ℕ) : Agent098.CPWL n = Ref.CPWL n := by
  ext f
  simp only [Agent098.CPWL, Ref.CPWL, Ref.IsCPWL, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hc, m, S, g, hpoly, hcov, hagree⟩
    refine ⟨hc, m, S, fun i => (g i).eval, fun i => polyhedron_of_agent (hpoly i),
      fun i => ⟨(g i).a, (g i).b, fun x => rfl⟩, hcov.symm, hagree⟩
  · rintro ⟨hc, m, P, g, hpoly, haff, hcov, hagree⟩
    choose a b hab using haff
    refine ⟨hc, m, P, fun i => ⟨a i, b i⟩, fun i => polyhedron_of_ref (hpoly i), hcov.symm,
      fun i x hx => ?_⟩
    rw [hagree i x hx]
    exact hab i x

/-! ### Depth bound -/

/-- The two depth bounds are the same term: `⌈·⌉₊` *is* `Nat.ceil`. -/
private lemma depthEq (n : ℕ) : Agent098.depthBound n = Ref.depthBound n := rfl

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent098.depthBound n = Ref.depthBound n := depthEq n

/-! ### The statement -/

theorem statement :
    (∀ n, 3 ≤ n → Agent098.CPWL n = Agent098.ReLUn n (Agent098.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
  constructor
  · intro h n hn
    rw [← cpwl n, ← depthEq n, ← relun n (Agent098.depthBound n)]
    exact h n hn
  · intro h n hn
    rw [cpwl n, relun n (Agent098.depthBound n), depthEq n]
    exact h n hn

end Star_098

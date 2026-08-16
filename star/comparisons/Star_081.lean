/-!
# Star comparison: `Agent081` vs `Ref`

`Agent081` is a genuine *polyhedral* formalization, not a neighbourhood-agreement
one: `CPWL n` asks for a finite cover of `ℝⁿ` by sets cut out by finitely many
non-strict affine inequalities, on each of which `f` agrees with an affine map.
That is exactly `Ref.IsCPWL`, modulo two purely presentational differences:

* a polyhedron is packaged as `{x | ∀ j, ∑ i, a j i * x i ≤ b j}` rather than as
  an intersection `⋂ j, H j` of halfspaces, and
* the affine pieces are `Affine n 1` records rather than `Ref.IsAffine`
  functionals.

`ReLUn` is "at most `k` hidden layers" on both sides, with the same recursion, so
`relun` is provable too (no padding identity is needed).  `depthBound` is
syntactically the same expression.
-/

namespace Star_081

/-! ### Affine pieces -/

/-- Evaluating an `Agent081.Affine n 1` in coordinates. -/
private lemma affine_eval {n : ℕ} (T : Agent081.Affine n 1) (x : Fin n → ℝ) :
    T.eval x 0 = (∑ j, T.A 0 j * x j) + T.c 0 := by
  first
    | rfl
    | simp [Agent081.Affine.eval, Matrix.mulVec]

/-! ### Polyhedra -/

/-- A finite system of non-strict affine inequalities is a `Ref` polyhedron. -/
private lemma poly_agent_to_ref {n : ℕ} {P : Set (Fin n → ℝ)}
    (h : Agent081.IsHalfspacePolyhedron P) : Ref.IsPolyhedron n P := by
  obtain ⟨m, a, b, rfl⟩ := h
  refine ⟨m, fun j => {x | (∑ i, a j i * x i) ≤ b j}, fun j => ⟨a j, b j, rfl⟩, ?_⟩
  ext x
  simp [Set.mem_iInter]

/-- A `Ref` polyhedron is a finite system of non-strict affine inequalities. -/
private lemma poly_ref_to_agent {n : ℕ} {P : Set (Fin n → ℝ)}
    (h : Ref.IsPolyhedron n P) : Agent081.IsHalfspacePolyhedron P := by
  obtain ⟨m, H, hH, rfl⟩ := h
  choose a b hab using hH
  refine ⟨m, a, b, ?_⟩
  ext x
  simp [Set.mem_iInter, hab]

/-! ### The four obligations -/

/-- The two `CPWL` definitions agree: both are "continuous + finite polyhedral
cover with an affine piece on each cell". -/
theorem cpwl (n : ℕ) : Agent081.CPWL n = Ref.CPWL n := by
  ext f
  simp only [Agent081.CPWL, Ref.CPWL, Ref.IsCPWL, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hf, m, P, g, hcov, hpoly, hagree⟩
    refine ⟨hf, m, P, fun i x => (g i).eval x 0, fun i => poly_agent_to_ref (hpoly i),
      fun i => ⟨fun j => (g i).A 0 j, (g i).c 0, fun x => affine_eval (g i) x⟩, hcov, hagree⟩
  · rintro ⟨hf, m, P, g, hpoly, haff, hcov, hagree⟩
    choose a b hab using haff
    refine ⟨hf, m, P, fun i => ⟨fun _ j => a i j, fun _ => b i⟩, hcov,
      fun i => poly_ref_to_agent (hpoly i), ?_⟩
    intro i x hx
    rw [hagree i x hx, hab i x, affine_eval]

/-- `Agent081.reluVec` and `Ref.reluVec` are the same function. -/
private lemma reluVec_eq {n : ℕ} (v : Fin n → ℝ) :
    Agent081.reluVec v = Ref.reluVec v := rfl

/-- The two network-computability predicates agree, layer count for layer count.
Both are the same recursion on the number of hidden layers; only the record type
holding the affine map differs. -/
private lemma computed_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent081.NetworkComputes n k f ↔ Ref.ComputedBy n k f := by
  intro k
  induction k with
  | zero =>
      intro n f
      constructor
      · rintro ⟨T, hT⟩
        exact ⟨⟨T.A, T.c⟩, hT⟩
      · rintro ⟨T, hT⟩
        exact ⟨⟨T.M, T.c⟩, hT⟩
  | succ k ih =>
      intro n f
      constructor
      · rintro ⟨m, T, g, hg, hf⟩
        exact ⟨m, ⟨T.A, T.c⟩, g, (ih m g).mp hg, hf⟩
      · rintro ⟨m, T, g, hg, hf⟩
        exact ⟨m, ⟨T.M, T.c⟩, g, (ih m g).mpr hg, hf⟩

/-- Both files read `ReLUn n k` as "**at most** `k` hidden layers", so no padding
identity is needed here. -/
theorem relun (n k : ℕ) : Agent081.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent081.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, (computed_iff j n f).mp h⟩
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, (computed_iff j n f).mpr h⟩

/-- The depth bounds are the same expression `⌈logb 3 (n-1)⌉₊ + 1`. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent081.depthBound n = Ref.depthBound n := rfl

theorem statement :
    (∀ n, 3 ≤ n → Agent081.CPWL n = Agent081.ReLUn n (Agent081.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
  constructor
  · intro h n hn
    have hstep := h n hn
    rwa [cpwl n, relun n (Agent081.depthBound n), depth n hn] at hstep
  · intro h n hn
    have hstep := h n hn
    rw [← cpwl n, ← depth n hn, ← relun n (Agent081.depthBound n)] at hstep
    exact hstep

end Star_081

namespace Star_086

/-!
`Agent086` is a *genuine* polyhedral formalization: its `CPWL` asks for a finite
cover of `ℝⁿ` by solution sets of finite systems of affine inequalities, on each
of which `f` is given by an affine formula.  That is exactly `Ref.IsCPWL` with
the affine functional inlined and the polyhedron written as one inequality
system instead of an intersection of halfspaces.  Both `ReLUn`s are the "at most
`k` hidden layers" reading, and the two depth bounds are literally the same term.
So all four obligations are provable.
-/

/-- The agent's inequality systems and the reference's finite intersections of
halfspaces cut out the same subsets of `ℝⁿ`. -/
private theorem poly_iff (n : ℕ) (S : Set (Fin n → ℝ)) :
    Agent086.IsPolyhedralSet n S ↔ Ref.IsPolyhedron n S := by
  constructor
  · rintro ⟨m, A, c, rfl⟩
    refine ⟨m, fun j => {x | ∑ i, A j i * x i ≤ c j}, fun j => ⟨A j, c j, rfl⟩, ?_⟩
    ext x
    simp [Set.mem_iInter]
  · rintro ⟨m, H, hH, rfl⟩
    choose a b hab using hH
    refine ⟨m, a, b, ?_⟩
    ext x
    simp [Set.mem_iInter, hab]

theorem cpwl (n : ℕ) : Agent086.CPWL n = Ref.CPWL n := by
  ext f
  simp only [Agent086.CPWL, Ref.CPWL, Ref.IsCPWL, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hc, ι, P, A, b, hP, hcov, hagree⟩
    exact ⟨hc, ι, P, fun j x => (∑ i, A j i * x i) + b j,
      fun j => (poly_iff n _).1 (hP j), fun j => ⟨A j, b j, fun _ => rfl⟩, hcov, hagree⟩
  · rintro ⟨hc, m, P, g, hP, hg, hcov, hagree⟩
    choose a b hab using hg
    refine ⟨hc, m, P, a, b, fun j => (poly_iff n _).2 (hP j), hcov, ?_⟩
    intro j x hx
    rw [hagree j x hx, hab j x]

/-- The two "exactly `k` hidden layers" predicates agree.  The agent's networks
carry an explicit output dimension; at output dimension `1` a network is the same
data as the reference's scalar-valued one, because `Fin 1` is a subsingleton. -/
private theorem net_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    (Agent086.NetComputes k n 1 fun x _ => f x) ↔ Ref.ComputedBy n k f := by
  intro k
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨A, c, h⟩
      exact ⟨⟨Matrix.of A, c⟩, fun x => h x 0⟩
    · rintro ⟨T, h⟩
      refine ⟨fun j i => T.M j i, T.c, fun x j => ?_⟩
      have hj : j = 0 := Subsingleton.elim j 0
      subst hj
      exact h x
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨h, T, g, hT, hg, hf⟩
      obtain ⟨A, c, hA⟩ := hT
      have hgg : (fun (y : Fin h → ℝ) (_ : Fin 1) => g y 0) = g := by
        funext y j
        exact congrArg (g y) (Subsingleton.elim 0 j)
      have hg' : Agent086.NetComputes k h 1 (fun (y : Fin h → ℝ) (_ : Fin 1) => g y 0) := by
        rw [hgg]; exact hg
      refine ⟨h, ⟨Matrix.of A, c⟩, fun y => g y 0, (ih h fun y => g y 0).1 hg', ?_⟩
      intro x
      have hx : Ref.Aff.eval ⟨Matrix.of A, c⟩ x = T x := by
        funext j
        exact (hA x j).symm
      rw [hx]
      exact congrFun (congrFun hf x) 0
    · rintro ⟨m, T, g, hg, hf⟩
      refine ⟨m, fun x => T.eval x, fun y _ => g y,
        ⟨fun j i => T.M j i, T.c, fun _ _ => rfl⟩, (ih m g).2 hg, ?_⟩
      funext x j
      exact hf x

theorem relun (n k : ℕ) : Agent086.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent086.ReLUn, Agent086.ReLUnExact, Ref.ReLUn, Set.mem_setOf_eq]
  exact exists_congr fun k' => and_congr_right fun _ => net_iff k' n f

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent086.depthBound n = Ref.depthBound n := rfl

theorem statement :
    (∀ n, 3 ≤ n → Agent086.CPWL n = Agent086.ReLUn n (Agent086.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
  constructor
  · intro h n hn
    rw [← cpwl n, ← depth n hn, ← relun n (Agent086.depthBound n)]
    exact h n hn
  · intro h n hn
    rw [cpwl n, depth n hn, relun n (Ref.depthBound n)]
    exact h n hn

end Star_086

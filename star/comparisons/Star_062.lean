/-!
# Star comparison: `Agent062` vs `Ref`

Agent 062 is a genuine polyhedral-subdivision formalization, so every obligation
is provable:

* `CPWL`  — same shape; the only difference is that a polyhedron is packaged as
  a single family of linear inequalities instead of an intersection of
  halfspaces.  These describe the same sets (`poly_iff`).
* `ReLUn` — both are "at most `k` hidden layers"; the agent uses an inductive
  predicate where the reference uses structural recursion, and the agent's
  constructors fix the function *intensionally* where the reference states it
  pointwise.  `funext` bridges the two (`net_iff`).
* `depthBound` — literally the same definition.
-/

namespace Star_062

/-- The two `IsAffine` predicates are the same statement. -/
private lemma affine_iff {n : ℕ} (g : (Fin n → ℝ) → ℝ) :
    Agent062.IsAffineFun g ↔ Ref.IsAffine g := Iff.rfl

/-- A finite system of linear inequalities cuts out exactly a finite
intersection of halfspaces. -/
private lemma poly_iff (n : ℕ) (S : Set (Fin n → ℝ)) :
    Agent062.IsPolyhedron S ↔ Ref.IsPolyhedron n S := by
  constructor
  · rintro ⟨m, L, b, rfl⟩
    refine ⟨m, fun j => {x | (∑ i, L j i * x i) ≤ b j}, fun j => ⟨L j, b j, rfl⟩, ?_⟩
    ext x
    constructor
    · intro hx
      exact Set.mem_iInter.2 fun j => hx j
    · intro hx j
      exact Set.mem_iInter.1 hx j
  · rintro ⟨m, H, hH, rfl⟩
    choose a b hab using hH
    refine ⟨m, a, b, ?_⟩
    ext x
    constructor
    · intro hx j
      have hj := Set.mem_iInter.1 hx j
      rw [hab j] at hj
      exact hj
    · intro hx
      refine Set.mem_iInter.2 fun j => ?_
      rw [hab j]
      exact hx j

/-- The agent's `CPWL` and the reference's `CPWL` are the same set. -/
theorem cpwl (n : ℕ) : Agent062.CPWL n = Ref.CPWL n := by
  ext f
  simp only [Agent062.CPWL, Ref.CPWL, Ref.IsCPWL, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hc, m, S, g, hS, hg, hcov, hagree⟩
    exact ⟨hc, m, S, g, fun i => (poly_iff n (S i)).1 (hS i),
      fun i => (affine_iff (g i)).1 (hg i), hcov, hagree⟩
  · rintro ⟨hc, m, P, g, hP, hg, hcov, hagree⟩
    exact ⟨hc, m, P, g, fun i => (poly_iff n (P i)).2 (hP i),
      fun i => (affine_iff (g i)).2 (hg i), hcov, hagree⟩

/-- Every network accepted by the agent's inductive predicate is accepted by the
reference's recursive one. -/
private lemma net_to_computed {n k : ℕ} {f : (Fin n → ℝ) → ℝ}
    (h : Agent062.NetComputes n k f) : Ref.ComputedBy n k f := by
  induction h with
  | zero T => exact ⟨⟨T.A, T.bias⟩, fun _ => rfl⟩
  | succ T g _ ih => exact ⟨_, ⟨T.A, T.bias⟩, g, ih, fun _ => rfl⟩

/-- Conversely: the reference states the layer equations pointwise, the agent
fixes the function on the nose, and `funext` bridges the gap. -/
private lemma computed_to_net : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Ref.ComputedBy n k f → Agent062.NetComputes n k f := by
  intro k
  induction k with
  | zero =>
      intro n f hf
      obtain ⟨T, hT⟩ := hf
      have hfe : f = fun x => (⟨T.M, T.c⟩ : Agent062.Affine n 1).eval x 0 := funext hT
      subst hfe
      exact Agent062.NetComputes.zero ⟨T.M, T.c⟩
  | succ k ih =>
      intro n f hf
      obtain ⟨m, T, g, hg, hfx⟩ := hf
      have hfe : f = fun x =>
          g (Agent062.reluVec ((⟨T.M, T.c⟩ : Agent062.Affine n m).eval x)) := funext hfx
      subst hfe
      exact Agent062.NetComputes.succ ⟨T.M, T.c⟩ g (ih m g hg)

/-- The two "computed by a network with exactly `k` hidden layers" predicates
agree. -/
private lemma net_iff (n k : ℕ) (f : (Fin n → ℝ) → ℝ) :
    Agent062.NetComputes n k f ↔ Ref.ComputedBy n k f :=
  ⟨net_to_computed, computed_to_net k n f⟩

/-- Both files read `ReLUn n k` as "at most `k` hidden layers", so the sets are
equal for every `n` and `k` — no padding argument is needed. -/
theorem relun (n k : ℕ) : Agent062.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent062.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  exact exists_congr fun j => and_congr_right fun _ => net_iff n j f

/-- The depth bounds are literally the same definition. -/
private lemma depthEq (n : ℕ) : Agent062.depthBound n = Ref.depthBound n := rfl

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent062.depthBound n = Ref.depthBound n :=
  depthEq n

/-- The two statements of Theorem 2 are equivalent instance by instance. -/
private lemma inst_iff (n : ℕ) :
    (Agent062.CPWL n = Agent062.ReLUn n (Agent062.depthBound n)) ↔
      (Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
  rw [cpwl n, relun n (Agent062.depthBound n), depthEq n]

theorem statement :
    (∀ n, 3 ≤ n → Agent062.CPWL n = Agent062.ReLUn n (Agent062.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
  constructor
  · intro h n hn
    exact (inst_iff n).1 (h n hn)
  · intro h n hn
    exact (inst_iff n).2 (h n hn)

end Star_062

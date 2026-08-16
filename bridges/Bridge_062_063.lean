namespace Bridge_062_063

/-
  Agent062 and Agent063 are, up to encoding, the *same* formalization:
  * Both encode affine maps `ℝ^a → ℝ^b` via a matrix and bias (062 bundles
    these into a `structure Affine`; 063 keeps them as separate arguments,
    with `A : Fin b → Fin a → ℝ`, which is defeq to `Matrix (Fin b) (Fin a) ℝ`).
  * Both define "computed by a `k`-hidden-layer ReLU net" by the same
    recursion on `k` (062 as an inductive predicate `NetComputes`, 063 as a
    `Represents` function defined by pattern matching on `k`), and both read
    `ReLUn n k` as "at most `k` layers".
  * Both define `CPWL` as: continuous, with a finite polyhedral subdivision
    of `ℝ^n` (`⋃ = univ`) on each piece of which `f` agrees with an affine
    function. 062's polyhedra use `∑ L j i * x i ≤ b j`; 063's use
    `∑ a j i * x i + b j ≤ 0` — the same class of sets, sign-flipped.
  So all four obligations are provable rather than refutable here.
-/

/-- 062's inequality form for polyhedra and 063's agree (negate the constant). -/
theorem isPolyhedron_iff {n : ℕ} (S : Set (Fin n → ℝ)) :
    Agent062.IsPolyhedron S ↔ Agent063.IsPolyhedron n S := by
  constructor
  · rintro ⟨m, L, b, hS⟩
    refine ⟨m, L, fun j => -(b j), ?_⟩
    rw [hS]; ext x; simp only [Set.mem_setOf_eq]
    constructor
    · intro h j; linarith [h j]
    · intro h j; linarith [h j]
  · rintro ⟨m, a, b, hP⟩
    refine ⟨m, a, fun j => -(b j), ?_⟩
    rw [hP]; ext x; simp only [Set.mem_setOf_eq]
    constructor
    · intro h j; linarith [h j]
    · intro h j; linarith [h j]

/-- `CPWL` agrees: same shape, `IsAffineFun`/`IsAffine` coincide definitionally,
and the polyhedron predicates coincide by `isPolyhedron_iff`. -/
theorem cpwl (n : ℕ) : Agent062.CPWL n = Agent063.CPWL n := by
  ext f
  constructor
  · rintro ⟨hf, m, S, g, hS, hg, hcov, hagree⟩
    exact ⟨hf, m, S, g, fun i => (isPolyhedron_iff (S i)).mp (hS i), hg, hcov, hagree⟩
  · rintro ⟨hf, m, S, g, hS, hg, hcov, hagree⟩
    exact ⟨hf, m, S, g, fun i => (isPolyhedron_iff (S i)).mpr (hS i), hg, hcov, hagree⟩

/-- `NetComputes` (062, inductive, matrix-bundled) and `Represents` (063,
recursive, matrix unbundled) describe the same functions at every `k`. -/
theorem netComputes_iff :
    ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
      Agent062.NetComputes n k f ↔ Agent063.Represents n k f := by
  intro k
  induction k with
  | zero =>
      intro n f
      constructor
      · intro h
        cases h with
        | zero T =>
            exact ⟨fun j => T.A 0 j, T.bias 0, fun x => by
              simp [Agent062.Affine.eval, Matrix.mulVec, dotProduct, Pi.add_apply]⟩
      · rintro ⟨c, b, hf⟩
        have heq : f = fun x =>
            (Agent062.Affine.mk (fun _ j => c j) (fun _ => b) : Agent062.Affine n 1).eval x 0 := by
          funext x
          rw [hf x]
          simp [Agent062.Affine.eval, Matrix.mulVec, dotProduct, Pi.add_apply]
        rw [heq]
        exact Agent062.NetComputes.zero (Agent062.Affine.mk (fun _ j => c j) (fun _ => b))
  | succ k ih =>
      intro n f
      constructor
      · intro h
        cases h with
        | succ T g hg =>
            have hgi := (ih _ g).mp hg
            refine ⟨_, T.A, T.bias, g, hgi, fun x => ?_⟩
            congr 1
            funext i
            simp [Agent062.Affine.eval, Agent063.affineApply, Agent062.reluVec,
                  Agent063.reluVec, Agent062.relu, Agent063.reluR, Matrix.mulVec,
                  dotProduct, Pi.add_apply]
      · rintro ⟨m, A, bvec, g, hg, hf⟩
        have hg' : Agent062.NetComputes m k g := (ih m g).mpr hg
        have heq : f = fun x =>
            g (Agent062.reluVec ((Agent062.Affine.mk A bvec).eval x)) := by
          funext x
          rw [hf x]
          congr 1
          funext i
          simp [Agent062.Affine.eval, Agent063.affineApply, Agent062.reluVec,
                Agent063.reluVec, Agent062.relu, Agent063.reluR, Matrix.mulVec,
                dotProduct, Pi.add_apply]
        rw [heq]
        exact Agent062.NetComputes.succ (Agent062.Affine.mk A bvec) g hg'

/-- `ReLUn n k` is "`∃ k' ≤ k`" wrapped around `NetComputes`/`Represents`, which
agree by `netComputes_iff`. -/
theorem relun (n k : ℕ) : Agent062.ReLUn n k = Agent063.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨k', hk', h⟩
    exact ⟨k', hk', (netComputes_iff k' n f).mp h⟩
  · rintro ⟨k', hk', h⟩
    exact ⟨k', hk', (netComputes_iff k' n f).mpr h⟩

/-- Both `depthBound`s are the literal expression `⌈log_3 (n - 1)⌉ + 1`. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent062.depthBound n = Agent063.depthBound n := rfl

theorem statement :
    (∀ n, 3 ≤ n → Agent062.CPWL n = Agent062.ReLUn n (Agent062.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent063.CPWL n = Agent063.ReLUn n (Agent063.depthBound n)) := by
  constructor
  · intro h n hn
    rw [← cpwl n, h n hn, relun n (Agent062.depthBound n), depth n hn]
  · intro h n hn
    rw [cpwl n, h n hn, ← relun n (Agent063.depthBound n), ← depth n hn]

end Bridge_062_063

namespace Bridge_054_055

/-- `depth`: both agents compute `⌈log₃(n-1)⌉ + 1`; `Nat.cast_sub` (valid
since `n ≥ 3 ≥ 1`) turns Agent055's ℕ-truncated-then-cast argument into
exactly Agent054's real subtraction `(n:ℝ) - 1`. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) :
    Agent054.depthBound n = Agent055.depthBound n := by
  have h1 : (1 : ℕ) ≤ n := by omega
  unfold Agent054.depthBound Agent055.depthBound
  rw [Nat.cast_sub h1, Nat.cast_one]

/-! ### `relun`: both are "at most `k` hidden layers" over isomorphic
affine-map structures (`AffineMap`/`AffMap` are both `Matrix + bias`, and
`relu`/`reluVec` are literally `max 0` applied pointwise in both files), so
the two families of representable functions coincide. -/

private theorem affEval054to055 {a b : ℕ} (T : Agent054.AffineMap a b)
    (x : Fin a → ℝ) (i : Fin b) :
    T.eval x i = Agent055.AffMap.eval ⟨T.A, T.c⟩ x i := by
  simp [Agent054.AffineMap.eval, Agent055.AffMap.eval, Matrix.mulVec,
    Matrix.dotProduct, Pi.add_apply]

private theorem affEval055to054 {a b : ℕ} (T : Agent055.AffMap a b)
    (x : Fin a → ℝ) (i : Fin b) :
    Agent055.AffMap.eval T x i = Agent054.AffineMap.eval ⟨T.A, T.c⟩ x i := by
  simp [Agent054.AffineMap.eval, Agent055.AffMap.eval, Matrix.mulVec,
    Matrix.dotProduct, Pi.add_apply]

private theorem reluAff054to055 {a b : ℕ} (T : Agent054.AffineMap a b)
    (x : Fin a → ℝ) :
    Agent054.reluVec (T.eval x) =
      Agent055.reluVec (Agent055.AffMap.eval ⟨T.A, T.c⟩ x) := by
  funext i
  have h := affEval054to055 T x i
  simp [Agent054.reluVec, Agent055.reluVec, Agent054.relu, Agent055.relu, h]

private theorem reluAff055to054 {a b : ℕ} (T : Agent055.AffMap a b)
    (x : Fin a → ℝ) :
    Agent055.reluVec (T.eval x) =
      Agent054.reluVec (Agent054.AffineMap.eval ⟨T.A, T.c⟩ x) := by
  funext i
  have h := affEval055to054 T x i
  simp [Agent054.reluVec, Agent055.reluVec, Agent054.relu, Agent055.relu, h]

private theorem netComputes_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent054.NetComputes k n f ↔ Agent055.ComputedByReLUNet n k f
  | 0, n, f => by
      constructor
      · rintro ⟨T, hf⟩
        exact ⟨fun j => T.A 0 j, T.c 0, fun x => by
          rw [hf]; exact affEval054to055 T x 0⟩
      · rintro ⟨a, b, hf⟩
        refine ⟨⟨fun _ j => a j, fun _ => b⟩, funext fun x => ?_⟩
        rw [hf x]
        exact (affEval054to055 ⟨fun _ j => a j, fun _ => b⟩ x 0).symm
  | (k + 1), n, f => by
      constructor
      · rintro ⟨m, T, g, hg, hf⟩
        refine ⟨m, ⟨T.A, T.c⟩, g, (netComputes_iff k m g).mp hg, fun x => ?_⟩
        rw [congrFun hf x, reluAff054to055 T x]
      · rintro ⟨m, T, g, hg, hf⟩
        refine ⟨m, ⟨T.A, T.c⟩, g, (netComputes_iff k m g).mpr hg,
          funext fun x => ?_⟩
        rw [hf x, reluAff055to054 T x]

theorem relun (n k : ℕ) : Agent054.ReLUn n k = Agent055.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨k', hk', h⟩
    exact ⟨k', hk', (netComputes_iff k' n f).mp h⟩
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, (netComputes_iff j n f).mpr h⟩

-- `cpwl`: Agent055's clause `∀ x, ∃ i, ∃ U ∈ nhds x, EqOn f (g i) U` demands
-- literal agreement with a *fixed finite* affine family throughout a full
-- neighborhood of every point; on the connected space `Fin n → ℝ` the
-- agreement regions are then clopen, which forces `f` to be a single affine
-- function globally (e.g. `x ↦ max 0 (x 0)` fails this at `0`), whereas
-- Agent054's polyhedral-cover clause genuinely admits piecewise-affine, non-
-- affine functions. The sets are almost certainly unequal, but formalizing
-- "affine functions agreeing on an open set are globally equal" (needed for
-- the refutation) is more than a quick win, so this is left open.
theorem cpwl (n : ℕ) : Agent054.CPWL n = Agent055.CPWL n := sorry

-- `statement`: this asks for an iff between each agent's own (`sorry`ed)
-- rendition of Theorem 2. Since `cpwl` above is doubtful, the two claims
-- cannot be transferred into each other by rewriting along the other three
-- bridges, and deciding the iff directly would require resolving the real
-- mathematical content of Theorem 2 for at least one side, out of scope here.
theorem statement :
    (∀ n, 3 ≤ n → Agent054.CPWL n = Agent054.ReLUn n (Agent054.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent055.CPWL n = Agent055.ReLUn n (Agent055.depthBound n)) :=
  sorry

end Bridge_054_055

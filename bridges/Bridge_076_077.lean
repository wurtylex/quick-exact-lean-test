namespace Bridge_076_077

/-!
Both files use the "at most k hidden layers" reading of `ReLUn`, the same
`⌈log₃(n-1)⌉+1` formula for `depthBound`, and the same "local agreement with
a finite affine family" reading of `CPWL` (076 via `=ᶠ[nhds x]`, 077 via an
explicit ε-ball). All four obligations turn out to be genuinely provable.
-/

/-- A scalar affine function of 076's form is one of 077's form (same data,
addition commuted). -/
theorem affineScalar_iff {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    Agent076.IsAffineScalar (n := n) f ↔ Agent077.IsAffineMap f := by
  constructor
  · rintro ⟨a, c, ha⟩
    exact ⟨a, c, fun x => by rw [ha x]; ring⟩
  · rintro ⟨w, b, hw⟩
    exact ⟨w, b, fun x => by rw [hw x]; ring⟩

/-- 076's scalar affine functions on `Fin n → ℝ` are exactly those computed by an
`Agent077.Affine n 1` evaluated at its single output coordinate. -/
theorem affine1_iff (n : ℕ) (f : (Fin n → ℝ) → ℝ) :
    Agent076.IsAffineScalar (n := n) f ↔
      ∃ T : Agent077.Affine n 1, ∀ x, f x = T.eval x 0 := by
  constructor
  · rintro ⟨a, c, ha⟩
    refine ⟨⟨fun _ j => a j, fun _ => c⟩, fun x => ?_⟩
    have h : (Agent077.Affine.mk (fun _ j => a j) (fun _ => c) :
        Agent077.Affine n 1).eval x 0 = (∑ j, a j * x j) + c := by
      simp [Agent077.Affine.eval, Matrix.mulVec, Matrix.dotProduct]
    rw [h, ha x]; ring
  · rintro ⟨T, hT⟩
    refine ⟨fun j => T.A 0 j, T.c 0, fun x => ?_⟩
    have h : T.eval x 0 = (∑ j, T.A 0 j * x j) + T.c 0 := by
      simp [Agent077.Affine.eval, Matrix.mulVec, Matrix.dotProduct]
    rw [hT x, h]; ring

/-- 076's general affine maps `(Fin n → ℝ) → (Fin m → ℝ)` are exactly the
functions computed by some `Agent077.Affine n m`. -/
theorem affineMap_iff (n m : ℕ) (T : (Fin n → ℝ) → (Fin m → ℝ)) :
    Agent076.IsAffineMap T ↔ ∃ S : Agent077.Affine n m, ∀ x, T x = S.eval x := by
  constructor
  · rintro ⟨A, c, hA⟩
    exact ⟨⟨A, c⟩, hA⟩
  · rintro ⟨S, hS⟩
    exact ⟨S.A, S.c, hS⟩

/-- The two recursive "computed by a ReLU network with exactly `k` hidden
layers" predicates agree pointwise, for every `k`. Proved by induction on `k`,
peeling off one affine layer at a time via `affineMap_iff`. -/
theorem computes_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent076.ComputesWithHiddenLayers k n f ↔ Agent077.Computes n k f
  | 0, n, f => by
      simpa [Agent076.ComputesWithHiddenLayers, Agent077.Computes] using affine1_iff n f
  | (k' + 1), n, f => by
      simp only [Agent076.ComputesWithHiddenLayers, Agent077.Computes]
      constructor
      · rintro ⟨m, T, g, hT, hg, hf⟩
        obtain ⟨S, hS⟩ := (affineMap_iff n m T).mp hT
        exact ⟨m, S, g, (computes_iff k' m g).mp hg, fun x => by rw [hf x, hS x]⟩
      · rintro ⟨m, S, g, hg, hf⟩
        exact ⟨m, S.eval, g, (affineMap_iff n m S.eval).mpr ⟨S, fun _ => rfl⟩,
               (computes_iff k' m g).mpr hg, hf⟩

theorem cpwl (n : ℕ) : Agent076.CPWL n = Agent077.CPWL n := by
  ext f
  simp only [Agent076.CPWL, Agent076.IsCPWL, Agent077.CPWL, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hf, m, g, hg, hloc⟩
    refine ⟨hf, m, g, fun i => (affineScalar_iff (g i)).mp (hg i), fun x => ?_⟩
    obtain ⟨i, hi⟩ := hloc x
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hi
    exact ⟨i, ε, hε, hball⟩
  · rintro ⟨hf, m, g, hg, hloc⟩
    refine ⟨hf, m, g, fun i => (affineScalar_iff (g i)).mpr (hg i), fun x => ?_⟩
    obtain ⟨i, ε, hε, hball⟩ := hloc x
    exact ⟨i, Metric.eventually_nhds_iff.mpr ⟨ε, hε, hball⟩⟩

theorem relun (n k : ℕ) : Agent076.ReLUn n k = Agent077.ReLUn n k := by
  ext f
  simp only [Agent076.ReLUn, Agent077.ReLUn, Set.mem_setOf_eq]
  exact exists_congr fun k' => and_congr_right fun _ => computes_iff k' n f

/-- Both files write the identical formula `⌈Real.logb 3 (↑n - 1)⌉₊ + 1`, so this
holds definitionally (the `3 ≤ n` hypothesis is unused). -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent076.depthBound n = Agent077.depthBound n := rfl

theorem statement :
    (∀ n, 3 ≤ n → Agent076.CPWL n = Agent076.ReLUn n (Agent076.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent077.CPWL n = Agent077.ReLUn n (Agent077.depthBound n)) := by
  constructor
  · intro h n hn
    rw [← cpwl n, ← relun n (Agent077.depthBound n), ← depth n hn]
    exact h n hn
  · intro h n hn
    rw [cpwl n, relun n (Agent076.depthBound n), depth n hn]
    exact h n hn

end Bridge_076_077

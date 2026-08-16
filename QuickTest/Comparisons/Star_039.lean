import QuickTest.Formalizations.Thm2_039
import QuickTest.Reference

namespace Star_039

/-! ## Networks

`Agent039.NetProp` and `Ref.ComputedBy` are the same recursion; the only
difference is the name of the affine-map structure, so the two are transported
across by rebuilding the structure. -/

private lemma netProp_iff (k : ℕ) : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent039.NetProp n k f ↔ Ref.ComputedBy n k f := by
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨⟨w.A, w.c⟩, hw⟩
    · rintro ⟨T, hT⟩
      exact ⟨⟨T.M, T.c⟩, hT⟩
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, T, g, hg, hf⟩
      exact ⟨m, ⟨T.A, T.c⟩, g, (ih m g).1 hg, hf⟩
    · rintro ⟨m, T, g, hg, hf⟩
      exact ⟨m, ⟨T.M, T.c⟩, g, (ih m g).2 hg, hf⟩

theorem relun (n k : ℕ) : Agent039.ReLUn n k = Ref.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (netProp_iff j n f).1 hf⟩
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (netProp_iff j n f).2 hf⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent039.depthBound n = Ref.depthBound n := rfl

/-! ## The kink lemma

`Agent039.CPWL` asks that every point have a *neighbourhood* on which `f` agrees
with one member of a finite affine family.  On connected `ℝⁿ` that forces `f` to
be globally affine, so `relu` of a coordinate is not in it. -/

/-- `x ↦ max 0 (x i₀)` is not in the agent's neighbourhood-agreement `CPWL`. -/
private lemma kink {n : ℕ} (i0 : Fin n) :
    (fun x : Fin n → ℝ => max 0 (x i0)) ∉ Agent039.CPWL n := by
  rintro ⟨-, ι, -, w, b, h⟩
  obtain ⟨i, U, hUopen, hxU, hU⟩ := h 0
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ → (Fin n → ℝ), ∀ t j, φ t j = if j = i0 then t else 0 :=
    ⟨fun t j => if j = i0 then t else 0, fun _ _ => rfl⟩
  have hcont : Continuous φ := by
    refine continuous_pi fun j => ?_
    by_cases hj : j = i0
    · simp only [hφ, if_pos hj]; exact continuous_id
    · simp only [hφ, if_neg hj]; exact continuous_const
  have hz : φ 0 = (0 : Fin n → ℝ) := by funext j; simp [hφ]
  have hopen : IsOpen (φ ⁻¹' U) := hUopen.preimage hcont
  have hmem : (0 : ℝ) ∈ φ ⁻¹' U := by show φ 0 ∈ U; rw [hz]; exact hxU
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 hmem
  have key : ∀ t : ℝ, |t| < ε → max 0 t = w i i0 * t + b i := by
    intro t ht
    have htU : φ t ∈ U := hball (by simpa [Real.dist_eq] using ht)
    have hthis : max 0 (φ t i0) = (∑ j, w i j * φ t j) + b i := hU (φ t) htU
    have hi : φ t i0 = t := by rw [hφ]; simp
    have hs : (∑ j, w i j * φ t j) = w i i0 * t := by
      rw [Finset.sum_eq_single i0]
      · rw [hφ]; simp
      · intro j _ hj; rw [hφ]; simp [hj]
      · intro hj; exact absurd (Finset.mem_univ i0) hj
    rw [hi, hs] at hthis
    exact hthis
  have e0 := key 0 (by simpa using hε)
  have ep := key (ε / 2) (by rw [abs_of_pos (by linarith : (0:ℝ) < ε / 2)]; linarith)
  have en := key (-(ε / 2)) (by
    rw [abs_neg, abs_of_pos (by linarith : (0:ℝ) < ε / 2)]; linarith)
  rw [max_self] at e0
  rw [max_eq_right (by linarith : (0:ℝ) ≤ ε / 2)] at ep
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0:ℝ))] at en
  nlinarith [e0, ep, en, hε]

/-! ## The reference side accepts the witness -/

private lemma isPoly (a : Fin 1 → ℝ) (c : ℝ) :
    Ref.IsPolyhedron 1 {x : Fin 1 → ℝ | (∑ i, a i * x i) ≤ c} :=
  ⟨1, fun _ => {x | (∑ i, a i * x i) ≤ c}, fun _ => ⟨a, c, rfl⟩, by ext y; simp⟩

/-- `x ↦ max 0 (x 0)` *is* continuous piecewise linear in the reference sense:
the two halflines `x 0 ≤ 0` and `-x 0 ≤ 0` are polyhedra covering `ℝ¹`. -/
private lemma max_mem_ref : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Ref.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2,
    ![{x : Fin 1 → ℝ | (∑ i, (1:ℝ) * x i) ≤ 0},
      {x : Fin 1 → ℝ | (∑ i, (-1:ℝ) * x i) ≤ 0}],
    ![fun _ => 0, fun x => x 0], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact isPoly (fun _ => 1) 0
    · exact isPoly (fun _ => -1) 0
  · intro i
    fin_cases i
    · exact ⟨0, 0, by intro x; simp⟩
    · exact ⟨fun _ => 1, 0, by intro x; simp⟩
  · refine Set.eq_univ_of_forall fun x => ?_
    rcases le_or_gt (x 0) 0 with hx | hx
    · exact Set.mem_iUnion.2 ⟨0, show (∑ i, (1:ℝ) * x i) ≤ 0 by
        simp only [Fin.sum_univ_one, one_mul]; linarith⟩
    · exact Set.mem_iUnion.2 ⟨1, show (∑ i, (-1:ℝ) * x i) ≤ 0 by
        simp only [Fin.sum_univ_one]; linarith⟩
  · intro i
    fin_cases i
    · intro x hx
      have hx' : (∑ i, (1:ℝ) * x i) ≤ 0 := hx
      simp only [Fin.sum_univ_one, one_mul] at hx'
      show max 0 (x 0) = 0
      exact max_eq_left hx'
    · intro x hx
      have hx' : (∑ i, (-1:ℝ) * x i) ≤ 0 := hx
      simp only [Fin.sum_univ_one] at hx'
      show max 0 (x 0) = x 0
      exact max_eq_right (by linarith)

/-! ## Verdict -/

/-- The agent's `CPWL` (neighbourhood agreement with a finite affine family) is
strictly stronger than the reference's polyhedral-cover `CPWL`. -/
theorem cpwl_ne : ∃ n, Agent039.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  exact kink (0 : Fin 1) (by rw [h]; exact max_mem_ref)

/-- The `1 × 3` matrix selecting the first coordinate. -/
private def row0 : Matrix (Fin 1) (Fin 3) ℝ :=
  Matrix.of fun _ j => if j = 0 then (1:ℝ) else 0

/-- The agent's own Theorem 2 is outright false: `relu` of a coordinate is a
one-hidden-layer network, but the neighbourhood-agreement `CPWL` rejects it. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent039.CPWL n = Agent039.ReLUn n (Agent039.depthBound n)) := by
  intro h
  refine kink (0 : Fin 3) ?_
  rw [h 3 le_rfl]
  have hT : ∀ x : Fin 3 → ℝ, (⟨row0, 0⟩ : Agent039.AffineMap 3 1).eval x 0 = x 0 := by
    intro x
    show (∑ j, (if j = 0 then (1:ℝ) else 0) * x j) + 0 = x 0
    simp
  have h0 : Agent039.NetProp 1 0 (fun v : Fin 1 → ℝ => v 0) :=
    ⟨⟨1, 0⟩, fun x => by simp [Agent039.AffineMap.eval, Matrix.one_mulVec]⟩
  exact ⟨1, Nat.le_add_left 1 _, 1, ⟨row0, 0⟩, (fun v : Fin 1 → ℝ => v 0), h0,
    fun x => by simp [Agent039.reluVec, Agent039.relu, hT x]⟩

/-- Unprovable here: the forward direction follows from `agent_side_false`, but
the converse needs the *truth* of the reference Theorem 2, which is `sorry`-ed
in `Ref` and is a genuine research-level theorem. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent039.CPWL n = Agent039.ReLUn n (Agent039.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

/-- The provable half of `statement`. -/
theorem statement_mp
    (hL : ∀ n, 3 ≤ n → Agent039.CPWL n = Agent039.ReLUn n (Agent039.depthBound n)) :
    ∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n) :=
  absurd hL agent_side_false

end Star_039

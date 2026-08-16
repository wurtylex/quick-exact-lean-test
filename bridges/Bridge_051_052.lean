namespace Bridge_051_052

/-!
Bridge between `Agent051` and `Agent052`'s formalizations of Theorem 2.

Key structural difference: `Agent051.CPWL` requires `f` to agree with a single affine
function on a full metric ball around *every* point (`∀ x, ∃ j, ∃ ε>0, ∀ y, dist y x<ε →
f y = g j y`). On the connected domain `ℝ^n` this forces `f` to have **no kinks at all**:
a genuine piecewise-linear function such as `x ↦ max 0 (x 0)` fails it at the kink `x = 0`.
`Agent052.CPWL` instead uses an honest finite polyhedral subdivision, so it does contain
such kinked functions. Hence `cpwl` is refuted below with the witness `kink`.
-/

/-- The witness function: the ReLU of the first coordinate. Continuous, genuinely
piecewise-affine (kinked at `x 0 = 0`), used to separate the two `CPWL` notions. -/
private def kink : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

private lemma kink_cont : Continuous kink :=
  continuous_const.max (continuous_apply 0)

/-! ### `kink` is not in `Agent051.CPWL 1` -/

private lemma kink_not_mem_051 : kink ∉ Agent051.CPWL 1 := by
  rintro ⟨-, m, g, hg_affine, hloc⟩
  obtain ⟨j, ε, hε, heq⟩ := hloc (fun _ => (0 : ℝ))
  obtain ⟨a, b, hgj⟩ := hg_affine j
  have hδpos : (0 : ℝ) < ε / 2 := by linarith
  have hy0 : dist (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (0 : ℝ)) < ε := by simpa using hε
  have hy1 : dist (fun _ : Fin 1 => ε / 2) (fun _ : Fin 1 => (0 : ℝ)) < ε := by
    rw [dist_pi_lt_iff hε]
    intro i
    rw [Real.dist_eq, sub_zero, abs_of_pos hδpos]
    linarith
  have hy2 : dist (fun _ : Fin 1 => -(ε / 2)) (fun _ : Fin 1 => (0 : ℝ)) < ε := by
    rw [dist_pi_lt_iff hε]
    intro i
    rw [Real.dist_eq, sub_zero, abs_of_neg (show -(ε / 2) < (0 : ℝ) by linarith)]
    linarith
  have h0 : (max (0 : ℝ) 0 : ℝ) = a 0 * 0 + b := by
    have hh := heq (fun _ => (0 : ℝ)) hy0
    rw [hgj] at hh
    simpa [kink, Fin.sum_univ_one] using hh
  have h1 : (max (0 : ℝ) (ε / 2) : ℝ) = a 0 * (ε / 2) + b := by
    have hh := heq (fun _ => ε / 2) hy1
    rw [hgj] at hh
    simpa [kink, Fin.sum_univ_one] using hh
  have h2 : (max (0 : ℝ) (-(ε / 2)) : ℝ) = a 0 * (-(ε / 2)) + b := by
    have hh := heq (fun _ => -(ε / 2)) hy2
    rw [hgj] at hh
    simpa [kink, Fin.sum_univ_one] using hh
  rw [max_self, mul_zero, zero_add] at h0
  rw [max_eq_right hδpos.le] at h1
  rw [max_eq_left (show -(ε / 2) ≤ (0 : ℝ) by linarith)] at h2
  have hb : b = 0 := h0.symm
  rw [hb, add_zero] at h1 h2
  have hexpand : a 0 * (-(ε / 2)) = -(a 0 * (ε / 2)) := by ring
  rw [hexpand] at h2
  linarith [h1, h2, hδpos]

/-! ### `kink` is in `Agent052.CPWL 1` (explicit two-piece polyhedral subdivision) -/

private def hs1 : Agent052.Halfspace 1 := ⟨fun _ => (-1 : ℝ), 0⟩
private def hs2 : Agent052.Halfspace 1 := ⟨fun _ => (1 : ℝ), 0⟩
private def gA1 : Agent052.AffMap 1 1 := ⟨fun _ _ => (1 : ℝ), fun _ => 0⟩
private def gA2 : Agent052.AffMap 1 1 := ⟨fun _ _ => (0 : ℝ), fun _ => 0⟩
private def H052 : Fin 2 → Fin 1 → Agent052.Halfspace 1 := ![fun _ => hs1, fun _ => hs2]
private def g052 : Fin 2 → Agent052.AffMap 1 1 := ![gA1, gA2]

private lemma mem_polyhedron_iff (H : Fin 1 → Agent052.Halfspace 1) (x : Fin 1 → ℝ) :
    x ∈ Agent052.Polyhedron H ↔ x ∈ (H 0).set := by
  unfold Agent052.Polyhedron
  constructor
  · intro h; exact Set.mem_iInter.mp h 0
  · intro h; exact Set.mem_iInter.mpr fun j => by rw [Subsingleton.elim j 0]; exact h

private lemma mem_hs_iff (h : Agent052.Halfspace 1) (x : Fin 1 → ℝ) :
    x ∈ h.set ↔ h.a 0 * x 0 ≤ h.b := by
  unfold Agent052.Halfspace.set
  simp [Fin.sum_univ_one]

private lemma kink_mem_052 : kink ∈ Agent052.CPWL 1 := by
  refine ⟨kink_cont, 2, fun _ => 1, H052, g052, ?_, ?_⟩
  · apply Set.eq_univ_of_forall
    intro x
    rcases le_total (0 : ℝ) (x 0) with h | h
    · refine Set.mem_iUnion.mpr ⟨0, ?_⟩
      have hH : H052 0 = fun _ => hs1 := by simp [H052]
      rw [hH]
      exact (mem_polyhedron_iff _ x).mpr ((mem_hs_iff hs1 x).mpr (by simp only [hs1]; linarith))
    · refine Set.mem_iUnion.mpr ⟨1, ?_⟩
      have hH : H052 1 = fun _ => hs2 := by simp [H052]
      rw [hH]
      exact (mem_polyhedron_iff _ x).mpr ((mem_hs_iff hs2 x).mpr (by simp only [hs2]; linarith))
  · intro i x hx
    fin_cases i
    · have hH : H052 (0 : Fin 2) = fun _ => hs1 := by simp [H052]
      rw [hH] at hx
      have hx0 : (0 : ℝ) ≤ x 0 := by
        have := (mem_hs_iff hs1 x).mp ((mem_polyhedron_iff _ x).mp hx)
        simp only [hs1] at this; linarith
      show kink x = (g052 (0 : Fin 2)).eval x 0
      have hg : g052 (0 : Fin 2) = gA1 := by simp [g052]
      rw [hg]
      simp [gA1, kink, Agent052.AffMap.eval, Fin.sum_univ_one, max_eq_right hx0]
    · have hH : H052 (1 : Fin 2) = fun _ => hs2 := by simp [H052]
      rw [hH] at hx
      have hx0 : x 0 ≤ (0 : ℝ) := by
        have := (mem_hs_iff hs2 x).mp ((mem_polyhedron_iff _ x).mp hx)
        simp only [hs2] at this; linarith
      show kink x = (g052 (1 : Fin 2)).eval x 0
      have hg : g052 (1 : Fin 2) = gA2 := by simp [g052]
      rw [hg]
      simp [gA2, kink, Agent052.AffMap.eval, Fin.sum_univ_one, max_eq_left hx0]

theorem cpwl_ne : ∃ n, Agent051.CPWL n ≠ Agent052.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  have hnm := kink_not_mem_051
  rw [h] at hnm
  exact hnm kink_mem_052

/-! ### `depthBound` -/

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent051.depthBound n = Agent052.depthBound n := by
  unfold Agent051.depthBound Agent052.depthBound
  have h1n : (1 : ℕ) ≤ n := by omega
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have := Nat.cast_sub (R := ℝ) h1n
    simpa using this
  rw [hcast]

/-! ### `ReLUn` -/

/-- SORRY: `Agent051.ReLUn n k` is networks with **exactly** `k` hidden layers
(`Agent051.IsReLUComputable`, a direct recursion on the function type), while
`Agent052.ReLUn n k` is networks with **at most** `k` hidden layers (`∃ k' ≤ k,
Agent052.Represents n k' f`, built from an explicit width-indexed `netEval` with
dependent casts). These coincide only via a nontrivial padding lemma (a `k`-layer network
can simulate `k+1` layers, since `x = ReLU x - ReLU (-x)` lets one layer act as the
identity), which neither source file proves, and reconciling it also requires translating
between the two structurally very different recursive encodings of a ReLU network -
more work than is safe to attempt here without being able to compile-check it. -/
theorem relun (n k : ℕ) : Agent051.ReLUn n k = Agent052.ReLUn n k := by
  sorry

/-! ### `statement` -/

/-- SORRY: the left-hand claim is provably **false** — `kink` is exactly-1-hidden-layer
representable in `Agent051.ReLUn` (take `T` the projection onto coordinate `0` and `g`
the identity), hence representable with `Agent051.depthBound n ≥ 2` layers by padding,
yet `kink ∉ Agent051.CPWL n` by the same argument as `kink_not_mem_051`. So this `Iff`
reduces to `¬ (∀ n ≥ 3, Agent052.CPWL n = Agent052.ReLUn n (Agent052.depthBound n))`, i.e.
to the negation of the paper's actual Theorem 2 in Agent052's encoding (the more faithful
of the two, per the `cpwl` analysis above). That is the real, hard, unproved mathematical
content of the paper — both source files leave their own `theorem2` as `sorry` — and is
out of reach here. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent051.CPWL n = Agent051.ReLUn n (Agent051.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent052.CPWL n = Agent052.ReLUn n (Agent052.depthBound n)) := by
  sorry

end Bridge_051_052

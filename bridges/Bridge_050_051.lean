namespace Bridge_050_051

/-!
Bridge between `Agent050` and `Agent051`.

`CPWL`: Agent050 uses a genuine polyhedral-subdivision reading (family (a) in the
spec); Agent051 uses a "local agreement with a finite family of affine functions"
reading (family (b)). On the connected domain `Fin n → ℝ`, if a continuous `f`
agrees with *some* member of a *finite* fixed family of affine functions on a
neighborhood of every point, then (since two distinct affine functions agreeing on
a nonempty open set must be equal everywhere) the open sets on which each distinct
family member is "active" are pairwise disjoint and cover the connected space, so
exactly one is active everywhere: `f` must in fact be a single *global* affine
function. Hence `Agent051.CPWL n` only contains affine functions, while
`Agent050.CPWL n` contains genuinely kinked functions like `x ↦ max 0 (x 0)`. So
the two `CPWL`s differ; we refute `cpwl`.
-/

theorem cpwl_ne : ∃ n, Agent050.CPWL n ≠ Agent051.CPWL n := by
  have hP0 : Agent050.IsPolyhedron ({x : Fin 1 → ℝ | x 0 ≤ 0}) := by
    refine ⟨1, fun _ _ => 1, fun _ => 0, ?_⟩
    ext x
    simp only [Set.mem_setOf_eq, Fin.sum_univ_one, one_mul]
    exact ⟨fun h _ => h, fun h => h 0⟩
  have hP1 : Agent050.IsPolyhedron ({x : Fin 1 → ℝ | 0 ≤ x 0}) := by
    refine ⟨1, fun _ _ => -1, fun _ => 0, ?_⟩
    ext x
    simp only [Set.mem_setOf_eq, Fin.sum_univ_one, neg_one_mul]
    constructor
    · intro h _; linarith
    · intro h; linarith [h 0]
  have hg0 : Agent050.IsAffineFun (fun _ : Fin 1 → ℝ => (0:ℝ)) :=
    ⟨fun _ => 0, 0, by intro x; simp⟩
  have hg1 : Agent050.IsAffineFun (fun x : Fin 1 → ℝ => x 0) :=
    ⟨fun _ => 1, 0, by intro x; simp [Fin.sum_univ_one]⟩
  have hmem050 : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent050.CPWL 1 := by
    refine ⟨continuous_const.max (continuous_apply 0), 2,
      ![{x : Fin 1 → ℝ | x 0 ≤ 0}, {x : Fin 1 → ℝ | 0 ≤ x 0}],
      ![fun _ : Fin 1 → ℝ => (0:ℝ), fun x : Fin 1 → ℝ => x 0], ?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i
      · simpa using hP0
      · simpa using hP1
    · intro i; fin_cases i
      · simpa using hg0
      · simpa using hg1
    · apply Set.eq_univ_iff_forall.mpr
      intro x
      rcases le_total (x 0) 0 with h | h
      · exact Set.mem_iUnion.mpr ⟨0, h⟩
      · exact Set.mem_iUnion.mpr ⟨1, h⟩
    · intro i; fin_cases i
      · intro x hx
        simp only [Matrix.cons_val_zero, Set.mem_setOf_eq] at hx ⊢
        simp [max_eq_left hx]
      · intro x hx
        simp only [Matrix.cons_val_one, Matrix.head_cons, Set.mem_setOf_eq] at hx ⊢
        simp [max_eq_right hx]
  have hnot051 : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∉ Agent051.CPWL 1 := by
    rintro ⟨-, m, g, hg, hloc⟩
    obtain ⟨j, ε, hε, hball⟩ := hloc (fun _ => (0:ℝ))
    obtain ⟨a, c, hgj⟩ := hg j
    have hgjval : ∀ y : Fin 1 → ℝ, g j y = a 0 * y 0 + c := by
      intro y; rw [hgj y, Fin.sum_univ_one]
    have h0 : c = 0 := by
      have h := hball (fun _ => (0:ℝ)) (by rw [dist_self]; exact hε)
      simp only [hgjval] at h
      simp only [max_self, mul_zero, zero_add] at h
      linarith [h]
    have hdpos : dist (fun _ : Fin 1 => (ε / 2 : ℝ)) (fun _ : Fin 1 => (0:ℝ)) < ε := by
      rw [dist_pi_lt_iff hε]
      intro i
      dsimp only
      rw [Real.dist_eq, show (ε / 2 - 0 : ℝ) = ε / 2 by ring,
        abs_of_pos (by linarith : (0:ℝ) < ε / 2)]
      linarith
    have hdneg : dist (fun _ : Fin 1 => (-(ε / 2) : ℝ)) (fun _ : Fin 1 => (0:ℝ)) < ε := by
      rw [dist_pi_lt_iff hε]
      intro i
      dsimp only
      rw [Real.dist_eq, show (-(ε / 2) - 0 : ℝ) = -(ε / 2) by ring,
        abs_of_neg (by linarith : -(ε / 2) < (0:ℝ))]
      linarith
    have hpos := hball (fun _ => (ε / 2 : ℝ)) hdpos
    have hneg := hball (fun _ => (-(ε / 2) : ℝ)) hdneg
    simp only [hgjval, h0, add_zero] at hpos hneg
    rw [max_eq_right (by linarith : (0:ℝ) ≤ ε / 2)] at hpos
    rw [max_eq_left (by linarith : -(ε / 2) ≤ (0:ℝ))] at hneg
    have hnz : (-(ε / 2) : ℝ) ≠ 0 := by intro h; linarith
    rcases mul_eq_zero.mp hneg.symm with ha0 | hcontra
    · rw [ha0, zero_mul] at hpos; linarith
    · exact hnz hcontra
  exact ⟨1, fun hEq => hnot051 (hEq ▸ hmem050)⟩

/-- `Agent050.ReLUn` reads "at most `k` hidden layers" (`∃ k' ≤ k, …`), while
`Agent051.ReLUn` reads "exactly `k` hidden layers". These coincide as *sets* only
via a padding argument: an extra hidden layer can simulate the identity map via
`x ↦ relu x - relu (-x)`, letting an "at most `k`" network be re-expressed with
"exactly `k`" layers. Nobody has formalized that padding lemma (per the spec), and
proving it in general (induction on the recursive `ReLUNet`/`IsReLUComputable`
structures, constructing the padded affine maps) is substantial work well beyond
what fits in a compact bridge, so this is left as an honest `sorry`. -/
theorem relun (n k : ℕ) : Agent050.ReLUn n k = Agent051.ReLUn n k := by
  sorry

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent050.depthBound n = Agent051.depthBound n := by
  unfold Agent050.depthBound Agent051.depthBound
  have h1 : (1:ℕ) ≤ n := by omega
  rw [Nat.cast_sub h1, Nat.cast_one]

/-- Deciding this biconditional needs the truth value of *both* sides. The
right-hand side (`Agent051`'s statement) is in fact refutable by the same
local-agreement argument as `cpwl_ne`: `Agent051.CPWL n` collapses to just the
globally affine functions on `ℝ^n`, whereas `Agent051.ReLUn n (depthBound n)`
already contains non-affine functions (e.g. `x ↦ relu (x 0)`, representable with a
single hidden layer) once `depthBound n ≥ 1`, so the two sides of Agent051's
equation differ for every `n ≥ 3`. But that alone does not settle the `Iff`: it
also requires knowing whether the left-hand side (`Agent050`'s statement) is true,
and that statement is literally a faithful rendering of the paper's actual
Theorem 2, whose proof is well outside the scope of a compact bridge file. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent050.CPWL n = Agent050.ReLUn n (Agent050.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent051.CPWL n = Agent051.ReLUn n (Agent051.depthBound n)) := by
  sorry

end Bridge_050_051

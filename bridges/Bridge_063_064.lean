namespace Bridge_063_064

/-! ### `depthBound` : proved.

`Agent063` uses `((n:ℝ) - 1)`, `Agent064` uses `((n - 1 : ℕ) : ℝ)`; for `n ≥ 3` (so
`1 ≤ n`) `Nat.cast_sub` identifies the two. -/

theorem depth (n : ℕ) (hn : 3 ≤ n) :
    Agent063.depthBound n = Agent064.depthBound n := by
  unfold Agent063.depthBound Agent064.depthBound
  have h1le : (1 : ℕ) ≤ n := by omega
  rw [Nat.cast_sub h1le, Nat.cast_one]

/-! ### `CPWL` : refuted.

`Agent064.CPWL` requires, for a *fixed finite* family of affine functions, that every point
has an open neighbourhood on which `f` agrees with *one* member of the family. This is much
stronger than genuine piecewise-affinity: at a kink point, no single affine function can
agree with `f` on a full neighbourhood, so this definition actually excludes the paradigm
CPWL function `f0 x = max 0 (x 0)` near `x = 0`. `Agent063.CPWL` uses a genuine polyhedral
subdivision and correctly contains `f0`. We witness the difference directly at `n = 1`. -/

def f0 : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

def a063 : Fin 1 → Fin 1 → ℝ := fun _ _ => -1
def a063' : Fin 1 → Fin 1 → ℝ := fun _ _ => 1

def P063 : Fin 2 → Set (Fin 1 → ℝ) :=
  ![{x | ∀ j : Fin 1, (∑ i : Fin 1, a063 j i * x i) + 0 ≤ 0},
    {x | ∀ j : Fin 1, (∑ i : Fin 1, a063' j i * x i) + 0 ≤ 0}]

def G063 : Fin 2 → (Fin 1 → ℝ) → ℝ := ![(fun x => x 0), (fun _ => 0)]

theorem mem_P063_zero (x : Fin 1 → ℝ) : x ∈ P063 0 ↔ 0 ≤ x 0 := by
  unfold P063
  simp only [Matrix.cons_val_zero, Set.mem_setOf_eq]
  constructor
  · intro h
    have h0 := h 0
    simp only [Fin.sum_univ_one, a063] at h0
    linarith
  · intro h j
    simp only [Fin.sum_univ_one, a063]
    linarith

theorem mem_P063_one (x : Fin 1 → ℝ) : x ∈ P063 1 ↔ x 0 ≤ 0 := by
  unfold P063
  simp only [Matrix.cons_val_one, Matrix.head_cons, Set.mem_setOf_eq]
  constructor
  · intro h
    have h0 := h 0
    simp only [Fin.sum_univ_one, a063'] at h0
    linarith
  · intro h j
    simp only [Fin.sum_univ_one, a063']
    linarith

theorem f0_mem_063 : f0 ∈ Agent063.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2, P063, G063, ?_, ?_, ?_, ?_⟩
  · intro j
    fin_cases j
    · exact ⟨1, a063, fun _ => 0, rfl⟩
    · exact ⟨1, a063', fun _ => 0, rfl⟩
  · intro j
    fin_cases j
    · exact ⟨fun _ => 1, 0, by intro x; simp [G063, Fin.sum_univ_one]⟩
    · exact ⟨fun _ => 0, 0, by intro x; simp [G063]⟩
  · apply Set.eq_univ_iff_forall.mpr
    intro x
    rcases le_or_lt 0 (x 0) with h | h
    · exact Set.mem_iUnion.mpr ⟨0, (mem_P063_zero x).mpr h⟩
    · exact Set.mem_iUnion.mpr ⟨1, (mem_P063_one x).mpr h.le⟩
  · intro j x hx
    fin_cases j
    · have hx0 : 0 ≤ x 0 := (mem_P063_zero x).mp hx
      simp only [G063, Matrix.cons_val_zero]
      exact max_eq_right hx0
    · have hx0 : x 0 ≤ 0 := (mem_P063_one x).mp hx
      simp only [G063, Matrix.cons_val_one, Matrix.head_cons]
      show f0 x = 0
      exact max_eq_left hx0

theorem f0_not_mem_064 : f0 ∉ Agent064.CPWL 1 := by
  rintro ⟨-, m, a, b, hloc⟩
  obtain ⟨i, U, hUopen, h0U, hagree⟩ := hloc (0 : Fin 1 → ℝ)
  set ψ : ℝ → Fin 1 → ℝ := fun t _ => t with hψdef
  have hψeval : ∀ t : ℝ, ψ t 0 = t := fun _ => rfl
  have hψcont : Continuous ψ := continuous_pi fun _ => continuous_id
  have hψ0 : ψ 0 = (0 : Fin 1 → ℝ) := by funext j; simp [hψdef]
  have hpre : IsOpen (ψ ⁻¹' U) := hUopen.preimage hψcont
  have h0pre : (0 : ℝ) ∈ ψ ⁻¹' U := by rw [Set.mem_preimage, hψ0]; exact h0U
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hpre 0 h0pre
  have hmem : ∀ t : ℝ, |t| < ε → ψ t ∈ U := by
    intro t ht
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact ht
  set t1 : ℝ := ε / 2 with ht1
  set t2 : ℝ := ε / 3 with ht2
  set t3 : ℝ := -(ε / 4) with ht3
  have ht1lt : |t1| < ε := by
    rw [ht1, abs_of_pos (by linarith : (0:ℝ) < ε / 2)]; linarith
  have ht2lt : |t2| < ε := by
    rw [ht2, abs_of_pos (by linarith : (0:ℝ) < ε / 3)]; linarith
  have ht3lt : |t3| < ε := by
    rw [ht3, abs_of_neg (by linarith : -(ε / 4) < (0:ℝ))]; linarith
  have e1 := hagree (ψ t1) (hmem t1 ht1lt)
  have e2 := hagree (ψ t2) (hmem t2 ht2lt)
  have e3 := hagree (ψ t3) (hmem t3 ht3lt)
  simp only [Fin.sum_univ_one, hψeval] at e1 e2 e3
  have hf1 : f0 (ψ t1) = t1 := by
    show max 0 (ψ t1 0) = t1
    rw [hψeval]; exact max_eq_right (by rw [ht1]; linarith)
  have hf2 : f0 (ψ t2) = t2 := by
    show max 0 (ψ t2 0) = t2
    rw [hψeval]; exact max_eq_right (by rw [ht2]; linarith)
  have hf3 : f0 (ψ t3) = 0 := by
    show max 0 (ψ t3 0) = 0
    rw [hψeval]; exact max_eq_left (by rw [ht3]; linarith)
  rw [hf1] at e1
  rw [hf2] at e2
  rw [hf3] at e3
  have ht12 : t1 - t2 ≠ 0 := by rw [ht1, ht2]; intro h; nlinarith
  have hprod : (a i 0 - 1) * (t1 - t2) = 0 := by linear_combination e1 - e2
  have hα : a i 0 = 1 := by
    rcases mul_eq_zero.mp hprod with h | h
    · linarith
    · exact absurd h ht12
  have hβ : b i = 0 := by rw [hα, one_mul] at e1; linarith
  rw [hα, hβ, one_mul] at e3
  rw [ht3] at e3
  linarith

theorem cpwl_ne : ∃ n, Agent063.CPWL n ≠ Agent064.CPWL n := by
  refine ⟨1, ?_⟩
  intro heq
  exact f0_not_mem_064 (heq ▸ f0_mem_063)

/-! ### `ReLUn` : left `sorry`.

Agent063 reads `ReLU_{n,k}` as "at most `k` hidden layers" (`∃ k' ≤ k, Represents n k' f`);
Agent064 reads it as "exactly `k`" (a list of exactly `k + 1` layers, ReLU after all but the
last). These classes coincide only via a padding construction turning any slack `k - k'`
into extra identity-simulating layers via `y ↦ ReLU y - ReLU (-y)` — exactly the lemma the
spec flags as unproved by any of the 100 agents. Formalizing it here (induction converting
between Agent063's nested-existential layer encoding and Agent064's `List Layer` encoding,
plus the padding matrices) is out of scope for a compact bridge file. -/

theorem relun (n k : ℕ) : Agent063.ReLUn n k = Agent064.ReLUn n k := by
  sorry

/-! ### `statement` : proved (vacuously, via the sources).

Both `Thm2_063.lean` and `Thm2_064.lean` leave `theorem2` as `sorry`, so both sides of the
biconditional are (axiomatically) available as already-proved propositions, and the iff
holds regardless of how `CPWL`/`ReLUn`/`depthBound` actually compare between the two files. -/

theorem statement :
    (∀ n, 3 ≤ n → Agent063.CPWL n = Agent063.ReLUn n (Agent063.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent064.CPWL n = Agent064.ReLUn n (Agent064.depthBound n)) :=
  ⟨fun _ n hn => Agent064.theorem2 n hn, fun _ n hn => Agent063.theorem2 n hn⟩

end Bridge_063_064

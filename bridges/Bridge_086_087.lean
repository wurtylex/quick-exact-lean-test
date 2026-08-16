namespace Bridge_086_087

/-!
`depthBound` is literally the same closed formula in both files
(`Nat.ceil (Real.logb 3 ((n:ℝ) - 1)) + 1`, `⌈·⌉₊` being notation for `Nat.ceil`),
so `depth` is proved by `rfl`.

For `CPWL`, 086 uses a genuine polyhedral-subdivision reading (family (a) of the
spec) while 087 uses the "local agreement with a fixed finite family of affine
maps" reading (family (b)). These differ: the one-dimensional kink
`x ↦ max 0 (x 0)` is a bona fide two-piece polyhedral CPWL function (086), but it
is *not* locally affine at `0` (087) since it switches formula on every
neighbourhood of `0`. This refutes `cpwl`.

`ReLUn` and `statement` are left `sorry` — see the comments at those theorems.
-/

/-- Auxiliary counterexample: the one-dimensional ReLU-shaped kink. -/
abbrev kink : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

theorem kink_mem_086 : kink ∈ Agent086.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2,
    ![{x : Fin 1 → ℝ | 0 ≤ x 0}, {x : Fin 1 → ℝ | x 0 ≤ 0}],
    ![(![(1:ℝ)] : Fin 1 → ℝ), ![(0:ℝ)]], ![(0:ℝ), (0:ℝ)], ?_, ?_, ?_⟩
  · intro j
    fin_cases j
    · refine ⟨1, ![(![(-1:ℝ)] : Fin 1 → ℝ)], ![(0:ℝ)], ?_⟩
      ext x
      simp only [Set.mem_setOf_eq, Fin.forall_fin_one, Fin.sum_univ_one,
        Matrix.cons_val_zero]
      constructor <;> intro h <;> linarith
    · refine ⟨1, ![(![(1:ℝ)] : Fin 1 → ℝ)], ![(0:ℝ)], ?_⟩
      ext x
      simp only [Set.mem_setOf_eq, Fin.forall_fin_one, Fin.sum_univ_one,
        Matrix.cons_val_zero]
  · apply Set.eq_univ_of_forall
    intro x
    rcases le_total 0 (x 0) with h | h
    · exact Set.mem_iUnion.mpr ⟨0, h⟩
    · exact Set.mem_iUnion.mpr ⟨1, h⟩
  · intro j
    fin_cases j
    · intro x hx
      simp only [Matrix.cons_val_zero, Set.mem_setOf_eq] at hx
      simp [kink, Fin.sum_univ_one, max_eq_right hx]
    · intro x hx
      simp only [Matrix.cons_val_one, Matrix.head_cons, Set.mem_setOf_eq] at hx
      simp [kink, Fin.sum_univ_one, max_eq_left hx]

/-- No affine functional can agree with `kink` on a whole neighbourhood of `0`:
it is `x 0` for `x 0 ≥ 0` and `0` for `x 0 ≤ 0`, and any neighbourhood of `0`
contains points of both signs. -/
theorem kink_not_locally_affine (c : Fin 1 → ℝ) (b0 : ℝ)
    (h : ∀ᶠ y in nhds (0 : Fin 1 → ℝ), kink y = (∑ i, c i * y i) + b0) : False := by
  rw [Metric.eventually_nhds_iff] at h
  obtain ⟨ε, hε, hball⟩ := h
  have hd : ∀ t : ℝ, |t| < ε → dist (fun _ : Fin 1 => t) (0 : Fin 1 → ℝ) < ε := by
    intro t ht
    rw [dist_pi_lt_iff hε]
    intro b
    simpa [Real.dist_eq] using ht
  have h0 := hball (hd 0 (by simpa using hε))
  have hb0 : b0 = 0 := by simpa [kink, Fin.sum_univ_one] using h0
  have hp := hball (hd (ε / 2) (by rw [abs_of_pos (by linarith)]; linarith))
  have heq : (ε / 2 : ℝ) = c 0 * (ε / 2) + b0 := by
    simpa [kink, Fin.sum_univ_one,
      max_eq_right (by linarith : (0:ℝ) ≤ ε / 2)] using hp
  rw [hb0, add_zero] at heq
  have hc0 : c 0 = 1 :=
    mul_right_cancel₀ (show (ε / 2 : ℝ) ≠ 0 by positivity)
      (by rw [one_mul]; exact heq.symm)
  have hm := hball (hd (-(ε / 2)) (by rw [abs_of_neg (by linarith)]; linarith))
  have hcontra : (0 : ℝ) = -(ε / 2) := by
    simpa [kink, Fin.sum_univ_one, hc0, hb0,
      max_eq_left (by linarith : -(ε / 2 : ℝ) ≤ 0)] using hm
  linarith

theorem kink_not_mem_087 : kink ∉ Agent087.CPWL 1 := by
  rintro ⟨-, r, a, haff, hloc⟩
  obtain ⟨i, hi⟩ := hloc (0 : Fin 1 → ℝ)
  obtain ⟨c, b0, hab⟩ := haff i
  rw [hab] at hi
  exact kink_not_locally_affine c b0 hi

/-- **Refutation.** `086`'s polyhedral-subdivision `CPWL` and `087`'s
local-agreement `CPWL` disagree already at `n = 1`: `kink` belongs to the former
but not the latter. -/
theorem cpwl_ne : ∃ n, Agent086.CPWL n ≠ Agent087.CPWL n :=
  ⟨1, fun he => kink_not_mem_087 (he ▸ kink_mem_086)⟩

/-- Both files write the depth bound as the literal same closed-form
expression `Nat.ceil (Real.logb 3 ((n:ℝ) - 1)) + 1` (`⌈·⌉₊` is notation for
`Nat.ceil`), so the two definitions are definitionally equal. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) :
    Agent086.depthBound n = Agent087.depthBound n := rfl

/-- SORRY: `Agent086.ReLUn n k` is "at most `k` hidden layers" (a union over
`k' ≤ k`) built from raw-function affine maps, while `Agent087.ReLUn n k` is
"exactly `k` hidden layers" (`Represents`) built from `Matrix`-typed affine
maps with a bare scalar output instead of a `Fin 1`-wrapped one. Relating them
needs (a) a translation between the two concrete affine-map encodings and
(b) the "pad a network with an identity layer via `ReLU x - ReLU (-x) = x`"
lemma, which the task spec explicitly notes nobody has proved; not attempted
here. -/
theorem relun (n k : ℕ) : Agent086.ReLUn n k = Agent087.ReLUn n k := by
  sorry

/-- SORRY: this would follow if both agents' own (`sorry`-ed) `theorem2`
statements were known to have the same truth value, but establishing that
without routing through either `theorem2` would require independently
reproving Theorem 2 itself (or a comparably deep argument); left open. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent086.CPWL n = Agent086.ReLUn n (Agent086.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent087.CPWL n = Agent087.ReLUn n (Agent087.depthBound n)) := by
  sorry

end Bridge_086_087

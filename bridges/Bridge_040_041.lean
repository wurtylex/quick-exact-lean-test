namespace Bridge_040_041

/-!
## Summary of the comparison

* `CPWL` differs genuinely between the two agents:
  - `Agent040.CPWL` requires *local* agreement with a member of the affine
    family: `∀ x, ∃ T ∈ S, ∀ᶠ y in nhds x, f y = T.eval y 0`.
  - `Agent041.CPWL` only requires *pointwise* agreement:
    `∀ x, ∃ j, f x = g j x`, with no neighbourhood condition.
  These are genuinely different conditions: the coordinate function
  `x ↦ max 0 (x 0)` is a pointwise selection between the zero function and the
  first-coordinate projection everywhere, but it does *not* locally agree with
  either affine piece in any neighbourhood of a point where the first
  coordinate is `0` (exactly the phenomenon flagged in `BRIDGE_SPEC.md`).
  So `cpwl` is refuted below (`cpwl_ne`).

* `depthBound` agrees: `Agent041` computes `Real.logb 3` of the *truncated
  natural subtraction* `↑(n - 1)` cast to `ℝ`, while `Agent040` computes
  `Real.logb 3` of `(↑n - 1 : ℝ)`. For `n ≥ 3` (in particular `1 ≤ n`),
  `Nat.cast_sub` shows these arguments are equal, so `depth` is proved below.

* `ReLUn` and `statement` are left `sorry`; see the comments immediately above
  each for exactly what is missing and why.
-/

/-- The "kinked" function `x ↦ max 0 (x 0)` on `ℝ^1`, used to separate the two
`CPWL` encodings: it is a valid pointwise selection between two affine pieces
everywhere, but fails to *locally* coincide with either piece near the point
where the first coordinate vanishes. -/
theorem cpwl_ne : ∃ n, Agent040.CPWL n ≠ Agent041.CPWL n := by
  refine ⟨1, ?_⟩
  set f : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0) with hf_def
  have hf_cont : Continuous f := continuous_const.max (continuous_apply 0)
  -- `f` is a pointwise selection of two affine pieces, hence lies in `Agent041.CPWL 1`.
  have hf_mem041 : f ∈ Agent041.CPWL 1 := by
    refine ⟨hf_cont, 2, ![fun _ : Fin 1 → ℝ => (0 : ℝ), fun x : Fin 1 → ℝ => x 0], ?_, ?_⟩
    · intro j
      fin_cases j <;>
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      · exact ⟨fun _ => 0, 0, by intro x; simp⟩
      · exact ⟨fun _ => 1, 0, by intro x; simp [Fin.sum_univ_one]⟩
    · intro x
      rcases le_or_lt 0 (x 0) with hx | hx
      · exact ⟨1, by
          simp only [Matrix.cons_val_one, Matrix.head_cons, hf_def, max_eq_right hx]⟩
      · exact ⟨0, by
          simp only [Matrix.cons_val_zero, hf_def, max_eq_left hx.le]⟩
  -- `f` does *not* locally agree with a single affine piece near the origin,
  -- so it is excluded from `Agent040.CPWL 1`.
  have hf_not_mem040 : f ∉ Agent040.CPWL 1 := by
    rintro ⟨-, S, hS⟩
    obtain ⟨T, -, hev⟩ := hS (fun _ : Fin 1 => (0 : ℝ))
    -- Pull the eventual equality back to a real neighbourhood of `0` along the
    -- continuous embedding `t ↦ (fun _ => t) : ℝ → (Fin 1 → ℝ)`.
    set ψ : ℝ → (Fin 1 → ℝ) := fun t _ => t with hψ_def
    have hψ_cont : Continuous ψ := continuous_pi (fun _ => continuous_id)
    have hψ0 : ψ 0 = fun _ : Fin 1 => (0 : ℝ) := rfl
    have htendsto : Filter.Tendsto ψ (nhds (0 : ℝ)) (nhds (fun _ : Fin 1 => (0 : ℝ))) := by
      rw [← hψ0]; exact hψ_cont.tendsto 0
    have hcomp : ∀ᶠ t in nhds (0 : ℝ), f (ψ t) = T.eval (ψ t) 0 := htendsto.eventually hev
    have hcomp' : ∀ᶠ t in nhds (0 : ℝ), max 0 t = T.A 0 0 * t + T.c 0 := by
      filter_upwards [hcomp] with t ht
      have e1 : f (ψ t) = max 0 t := by simp [hf_def, hψ_def]
      have e2 : T.eval (ψ t) 0 = T.A 0 0 * t + T.c 0 := by
        simp [Agent040.Affine.eval, hψ_def, Fin.sum_univ_one]
      rw [e1, e2] at ht; exact ht
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hcomp'
    have hball' : ∀ t : ℝ, |t| < ε → max 0 t = T.A 0 0 * t + T.c 0 := by
      intro t ht
      apply hball
      rw [Real.dist_eq, sub_zero]; exact ht
    -- evaluate at `t = 0`, `t = ε/2`, `t = -ε/2` to pin down the (would-be)
    -- affine coefficients and derive a contradiction.
    have hεhalf : (0 : ℝ) < ε / 2 := by linarith
    have hc : T.c 0 = 0 := by
      have h0 := hball' 0 (by rw [abs_zero]; exact hε)
      rw [max_self, mul_zero, zero_add] at h0
      exact h0.symm
    have hp := hball' (ε / 2) (by rw [abs_of_pos hεhalf]; linarith)
    have hn := hball' (-(ε / 2)) (by
      rw [abs_of_neg (show (-(ε / 2) : ℝ) < 0 by linarith)]; linarith)
    rw [hc, add_zero] at hp hn
    rw [max_eq_right hεhalf.le] at hp
    rw [max_eq_left (show (-(ε / 2) : ℝ) ≤ 0 by linarith)] at hn
    rw [mul_neg] at hn
    have hzero : T.A 0 0 * (ε / 2) = 0 := by linarith
    rw [hzero] at hp
    linarith
  intro hEq
  exact hf_not_mem040 (by rw [hEq]; exact hf_mem041)

/-- Both agents encode `⌈log_3(n-1)⌉ + 1`; `Agent041` first truncates the
subtraction in `ℕ` and then casts, `Agent040` casts first and subtracts in
`ℝ`. For `n ≥ 3` (so in particular `1 ≤ n`) `Nat.cast_sub` identifies the two
arguments to `Real.logb`, hence the two ceilings agree. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent040.depthBound n = Agent041.depthBound n := by
  have h1 : (1 : ℕ) ≤ n := by omega
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub h1, Nat.cast_one]
  simp only [Agent040.depthBound, Agent041.depthBound, hcast]

/-
`relun` is left `sorry`.

`Agent040.ReLUn n k` is `NetworkComputes k n f`, built by peeling the *first*
(input-side) affine layer off `f` and recursing on the remainder — the base
case `k = 0` is a single affine map `ℝ^n → ℝ`, and this is an *exact* `k`
reading (no existential over depth).

`Agent041.ReLUn n k` is `∃ k' ≤ k, ∃ F, NetFunc k' n 1 F ∧ f = …`, where
`NetFunc` is built by peeling the *last* (output-side) affine layer off `F`
and recursing on the remainder, and the whole thing is wrapped in an
existential over `k' ≤ k` (an *at most* `k` reading).

Bridging these requires two independent, nontrivial results, neither of which
is available "for free":

1. A structural induction showing that "peel the first layer, recurse" and
   "peel the last layer, recurse" describe the *same* class of
   exactly-`k`-hidden-layer functions (an associativity-of-composition
   argument, akin to relating `foldl`/`foldr` decompositions of the same
   chain of affine/ReLU blocks).
2. The monotonicity/padding lemma flagged in `BRIDGE_SPEC.md`: that
   `Agent040`'s "exactly `k`" reading is monotone in `k` (via the identity
   emulation `x = ReLU x - ReLU (-x)`), which is what is needed to reconcile
   an *exact*-`k` family with an *at-most*-`k` family. This lemma is stated as
   unproved by the spec and by `Agent040`'s and `Agent041`'s own comments.

Neither (1) nor (2) is proved here or elsewhere in either source file, so a
correct proof or refutation of `relun` is left for future work rather than
risking a bogus proof.
-/
theorem relun (n k : ℕ) : Agent040.ReLUn n k = Agent041.ReLUn n k := sorry

/-
`statement` is left `sorry`.

The left-hand side of the iff is very likely false in isolation: by the same
argument used for `cpwl_ne` above (applied at the point where the relevant
coordinate vanishes, and using that `relu` is idempotent so the "kinked"
coordinate function is representable with *exactly* any number `≥ 2` of
hidden layers, not just the minimal one), the coordinate function
`x ↦ max 0 (x 0)` should witness `Agent040.CPWL n ≠ Agent040.ReLUn n
(Agent040.depthBound n)` for every `n ≥ 3`, refuting `Agent040`'s own
rendering of Theorem 2 outright. That argument has not been fully carried out
here (it needs the idempotence-of-`relu` padding argument sketched for
`relun` above, restricted to this one specific function, which is more
tractable than the general lemma but still nontrivial), so it is not asserted
as an established fact.

Even granting that, resolving the stated `iff` requires knowing the truth
value of the right-hand side — whether Theorem 2 actually holds under
`Agent041`'s "pointwise selection" `CPWL` and "at most `k`" `ReLUn`
encodings. That is precisely the mathematical content of the paper's Theorem
2 (left as `sorry` in `Thm2_041.lean` itself) and is out of scope for a
bridge between two formalizations.
-/
theorem statement :
    (∀ n, 3 ≤ n → Agent040.CPWL n = Agent040.ReLUn n (Agent040.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent041.CPWL n = Agent041.ReLUn n (Agent041.depthBound n)) := sorry

end Bridge_040_041

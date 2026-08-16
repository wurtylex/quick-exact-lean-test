namespace Bridge_021_022

/-!
## Comparing `Agent021` and `Agent022`

* `depthBound`: both agents write `⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1` verbatim (021 uses the
  `⌈·⌉₊` notation, 022 spells it `Nat.ceil`, which is the same notation unfolds to) —
  the two definitions are literally the same term, so `depth` is `rfl`.
* `ReLUn`/`ComputesReLU`/`ExactReLUComputable`: both agents model "at most `k` hidden
  layers" via the identical alternating affine/ReLU composition, just packaged once as
  an inductive predicate (021) and once as a `Nat`-recursive `def` (022), and with the
  affine-map structure's bias field named `b` vs `c`. We build an explicit bridge between
  the two computability predicates and get `relun` for free.
* `CPWL`: 021 uses the standard *global polyhedral subdivision* reading. 022 uses a
  *local* reading (`∀ x, ∃ i, ∀ᶠ y near x, f y = affine_i y`). We show (via a direct
  neighbourhood computation, no need for the general connectedness argument) that the
  one-dimensional ReLU function `x ↦ max 0 (x 0)` is a genuine two-piece polyhedral CPWL
  function in 021's sense, but *fails* 022's local condition at the kink `x = 0`: any
  neighbourhood of `0` contains points on both sides of the kink, and no single affine
  function can agree with `f` on both a positive and a negative point while also matching
  `f 0 = 0`. Hence `CPWL021 1 ≠ CPWL022 1`, and `cpwl` is refuted.
-/

/-- Convert an `Agent021`-style affine map to an `Agent022`-style one (same matrix, bias
field renamed `b ↦ c`). -/
def cast0221 {n m : ℕ} (T : Agent021.AffineMap n m) : Agent022.AffineMap' n m :=
  ⟨T.A, T.b⟩

/-- Convert an `Agent022`-style affine map to an `Agent021`-style one (same matrix, bias
field renamed `c ↦ b`). -/
def cast0210 {n m : ℕ} (T : Agent022.AffineMap' n m) : Agent021.AffineMap n m :=
  ⟨T.A, T.c⟩

lemma apply_cast0221 {n m : ℕ} (T : Agent021.AffineMap n m) (x : Fin n → ℝ) :
    (cast0221 T).apply x = T.apply x := by
  simp [cast0221, Agent021.AffineMap.apply, Agent022.AffineMap'.apply]

lemma apply_cast0210 {n m : ℕ} (T : Agent022.AffineMap' n m) (x : Fin n → ℝ) :
    (cast0210 T).apply x = T.apply x := by
  simp [cast0210, Agent021.AffineMap.apply, Agent022.AffineMap'.apply]

lemma reluVec_eq {m : ℕ} (x : Fin m → ℝ) :
    Agent021.reluVec x = Agent022.reluVec x := by
  funext j
  simp [Agent021.reluVec, Agent021.relu, Agent022.reluVec, Agent022.relu]

/-- Every function computed by an `Agent021`-style network with exactly `k` hidden layers
is also computed, in `Agent022`'s sense, with exactly `k` hidden layers. -/
lemma computes_to_exact {n k : ℕ} {f : (Fin n → ℝ) → ℝ} :
    Agent021.ComputesReLU n k f → Agent022.ExactReLUComputable k n f
  | .base T => by
      refine ⟨fun j => T.A 0 j, T.b 0, fun x => ?_⟩
      show T.apply x 0 = (∑ j, T.A 0 j * x j) + T.b 0
      simp [Agent021.AffineMap.apply, Matrix.mulVec, Matrix.dotProduct]
  | .step T hg => by
      refine ⟨_, cast0221 T, _, computes_to_exact hg, ?_⟩
      funext x
      simp only [Function.comp_apply, apply_cast0221, reluVec_eq]

/-- Converse of `computes_to_exact`. -/
lemma exact_to_computes {n : ℕ} : ∀ (k : ℕ) {f : (Fin n → ℝ) → ℝ},
    Agent022.ExactReLUComputable k n f → Agent021.ComputesReLU n k f
  | 0, f, h => by
      obtain ⟨w, b, hf⟩ := h
      have hT : f = fun x => (⟨fun _ j => w j, fun _ => b⟩ : Agent021.AffineMap n 1).apply x 0 := by
        funext x
        rw [hf x]
        simp [Agent021.AffineMap.apply, Matrix.mulVec, Matrix.dotProduct]
      rw [hT]
      exact Agent021.ComputesReLU.base _
  | (k + 1), f, h => by
      obtain ⟨m, T, g, hg, hf⟩ := h
      have hstep := Agent021.ComputesReLU.step (cast0210 T) (exact_to_computes k hg)
      rw [hf]
      have heq : g ∘ Agent022.reluVec ∘ T.apply
               = fun x => g (Agent021.reluVec ((cast0210 T).apply x)) := by
        funext x
        simp only [Function.comp_apply]
        rw [apply_cast0210, reluVec_eq]
      rw [heq]
      exact hstep

/-- **`ReLUn` bridge.** Both agents read `ReLUn n k` as "at most `k` hidden layers", built
from computability predicates that we have just shown are pointwise equivalent. -/
theorem relun (n k : ℕ) : Agent021.ReLUn n k = Agent022.ReLUn n k := by
  ext g
  constructor
  · rintro ⟨j, hj, hg⟩
    exact ⟨j, hj, computes_to_exact hg⟩
  · rintro ⟨j, hj, hg⟩
    exact ⟨j, hj, exact_to_computes j hg⟩

/-- **`depthBound` bridge.** Both agents write the exact same term
`⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1` (`⌈·⌉₊` is notation for `Nat.ceil`). -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent021.depthBound n = Agent022.depthBound n := rfl

/-- **`CPWL` refutation.** The one-dimensional ReLU function is a genuine two-piece
polyhedral CPWL function for `Agent021`, but is not locally affine at its kink `x = 0`
in `Agent022`'s sense. -/
theorem cpwl_ne : ∃ n, Agent021.CPWL n ≠ Agent022.CPWL n := by
  refine ⟨1, fun hEq => ?_⟩
  have hmem : (fun x : Fin 1 → ℝ => max (0:ℝ) (x 0)) ∈ Agent021.CPWL 1 := by
    refine ⟨continuous_const.max (continuous_apply 0), 2,
      ![{x : Fin 1 → ℝ | x 0 ≤ 0}, {x : Fin 1 → ℝ | 0 ≤ x 0}],
      ![(fun _ : Fin 1 => (0:ℝ)), fun _ : Fin 1 => (1:ℝ)],
      ![(0:ℝ), (0:ℝ)], ?_, ?_, ?_⟩
    · intro i
      fin_cases i
      · simp only [Matrix.cons_val_zero]
        refine ⟨1, fun _ _ => (1:ℝ), fun _ => (0:ℝ), ?_⟩
        ext x
        simp only [Set.mem_setOf_eq]
        constructor
        · intro h l
          fin_cases l
          simp only [Fin.sum_univ_one]
          linarith [h]
        · intro h
          have h0 := h 0
          simp only [Fin.sum_univ_one] at h0
          linarith
      · simp only [Matrix.cons_val_one]
        refine ⟨1, fun _ _ => (-1:ℝ), fun _ => (0:ℝ), ?_⟩
        ext x
        simp only [Set.mem_setOf_eq]
        constructor
        · intro h l
          fin_cases l
          simp only [Fin.sum_univ_one]
          linarith [h]
        · intro h
          have h0 := h 0
          simp only [Fin.sum_univ_one] at h0
          linarith
    · ext x
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      rcases le_or_lt (x 0) 0 with h | h
      · exact ⟨0, by simpa [Matrix.cons_val_zero] using h⟩
      · exact ⟨1, by simpa [Matrix.cons_val_one] using h.le⟩
    · intro i
      fin_cases i
      · intro x hx
        simp only [Matrix.cons_val_zero, Set.mem_setOf_eq] at hx
        simp only [Matrix.cons_val_zero, Fin.sum_univ_one]
        rw [max_eq_left_iff.mpr hx]
        ring
      · intro x hx
        simp only [Matrix.cons_val_one, Set.mem_setOf_eq] at hx
        simp only [Matrix.cons_val_one, Fin.sum_univ_one]
        rw [max_eq_right_iff.mpr hx]
        ring
  rw [hEq] at hmem
  obtain ⟨-, m, w, b, hloc⟩ := hmem
  obtain ⟨i, U, hU, hfU⟩ := hloc (fun _ => (0:ℝ))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  have h0mem : (fun _ : Fin 1 => (0:ℝ)) ∈ U := hball (Metric.mem_ball_self hε)
  have h1mem : (fun _ : Fin 1 => (ε / 2 : ℝ)) ∈ U := by
    apply hball
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro j
    simp only [Real.dist_eq, sub_zero]
    rw [abs_of_pos (by linarith : (0:ℝ) < ε / 2)]
    linarith
  have h2mem : (fun _ : Fin 1 => (-(ε / 2) : ℝ)) ∈ U := by
    apply hball
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro j
    simp only [Real.dist_eq, sub_zero]
    rw [abs_of_neg (by linarith : (-(ε / 2) : ℝ) < 0)]
    linarith
  have e0 := hfU _ h0mem
  have e1 := hfU _ h1mem
  have e2 := hfU _ h2mem
  simp only [Fin.sum_univ_one] at e0 e1 e2
  have hεpos : (0:ℝ) < ε / 2 := by linarith
  have hb : b i = 0 := by
    have hmax0 : max (0:ℝ) 0 = 0 := max_self 0
    rw [hmax0, mul_zero, zero_add] at e0
    exact e0.symm
  have hm1 : max (0:ℝ) (ε / 2) = ε / 2 := max_eq_right_iff.mpr (by linarith)
  have hm2 : max (0:ℝ) (-(ε / 2)) = 0 := max_eq_left_iff.mpr (by linarith)
  rw [hm1, hb] at e1
  rw [hm2, hb] at e2
  have e1' : w i 0 * (ε / 2) = ε / 2 := by linarith [e1]
  have e2' : w i 0 * (-(ε / 2)) = 0 := by linarith [e2]
  have hw1 : w i 0 = 1 := by
    have expand : (w i 0 - 1) * (ε / 2) = w i 0 * (ε / 2) - ε / 2 := by ring
    have hz : (w i 0 - 1) * (ε / 2) = 0 := by rw [expand]; linarith [e1']
    rcases mul_eq_zero.mp hz with h | h
    · linarith
    · exfalso; linarith
  rw [hw1] at e2'
  linarith [e2']

/-- **`statement` obligation.**
Using `relun` and `depth`, the ReLU-side set `Agent021.ReLUn n (Agent021.depthBound n)`
and `Agent022.ReLUn n (Agent022.depthBound n)` literally coincide as sets for every `n`.
So the stated iff reduces to
`(∀ n, 3 ≤ n → Agent021.CPWL n = R n) ↔ (∀ n, 3 ≤ n → Agent022.CPWL n = R n)`
for this common set `R n`. The proof of `cpwl_ne` above shows (and the same
neighbourhood argument generalises to every `n ≥ 3`, e.g. by extending the kink function
to `x ↦ max 0 (x 0)` on `Fin n → ℝ`) that the *right* side is false: `Agent022.CPWL n`
consists only of functions that are locally affine at every point, which forces (by a
connectedness argument on the finitely many affine pieces) `Agent022.CPWL n` to be just
the affine functions, while `R n` already contains the non-affine ReLU-representable
function `x ↦ max 0 (x 0)` as soon as `depthBound n ≥ 1` (always true). So proving
`statement` outright would require proving `¬(∀ n, 3 ≤ n → Agent021.CPWL n = R n)`, i.e.
that `Agent021`'s formalization of Theorem 2 (the polyhedral-subdivision reading, which
looks like the mathematically correct/standard one) is actually *false* — equivalently,
proving `statement_ne` would require proving the *actual, hard* Theorem 2 for `Agent021`'s
encoding. Neither is in scope of a definitional bridge between two formalizations, so we
leave this as `sorry`. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent021.CPWL n = Agent021.ReLUn n (Agent021.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent022.CPWL n = Agent022.ReLUn n (Agent022.depthBound n)) := by
  sorry

end Bridge_021_022

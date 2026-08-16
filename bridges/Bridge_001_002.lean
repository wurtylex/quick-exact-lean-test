namespace Bridge_001_002

/-!
## Summary of the comparison

* `depthBound`: Agent001 casts `n - 1` (truncated ℕ subtraction) to `ℝ` before taking
  `logb`; Agent002 casts `n` to `ℝ` first and subtracts `1` in `ℝ`. For `n ≥ 3` (in fact
  for `n ≥ 1`) these coincide via `Nat.cast_sub`. **PROVED**.
* `ReLUn`: both agents define "exactly `k` hidden layers" by the *same* recursion, and
  their `AffineMap`/`Affine` structures are literally the same pair of fields
  (`A : Matrix (Fin b) (Fin a) ℝ`, `c : Fin b → ℝ`) evaluated by the same formula
  `A.mulVec x + c`, and their `relu`/`reluVec` are both `max 0 ·` applied componentwise.
  So the two notions of "representable by a ReLU net" coincide for every `n k`. **PROVED**.
* `CPWL`: Agent001 uses a genuine polyhedral-subdivision definition (family (a) in the
  spec); Agent002 uses the "local agreement with *some* affine function in a ball around
  each point" definition (family (b)). These are *not* the same: `f = fun x => max 0 (x 0)`
  is CPWL under Agent001's definition (two half-spaces `x 0 ≥ 0` / `x 0 ≤ 0`) but fails
  Agent002's definition at `x = 0`, since no single affine function can agree with `f` on
  a whole ball around `0` (it would have to equal `t` for small `t > 0` and `0` for small
  `t < 0` simultaneously, which pins down the affine function on the positive side and then
  contradicts the negative side). **REFUTED**.
* `statement`: this is the biconditional of the two agents' (still-`sorry`ed) Theorem 2
  statements, quantified over `n ≥ 3`. Since `ReLUn`/`depthBound` agree (above) but `CPWL`
  differs (above, and the same counterexample works for every `n ≥ 1`, in particular for
  `n ≥ 3`), the right-hand side of the biconditional (Agent002's statement) is false
  precisely when Agent002's `ReLUn n (depthBound n)` contains some function that is *not*
  local-agreement-CPWL for some `n ≥ 3` (e.g. `max 0 (x 0)`, which one can build with the
  right number of layers by "padding" a redundant layer). Establishing that rigorously,
  and independently determining the truth value of Agent001's (mathematically faithful)
  statement, amounts to reproving the paper's actual Theorem 2 for each encoding — genuine
  new mathematics well beyond what a single bridge file can respect. **SORRY**.
-/

/-! ### `depthBound` -/

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent001.depthBound n = Agent002.depthBound n := by
  have h1 : (1 : ℕ) ≤ n := by omega
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub h1, Nat.cast_one]
  simp only [Agent001.depthBound, Agent002.depthBound, hcast]

/-! ### `ReLUn` -/

/-- The two "computed by a ReLU network with exactly `k` hidden layers" predicates agree,
by induction on `k`. The base case converts between Agent001's `(a, b)`-pair encoding of
an affine functional and Agent002's `Affine n 1` structure (built from the very same kind
of data, `A : Matrix _ _ ℝ` and `c : _ → ℝ`); the successor case simply transports the
witnessing affine map `T` across the (field-for-field identical) `AffineMap`/`Affine`
structures and uses that `reluVec`/`relu` are definitionally the same on both sides. -/
private lemma isReLUNet_iff (n k : ℕ) (f : (Fin n → ℝ) → ℝ) :
    Agent001.IsReLUNet n k f ↔ Agent002.ComputesWithHiddenLayers n k f := by
  induction k generalizing n f with
  | zero =>
      constructor
      · rintro ⟨a, b, hf⟩
        refine ⟨⟨Matrix.of fun _ j => a j, fun _ => b⟩, funext fun x => ?_⟩
        simpa only [Agent002.Affine.eval, Pi.add_apply, Matrix.mulVec, dotProduct,
          Matrix.of_apply] using hf x
      · rintro ⟨T, hf⟩
        refine ⟨fun j => T.A 0 j, T.c 0, fun x => ?_⟩
        simpa only [Agent002.Affine.eval, Pi.add_apply, Matrix.mulVec, dotProduct]
          using congrFun hf x
  | succ k ih =>
      constructor
      · rintro ⟨m, T, g, hg, hf⟩
        refine ⟨m, ⟨T.A, T.c⟩, g, (ih m g).mp hg, funext fun x => ?_⟩
        show f x = g (Agent002.reluVec (Agent002.Affine.eval ⟨T.A, T.c⟩ x))
        exact hf x
      · rintro ⟨m, T, g, hg, hf⟩
        refine ⟨m, ⟨T.A, T.c⟩, g, (ih m g).mpr hg, fun x => ?_⟩
        show f x = g (Agent001.reluVec (Agent001.AffineMap.eval ⟨T.A, T.c⟩ x))
        exact congrFun hf x

theorem relun (n k : ℕ) : Agent001.ReLUn n k = Agent002.ReLUn n k := by
  ext f
  simp only [Agent001.ReLUn, Agent002.ReLUn, Set.mem_setOf_eq]
  exact isReLUNet_iff n k f

/-! ### `CPWL` -/

/-- The counterexample: the one-input-coordinate ReLU function itself. It is CPWL in the
polyhedral-subdivision sense (two half-spaces `x 0 ≥ 0`, `x 0 ≤ 0`), but *not* CPWL in the
local-agreement sense, since no single affine function can agree with it on a whole
neighbourhood of `0`. -/
private noncomputable def exampleF : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

private lemma exampleF_continuous : Continuous exampleF :=
  continuous_const.max (continuous_apply 0)

private lemma exampleF_mem_cpwl1 : exampleF ∈ Agent001.CPWL 1 := by
  refine ⟨exampleF_continuous, 2,
    ![{x : Fin 1 → ℝ | 0 ≤ x 0}, {x : Fin 1 → ℝ | x 0 ≤ 0}],
    ![fun _ => (1 : ℝ), fun _ => (0 : ℝ)], ![(0 : ℝ), (0 : ℝ)], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · refine ⟨1, fun _ => {x : Fin 1 → ℝ | 0 ≤ x 0}, fun _ => ⟨fun _ => (-1 : ℝ), 0, ?_⟩,
        (Set.iInter_const _).symm⟩
      ext x
      simp only [Set.mem_setOf_eq, Fin.sum_univ_one]
      constructor <;> intro h <;> linarith
    · refine ⟨1, fun _ => {x : Fin 1 → ℝ | x 0 ≤ 0}, fun _ => ⟨fun _ => (1 : ℝ), 0, ?_⟩,
        (Set.iInter_const _).symm⟩
      ext x
      simp only [Set.mem_setOf_eq, Fin.sum_univ_one]
      constructor <;> intro h <;> linarith
  · apply Set.eq_univ_iff_forall.mpr
    intro x
    rcases le_total 0 (x 0) with h | h
    · exact Set.mem_iUnion.mpr ⟨0, by simpa using h⟩
    · exact Set.mem_iUnion.mpr ⟨1, by simpa using h⟩
  · intro i x hx
    fin_cases i
    · simp only [Matrix.cons_val_zero, Set.mem_setOf_eq] at hx
      simp only [Matrix.cons_val_zero, Fin.sum_univ_one, exampleF]
      linarith [max_eq_right hx]
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Set.mem_setOf_eq] at hx
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Fin.sum_univ_one, exampleF]
      linarith [max_eq_left hx]

private lemma exampleF_not_mem_cpwl1 : exampleF ∉ Agent002.CPWL 1 := by
  rintro ⟨-, m, g, hloc⟩
  obtain ⟨i, ε, hε, hi⟩ := hloc (fun _ => (0 : ℝ))
  have hdist : ∀ t : ℝ, |t| < ε →
      exampleF (fun _ : Fin 1 => t) = ((g i).eval (fun _ : Fin 1 => t)) 0 := by
    intro t ht
    apply hi
    rw [dist_pi_lt_iff hε]
    intro b
    simpa [Real.dist_eq, sub_zero] using ht
  set a : ℝ := (g i).A 0 0 with ha
  set b : ℝ := (g i).c 0 with hb
  have heval : ∀ t : ℝ, ((g i).eval (fun _ : Fin 1 => t)) 0 = a * t + b := by
    intro t
    simp only [Agent002.Affine.eval, Pi.add_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_one, ha, hb]
  have h1 : ∀ t : ℝ, 0 < t → t < ε → t = a * t + b := by
    intro t ht0 htε
    have hxt : exampleF (fun _ : Fin 1 => t) = ((g i).eval (fun _ : Fin 1 => t)) 0 :=
      hdist t (by rw [abs_of_pos ht0]; exact htε)
    rw [heval] at hxt
    rwa [show exampleF (fun _ : Fin 1 => t) = t from max_eq_right ht0.le] at hxt
  have h2 : ∀ t : ℝ, 0 < t → t < ε → (0 : ℝ) = a * (-t) + b := by
    intro t ht0 htε
    have hlt : |(-t)| < ε := by rw [abs_neg, abs_of_pos ht0]; exact htε
    have hxt : exampleF (fun _ : Fin 1 => (-t)) = ((g i).eval (fun _ : Fin 1 => (-t))) 0 :=
      hdist (-t) hlt
    rw [heval] at hxt
    rwa [show exampleF (fun _ : Fin 1 => (-t)) = 0 from max_eq_left (by linarith)] at hxt
  have e1 : (ε / 2 : ℝ) = a * (ε / 2) + b := h1 (ε / 2) (by linarith) (by linarith)
  have e2 : (0 : ℝ) = a * (-(ε / 2)) + b := h2 (ε / 2) (by linarith) (by linarith)
  have e3 : (ε / 3 : ℝ) = a * (ε / 3) + b := h1 (ε / 3) (by linarith) (by linarith)
  have e4 : (0 : ℝ) = a * (-(ε / 3)) + b := h2 (ε / 3) (by linarith) (by linarith)
  have hb1 : (ε / 2 : ℝ) = 2 * b := by linear_combination e1 + e2
  have hb2 : (ε / 3 : ℝ) = 2 * b := by linear_combination e3 + e4
  linarith [hb1, hb2, hε]

theorem cpwl_ne : ∃ n, Agent001.CPWL n ≠ Agent002.CPWL n :=
  ⟨1, fun h => exampleF_not_mem_cpwl1 (h ▸ exampleF_mem_cpwl1)⟩

/-! ### `statement` -/

-- The right-hand side of this biconditional is false (Agent002's `CPWL` fails to equal
-- `ReLUn _ (depthBound _)`, witnessed by the same `exampleF`-style padding argument
-- described above, e.g. `n = 3`), but the left-hand side is exactly a restatement of the
-- paper's actual Theorem 2 for Agent001's own (faithful) encoding, which neither Agent001
-- nor this bridge proves. Resolving `statement` therefore requires resolving that open
-- `sorry` — genuinely new mathematics, not a bridging fact between the two files.
theorem statement :
    (∀ n, 3 ≤ n → Agent001.CPWL n = Agent001.ReLUn n (Agent001.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent002.CPWL n = Agent002.ReLUn n (Agent002.depthBound n)) := by
  sorry

end Bridge_001_002

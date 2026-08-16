namespace Bridge_052_053

/-!
## Summary

* `depthBound`: both agents write the *literal same* term
  `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`. **PROVED** (by `rfl`).
* `CPWL`: Agent052 uses a genuine polyhedral-subdivision definition (a finite cover of
  `ℝⁿ` by closed polyhedra, `f` affine on each). Agent053 uses "local agreement": every
  point has a metric ball on which `f` coincides with *one globally affine* piece. These
  differ: `kink = fun x => max 0 (x 0)` on `ℝ¹` is CPWL under Agent052's definition (two
  half-spaces `x 0 ≤ 0` and `x 0 ≥ 0`) but *not* under Agent053's, since no single affine
  function can equal `kink` on a whole ball around `0` (it would have to equal `t` for
  small `t > 0` and `0` for small `t < 0` simultaneously). **REFUTED**.
* `ReLUn`: both are "at most `k` hidden layers" built from an "exactly `k` hidden layers"
  notion, but the two "exactly `k`" encodings are structurally very different: Agent052
  represents a network via a global width function `w : ℕ → ℕ` and an indexed family of
  layers with explicit `cast`/`congrArg` transport to line up `w 0 = n` and `w (k+1) = 1`,
  while Agent053 defines the same architecture by clean structural recursion on `k`. They
  almost certainly compute the same class of functions (both encode
  `T^(k+1) ∘ ReLU ∘ ⋯ ∘ ReLU ∘ T^(1)`), but proving it needs an induction that builds an
  explicit dictionary between the cast-laden width-indexed encoding and the recursive one,
  which cannot safely be done without compiler feedback in this budget. **SORRY**.
* `statement`: the right-hand side (Agent053's instance of Theorem 2) is false by the same
  `kink`-style counterexample at, e.g., `n = 3` (it lies in `ReLUn 3 (depthBound 3)` via a
  single hidden layer computing `x ↦ max 0 (x 0)`, but not in Agent053's `CPWL 3`, by the
  same ball argument as above). The left-hand side is literally a restatement of the
  paper's actual Theorem 2 for Agent052's own (faithful) encoding, which neither Agent052
  nor this bridge proves. Resolving the biconditional therefore requires resolving that
  open `sorry` — genuinely new mathematics, not a bridging fact. **SORRY**.
-/

/-! ### `depthBound` -/

theorem depth (n : ℕ) (hn : 3 ≤ n) :
    Agent052.depthBound n = Agent053.depthBound n := rfl

/-! ### `CPWL` -/

/-- The counterexample: the one-input-coordinate ReLU function. It is CPWL in the
polyhedral-subdivision sense (two half-spaces `x 0 ≤ 0`, `x 0 ≥ 0`) but *not* CPWL in the
local-agreement sense, since no single affine function agrees with it on a whole
neighbourhood of `0`. -/
private noncomputable def kink : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

private lemma kink_continuous : Continuous kink :=
  continuous_const.max (continuous_apply 0)

private lemma kink_mem_052 : kink ∈ Agent052.CPWL 1 := by
  refine ⟨kink_continuous, 2, fun _ => 1,
    ![(fun _ => (⟨fun _ => (1 : ℝ), 0⟩ : Agent052.Halfspace 1)),
      (fun _ => (⟨fun _ => (-1 : ℝ), 0⟩ : Agent052.Halfspace 1))],
    ![(⟨fun _ _ => (0 : ℝ), fun _ => (0 : ℝ)⟩ : Agent052.AffMap 1 1),
      (⟨fun _ _ => (1 : ℝ), fun _ => (0 : ℝ)⟩ : Agent052.AffMap 1 1)],
    ?_, ?_⟩
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true, Agent052.Polyhedron,
      Set.mem_iInter, Agent052.Halfspace.set, Set.mem_setOf_eq, Fin.sum_univ_one]
    rcases le_or_lt (x 0) 0 with h | h
    · exact ⟨0, fun _ => by simp only [Matrix.cons_val_zero]; linarith⟩
    · exact ⟨1, fun _ => by simp only [Matrix.cons_val_one, Matrix.head_cons]; linarith⟩
  · intro i x hx
    fin_cases i
    · simp only [Matrix.cons_val_zero, Agent052.Polyhedron, Set.mem_iInter,
        Agent052.Halfspace.set, Set.mem_setOf_eq, Fin.sum_univ_one] at hx
      have hx0 : x 0 ≤ 0 := by have h0 := hx 0; linarith
      simp only [Matrix.cons_val_zero, kink, Agent052.AffMap.eval, Fin.sum_univ_one]
      linarith [max_eq_left hx0]
    · simp only [Matrix.cons_val_one, Matrix.head_cons, Agent052.Polyhedron, Set.mem_iInter,
        Agent052.Halfspace.set, Set.mem_setOf_eq, Fin.sum_univ_one] at hx
      have hx0 : 0 ≤ x 0 := by have h0 := hx 0; linarith
      simp only [Matrix.cons_val_one, Matrix.head_cons, kink, Agent052.AffMap.eval,
        Fin.sum_univ_one]
      linarith [max_eq_right hx0]

private lemma kink_not_mem_053 : kink ∉ Agent053.CPWL 1 := by
  rintro ⟨-, N, pieces, haff, hloc⟩
  obtain ⟨i, ε, hε, hi⟩ := hloc (fun _ => (0 : ℝ))
  have hdist : ∀ t : ℝ, |t| < ε →
      kink (fun _ : Fin 1 => t) = pieces i (fun _ : Fin 1 => t) := by
    intro t ht
    apply hi
    rw [dist_pi_lt_iff hε]
    intro b
    simpa [Real.dist_eq, sub_zero] using ht
  obtain ⟨w, b, hw⟩ := haff i
  have heval : ∀ t : ℝ, pieces i (fun _ : Fin 1 => t) = w 0 * t + b := by
    intro t
    simpa [Fin.sum_univ_one] using hw (fun _ : Fin 1 => t)
  have h1 : ∀ t : ℝ, 0 < t → t < ε → t = w 0 * t + b := by
    intro t ht0 htε
    have hxt := hdist t (by rw [abs_of_pos ht0]; exact htε)
    rw [heval] at hxt
    rwa [show kink (fun _ : Fin 1 => t) = t from max_eq_right ht0.le] at hxt
  have h2 : ∀ t : ℝ, 0 < t → t < ε → (0 : ℝ) = w 0 * (-t) + b := by
    intro t ht0 htε
    have hlt : |(-t)| < ε := by rw [abs_neg, abs_of_pos ht0]; exact htε
    have hxt := hdist (-t) hlt
    rw [heval] at hxt
    rwa [show kink (fun _ : Fin 1 => (-t)) = 0 from max_eq_left (by linarith)] at hxt
  have e1 : (ε / 2 : ℝ) = w 0 * (ε / 2) + b := h1 (ε / 2) (by linarith) (by linarith)
  have e2 : (0 : ℝ) = w 0 * (-(ε / 2)) + b := h2 (ε / 2) (by linarith) (by linarith)
  have e3 : (ε / 3 : ℝ) = w 0 * (ε / 3) + b := h1 (ε / 3) (by linarith) (by linarith)
  have e4 : (0 : ℝ) = w 0 * (-(ε / 3)) + b := h2 (ε / 3) (by linarith) (by linarith)
  have hb1 : (ε / 2 : ℝ) = 2 * b := by linear_combination e1 + e2
  have hb2 : (ε / 3 : ℝ) = 2 * b := by linear_combination e3 + e4
  linarith [hb1, hb2, hε]

theorem cpwl_ne : ∃ n, Agent052.CPWL n ≠ Agent053.CPWL n :=
  ⟨1, fun h => kink_not_mem_053 (h ▸ kink_mem_052)⟩

/-! ### `ReLUn` -/

-- Both `ReLUn n k` unfold to "∃ j ≤ k, computable with exactly j hidden layers", and the
-- two "exactly j hidden layers" predicates almost certainly describe the same class of
-- functions (both are `T^(j+1) ∘ ReLU ∘ ⋯ ∘ ReLU ∘ T^(1)`). But Agent052 encodes this via
-- a global width function `w : ℕ → ℕ` plus `cast`/`congrArg` transport at the two
-- boundary widths, while Agent053 encodes it via clean structural recursion on `j`.
-- Bridging these requires building an explicit induction translating between the
-- cast-laden encoding and the recursive one (peeling one layer at a time and repackaging
-- the width function), which is delicate dependent-type bookkeeping we cannot verify
-- without compiler feedback in this budget.
theorem relun (n k : ℕ) : Agent052.ReLUn n k = Agent053.ReLUn n k := by
  sorry

/-! ### `statement` -/

-- The right-hand side is false: Agent053's `CPWL 3 ≠ ReLUn 3 (depthBound 3)`, witnessed by
-- the same `kink`-style function on the first coordinate (representable with one hidden
-- layer, hence in `ReLUn 3 (depthBound 3)` since `depthBound 3 = 2 ≥ 1`, but not
-- local-agreement-CPWL at the origin by the same ball argument as `kink_not_mem_053`). The
-- left-hand side is exactly a restatement of the paper's actual Theorem 2 for Agent052's
-- own (faithful) encoding, which is genuinely new mathematics well beyond a bridge file.
theorem statement :
    (∀ n, 3 ≤ n → Agent052.CPWL n = Agent052.ReLUn n (Agent052.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent053.CPWL n = Agent053.ReLUn n (Agent053.depthBound n)) := by
  sorry

end Bridge_052_053

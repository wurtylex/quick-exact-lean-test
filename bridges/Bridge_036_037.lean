namespace Bridge_036_037

/-!
# Bridge between `Agent036` and `Agent037`

Both formalizations model `ℝ^a → ℝ^b` affine maps by a matrix/bias-vector pair
(`Agent036.Affine` / `Agent037.AffineMap`, literally the same two fields `A`, `c`,
evaluated by the same formula `x ↦ A.mulVec x + c`), and both define `NetOutput`/
`computesReLU` and `ReLUn` by literally the same recursive unwinding of
`T^(k+1) ∘ ReLU ∘ ⋯ ∘ ReLU ∘ T^(1)`, with `ReLUn n k` meaning "at most `k` hidden
layers" in both files. `depthBound` is the *same* term
`Nat.ceil (Real.logb 3 ((n:ℝ) - 1)) + 1` in both files, verbatim.

The one place the two files genuinely disagree is `CPWL`:

* `Agent036.CPWL` requires `f` continuous and asks, for every point `x`, that *some*
  member of a fixed finite family of affine functions agrees with `f` on a full
  neighbourhood of `x` (a "locally affine at every point" reading).
* `Agent037.CPWL` requires `f` continuous and asks for a finite polyhedral
  subdivision of `ℝ^n` on each piece of which `f` agrees (globally on that piece)
  with an affine function (the standard polyhedral-subdivision reading, and the more
  faithful rendering of "continuous piecewise linear").

These are genuinely different conditions: `Agent036`'s reading fails on the most basic
example of a CPWL function, `x ↦ max 0 (x 0)`, exactly at the kink `x 0 = 0`, because
*every* full neighbourhood of such a point contains points on both sides of the kink,
so no single affine function can match `f` throughout any neighbourhood of that point.
`Agent037`'s polyhedral reading has no trouble with this function at all. This is
witnessed concretely below (`witness_mem_037`, `witness_notMem_036`), giving `cpwl_ne`.
-/

/-! ### `depth`

The two `depthBound` definitions are the identical term
`Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1`, so this is definitional equality. -/

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent036.depthBound n = Agent037.depthBound n := rfl

/-! ### `relun`

`Agent036.NetOutput n k f` and `Agent037.computesReLU k n f` are literally the same
recursive unwinding (same `Affine`/`AffineMap` fields and `eval` formula, same `relu`,
`reluVec`), just with the `n`/`k` arguments in different order. We bridge them by
induction on the hidden-layer count, transporting the affine witness `T` from one
structure to the other by copying its `A`, `c` fields (the two `eval`/`reluVec`
formulas are then definitionally equal). -/

theorem netOutput_iff :
    ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
      Agent036.NetOutput n k f ↔ Agent037.computesReLU k n f
  | 0, n, f => by
      constructor
      · rintro ⟨T, hT⟩
        exact ⟨⟨T.A, T.c⟩, hT⟩
      · rintro ⟨T, hT⟩
        exact ⟨⟨T.A, T.c⟩, hT⟩
  | (k + 1), n, f => by
      constructor
      · rintro ⟨m, T, g, hg, hf⟩
        exact ⟨m, ⟨T.A, T.c⟩, g, (netOutput_iff k m g).mp hg, hf⟩
      · rintro ⟨m, T, g, hg, hf⟩
        exact ⟨m, ⟨T.A, T.c⟩, g, (netOutput_iff k m g).mpr hg, hf⟩

theorem relun (n k : ℕ) : Agent036.ReLUn n k = Agent037.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (netOutput_iff j n f).mp hf⟩
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (netOutput_iff j n f).mpr hf⟩

/-! ### `cpwl_ne`

The counterexample: `witness x := max 0 (x 0)` on `Fin 1 → ℝ`, the most basic
one-hidden-layer ReLU network. It lies in `Agent037.CPWL 1` (an explicit two-piece
polyhedral subdivision) but not in `Agent036.CPWL 1` (no single affine function can
match it on a full neighbourhood of `0`, since such a neighbourhood always contains
points with `x 0 > 0` and points with `x 0 < 0`). -/

/-- The constant-vector embedding `ℝ → (Fin 1 → ℝ)`; used to build a one-parameter
family of test points for the neighbourhood argument in `witness_notMem_036`. -/
def line (t : ℝ) : Fin 1 → ℝ := fun _ => t

@[simp] theorem line_apply (t : ℝ) (i : Fin 1) : line t i = t := rfl

/-- The counterexample function. -/
def witness : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

@[simp] theorem witness_apply (x : Fin 1 → ℝ) : witness x = max 0 (x 0) := rfl

theorem witness_mem_037 : witness ∈ Agent037.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2,
    fun i => if i = 0 then {x : Fin 1 → ℝ | 0 ≤ x 0} else {x : Fin 1 → ℝ | x 0 ≤ 0},
    fun i => if i = 0 then (fun x : Fin 1 → ℝ => x 0) else (fun _ : Fin 1 → ℝ => (0 : ℝ)),
    ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · show Agent037.IsPolyhedron 1 {x : Fin 1 → ℝ | 0 ≤ x 0}
      refine ⟨1, fun _ _ => (-1 : ℝ), fun _ => 0, ?_⟩
      ext x
      show (0 ≤ x 0) ↔ (∀ _ : Fin 1, (∑ k : Fin 1, (-1 : ℝ) * x k) ≤ 0)
      rw [Fin.sum_univ_one]
      constructor
      · intro hx _
        linarith
      · intro h
        have := h 0
        linarith
    · show Agent037.IsPolyhedron 1 {x : Fin 1 → ℝ | x 0 ≤ 0}
      refine ⟨1, fun _ _ => (1 : ℝ), fun _ => 0, ?_⟩
      ext x
      show (x 0 ≤ 0) ↔ (∀ _ : Fin 1, (∑ k : Fin 1, (1 : ℝ) * x k) ≤ 0)
      rw [Fin.sum_univ_one]
      constructor
      · intro hx _
        linarith
      · intro h
        have := h 0
        linarith
  · intro i
    fin_cases i
    · show Agent037.IsAffineFn 1 (fun x : Fin 1 → ℝ => x 0)
      refine ⟨fun _ => (1 : ℝ), 0, fun x => ?_⟩
      show x 0 = (∑ k : Fin 1, (1 : ℝ) * x k) + 0
      rw [Fin.sum_univ_one]
      ring
    · show Agent037.IsAffineFn 1 (fun _ : Fin 1 → ℝ => (0 : ℝ))
      refine ⟨fun _ => (0 : ℝ), 0, fun x => ?_⟩
      show (0 : ℝ) = (∑ k : Fin 1, (0 : ℝ) * x k) + 0
      rw [Fin.sum_univ_one]
      ring
  · intro x
    rcases le_total 0 (x 0) with h | h
    · refine ⟨0, ?_⟩
      show (0 : ℝ) ≤ x 0
      exact h
    · refine ⟨1, ?_⟩
      show x 0 ≤ (0 : ℝ)
      exact h
  · intro i
    fin_cases i
    · intro x hx
      show max 0 (x 0) = x 0
      exact max_eq_right_iff.mpr hx
    · intro x hx
      show max 0 (x 0) = (0 : ℝ)
      exact max_eq_left_iff.mpr hx

theorem witness_notMem_036 : witness ∉ Agent036.CPWL 1 := by
  rintro ⟨-, m, g, hgaffine, hlocal⟩
  obtain ⟨i, U, hU, hagree⟩ := hlocal (line 0)
  obtain ⟨T, hT⟩ := hgaffine i
  -- Every value of `g i` has the closed form `T.A 0 0 * x 0 + T.c 0`.
  have hcalc : ∀ x : Fin 1 → ℝ, T.eval x 0 = T.A 0 0 * x 0 + T.c 0 := by
    intro x
    have hmv : T.A.mulVec x 0 = T.A 0 0 * x 0 := by
      rw [show T.A.mulVec x 0 = ∑ j : Fin 1, T.A 0 j * x j from rfl, Fin.sum_univ_one]
    show T.A.mulVec x 0 + T.c 0 = T.A 0 0 * x 0 + T.c 0
    rw [hmv]
  have key : ∀ x : Fin 1 → ℝ, g i x = T.A 0 0 * x 0 + T.c 0 :=
    fun x => (hT x).trans (hcalc x)
  -- `U` is a neighbourhood of `line 0`, so pulling back along the continuous path
  -- `line : ℝ → Fin 1 → ℝ` gives a neighbourhood of `0` in `ℝ`, hence an interval
  -- `(-ε, ε)` that lands entirely inside `U`.
  have hcont : Continuous line := continuous_pi (fun _ => continuous_id)
  have hpre : line ⁻¹' U ∈ nhds (0 : ℝ) := hcont.continuousAt.preimage_mem_nhds hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  have ht : (0 : ℝ) < ε / 2 := half_pos hε
  have htlt : ε / 2 < ε := by linarith
  have htmem : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.le]
    exact htlt
  have htmem' : (-(ε / 2)) ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_neg, abs_of_nonneg ht.le]
    exact htlt
  have hUt : line (ε / 2) ∈ U := hball htmem
  have hUnt : line (-(ε / 2)) ∈ U := hball htmem'
  have hU0 : line 0 ∈ U := mem_of_mem_nhds hU
  have eq0 : witness (line 0) = g i (line 0) := hagree (line 0) hU0
  have eqt : witness (line (ε / 2)) = g i (line (ε / 2)) := hagree (line (ε / 2)) hUt
  have eqnt : witness (line (-(ε / 2))) = g i (line (-(ε / 2))) :=
    hagree (line (-(ε / 2))) hUnt
  rw [key (line 0)] at eq0
  rw [key (line (ε / 2))] at eqt
  rw [key (line (-(ε / 2)))] at eqnt
  rw [witness_apply, line_apply] at eq0 eqt eqnt
  -- `eq0 : max 0 0 = T.A 0 0 * 0 + T.c 0`
  rw [max_eq_left_iff.mpr (le_refl (0 : ℝ)), mul_zero, zero_add] at eq0
  -- `eqt : max 0 (ε / 2) = T.A 0 0 * (ε / 2) + T.c 0`
  rw [max_eq_right_iff.mpr ht.le] at eqt
  -- `eqnt : max 0 (-(ε / 2)) = T.A 0 0 * (-(ε / 2)) + T.c 0`
  rw [max_eq_left_iff.mpr (show (-(ε / 2) : ℝ) ≤ 0 by linarith)] at eqnt
  rw [← eq0, add_zero] at eqt eqnt
  -- `eqt : ε / 2 = T.A 0 0 * (ε / 2)`,  `eqnt : 0 = T.A 0 0 * (-(ε / 2))`
  rw [mul_neg] at eqnt
  -- `eqnt : 0 = -(T.A 0 0 * (ε / 2))`, contradicts `eqt` together with `ht`.
  linarith

theorem cpwl_ne : ∃ n, Agent036.CPWL n ≠ Agent037.CPWL n := by
  refine ⟨1, fun hEq => witness_notMem_036 ?_⟩
  rw [hEq]
  exact witness_mem_037

/-! ### `statement`

Bridging `relun` and `depth` shows the right-hand sides of the two internal
equalities agree for every `n` (both denote the same set `ReLUn n (depthBound n)`),
so the biconditional reduces to comparing `Agent036.CPWL n` and `Agent037.CPWL n`
against that common target, for `n ≥ 3`.

The same construction as `witness_notMem_036`/`witness_mem_037` goes through
verbatim at every `n ≥ 1` (in particular at any `n ≥ 3`: use coordinate `0` and leave
the rest of the domain unconstrained), and `witness` is a genuine one-hidden-layer
ReLU network, so it lies in `ReLUn n (depthBound n)` for every such `n`. Hence
`Agent036`'s internal statement (the left side of the `↔`) is actually *false*, which
makes `statement` equivalent to *refuting* `Agent037`'s internal statement — i.e. to
refuting an instance of the paper's actual, unproved Theorem 2 for the
polyhedral-subdivision reading of `CPWL` (the more faithful of the two
formalizations here). That refutation (or a proof that no such counterexample
exists, i.e. that Theorem 2 genuinely holds for `Agent037`'s formalization) is the
paper's real mathematical content and is well beyond the scope of this bridge; no one
has established it here, so this is left as an honest `sorry`. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent036.CPWL n = Agent036.ReLUn n (Agent036.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent037.CPWL n = Agent037.ReLUn n (Agent037.depthBound n)) := by
  sorry

end Bridge_036_037

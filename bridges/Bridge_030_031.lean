namespace Bridge_030_031

/-!
## Comparing `Agent030` and `Agent031`

Both agents use *exactly* the same modelling for `ReLUn`/`depthBound`:

* An affine map `ℝ^a → ℝ^b` is a matrix `A` plus a bias vector: `Agent030` carries these as
  two curried arguments `(A, c)` to a bare function `affineMap`, while `Agent031` bundles them
  into a one-field-each structure `AffineMap'`. The underlying arithmetic
  (`A.mulVec x + c` vs. `fun i => (∑ j, A i j * x j) + bias i`) is the same computation.
* `ComputesWithHiddenLayers`/`IsReLUComputable` are the same recursion on `k`, and `ReLUn` is
  "at most `k` hidden layers" for both.
* `depthBound` is *syntactically* the same expression (`Nat.ceil (Real.logb 3 (n - 1)) + 1`
  vs. `⌈Real.logb 3 (n - 1)⌉₊ + 1`, and `⌈·⌉₊` is notation for `Nat.ceil`).

So `relun` and `depth` below are provable via a routine bridging induction.

`CPWL`, however, is where the two disagree in substance:

* `Agent030.CPWL` is the genuine *polyhedral subdivision* reading (family (a) in the spec):
  finitely many polyhedral pieces covering `ℝⁿ`, `f` affine on each *closed* piece. Two pieces
  are allowed to share a boundary where the two affine functions agree only pointwise there.
* `Agent031.CPWL` is the *local agreement* reading (family (b)): `∀ x, ∃ i, ∃ ε > 0, ∀ y,
  dist y x < ε → f y = (T i).eval y 0`. This demands a *single* affine function that matches
  `f` on a full open ball around `x`.

These are genuinely different: the local-agreement reading fails at any kink point. The
one-dimensional ReLU-like function `x ↦ max 0 (x 0)` is a textbook member of `CPWL 1` (two
polyhedral pieces `{x 0 ≤ 0}` and `{x 0 ≥ 0}`), but at `x = 0` no single affine function agrees
with it on any two-sided neighbourhood (its two "sides" have different slopes). So
`Agent030.CPWL 1 ≠ Agent031.CPWL 1`, which is exactly the situation flagged in the spec:
"look hard at (b) ... think about whether `x ↦ max 0 (x 0)` satisfies it near 0."
-/

/-- The one-dimensional kink function `x ↦ max 0 (x 0)`, i.e. `relu` in one variable, used as
the witness that `Agent030.CPWL` and `Agent031.CPWL` disagree. -/
def kink : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

private lemma kink_continuous : Continuous kink :=
  continuous_const.max (continuous_apply 0)

/-- `affineMap A c x` (curried matrix + bias, `Agent030`'s style) computes the same vector as
`(⟨A, c⟩ : AffineMap' a b).eval x` (bundled structure, `Agent031`'s style): both unfold to
`fun i => (∑ j, A i j * x j) + c i`. -/
private lemma affineMap_eq {a b : ℕ} (A : Matrix (Fin b) (Fin a) ℝ) (c : Fin b → ℝ)
    (x : Fin a → ℝ) :
    Agent030.affineMap A c x = Agent031.AffineMap'.eval ⟨A, c⟩ x := by
  funext i
  simp [Agent030.affineMap, Agent031.AffineMap'.eval, Matrix.mulVec, Matrix.dotProduct]

/-- `Agent030.reluVec` and `Agent031.reluVec` are literally the same function
(`fun i => max 0 (v i)`), just defined in two different namespaces. -/
private lemma reluVec_eq {m : ℕ} (v : Fin m → ℝ) :
    Agent030.reluVec v = Agent031.reluVec v := by
  funext i
  simp [Agent030.reluVec, Agent031.reluVec, Agent030.relu, Agent031.relu]

/-- The two "computes with exactly `k` hidden layers" predicates coincide: same recursion on
`k`, same underlying affine-map arithmetic, just packaged differently
(curried matrix+bias vs. the bundled `AffineMap'` structure). -/
private lemma computes_iff :
    ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
      Agent030.ComputesWithHiddenLayers n k f ↔ Agent031.IsReLUComputable n k f := by
  intro k
  induction k with
  | zero =>
      intro n f
      constructor
      · rintro ⟨A, c, hf⟩
        refine ⟨⟨A, c⟩, fun x => ?_⟩
        rw [hf]
        exact congrFun (affineMap_eq A c x) 0
      · rintro ⟨T, hf⟩
        refine ⟨T.A, T.bias, fun x => ?_⟩
        rw [hf]
        exact (congrFun (affineMap_eq T.A T.bias x) 0).symm
  | succ k ih =>
      intro n f
      constructor
      · rintro ⟨m, A, c, g, hg, hf⟩
        refine ⟨m, ⟨A, c⟩, g, (ih m g).mp hg, fun x => ?_⟩
        rw [hf, affineMap_eq A c x, reluVec_eq]
      · rintro ⟨m, T, g, hg, hf⟩
        refine ⟨m, T.A, T.bias, g, (ih m g).mpr hg, fun x => ?_⟩
        rw [hf]
        congr 1
        rw [affineMap_eq T.A T.bias x]
        exact (reluVec_eq _).symm

/-- `kink` lies in `Agent030.CPWL 1`: witnessed by the two-piece polyhedral subdivision
`{x 0 ≤ 0}` (where `kink = 0`) and `{x 0 ≥ 0}` (where `kink = fun x => x 0`). -/
private lemma kink_mem_cpwl030 : kink ∈ Agent030.CPWL 1 := by
  refine ⟨kink_continuous, 2,
      ![{x : Fin 1 → ℝ | x 0 ≤ 0}, {x : Fin 1 → ℝ | 0 ≤ x 0}],
      ![fun _ : Fin 1 → ℝ => (0 : ℝ), fun x : Fin 1 → ℝ => x 0],
      ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · simp only [Matrix.cons_val_zero]
      refine ⟨1, fun _ => {x : Fin 1 → ℝ | x 0 ≤ 0}, fun _ => ⟨fun _ => 1, 0, ?_⟩, ?_⟩
      · ext x
        simp [Fin.sum_univ_one]
      · exact (Set.iInter_const {x : Fin 1 → ℝ | x 0 ≤ 0}).symm
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      refine ⟨1, fun _ => {x : Fin 1 → ℝ | 0 ≤ x 0}, fun _ => ⟨fun _ => -1, 0, ?_⟩, ?_⟩
      · ext x
        simp only [Set.mem_setOf_eq, Fin.sum_univ_one]
        constructor <;> intro h <;> linarith
      · exact (Set.iInter_const {x : Fin 1 → ℝ | 0 ≤ x 0}).symm
  · intro i
    fin_cases i
    · simp only [Matrix.cons_val_zero]
      exact ⟨0, 0, by intro x; simp⟩
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      exact ⟨fun _ => 1, 0, by intro x; simp [Fin.sum_univ_one]⟩
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    rcases le_total (x 0) 0 with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  · intro i
    fin_cases i
    · intro x hx
      simp only [Matrix.cons_val_zero, Set.mem_setOf_eq] at hx
      simp only [Matrix.cons_val_zero]
      exact max_eq_left hx
    · intro x hx
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Set.mem_setOf_eq] at hx
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      exact max_eq_right hx

/-- `kink` does *not* lie in `Agent031.CPWL 1`: at `x = 0` no single affine function can agree
with `kink` on a whole open ball, since `kink` has slope `0` on one side and slope `1` on the
other. We witness this with the three sample points `0`, `ε/2`, `-ε/2`. -/
private lemma kink_not_mem_cpwl031 : kink ∉ Agent031.CPWL 1 := by
  rintro ⟨-, m, T, hT⟩
  obtain ⟨i, ε, hε, hy⟩ := hT (fun _ => (0 : ℝ))
  have e0 := hy (fun _ => (0 : ℝ)) (by rw [dist_self]; exact hε)
  have hd_pos : dist (fun _ : Fin 1 => ε / 2) (fun _ : Fin 1 => (0 : ℝ)) < ε := by
    apply (dist_pi_lt_iff hε).mpr
    intro b
    rw [Real.dist_eq]
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have hd_neg : dist (fun _ : Fin 1 => -(ε / 2)) (fun _ : Fin 1 => (0 : ℝ)) < ε := by
    apply (dist_pi_lt_iff hε).mpr
    intro b
    rw [Real.dist_eq]
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have ep := hy (fun _ => ε / 2) hd_pos
  have en := hy (fun _ => -(ε / 2)) hd_neg
  have hk0 : kink (fun _ : Fin 1 => (0 : ℝ)) = 0 := by simp [kink]
  have hkp : kink (fun _ : Fin 1 => ε / 2) = ε / 2 :=
    max_eq_right (by linarith)
  have hkn : kink (fun _ : Fin 1 => -(ε / 2)) = 0 :=
    max_eq_left (by linarith)
  have hev0 : (T i).eval (fun _ : Fin 1 => (0 : ℝ)) 0 = (T i).bias 0 := by
    simp [Agent031.AffineMap'.eval, Fin.sum_univ_one]
  have hevp : (T i).eval (fun _ : Fin 1 => ε / 2) 0
      = (T i).A 0 0 * (ε / 2) + (T i).bias 0 := by
    simp [Agent031.AffineMap'.eval, Fin.sum_univ_one]
  have hevn : (T i).eval (fun _ : Fin 1 => -(ε / 2)) 0
      = (T i).A 0 0 * (-(ε / 2)) + (T i).bias 0 := by
    simp [Agent031.AffineMap'.eval, Fin.sum_univ_one]
  rw [hk0, hev0] at e0
  rw [hkp, hevp] at ep
  rw [hkn, hevn] at en
  rw [mul_neg] at en
  linarith

theorem relun (n k : ℕ) : Agent030.ReLUn n k = Agent031.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨k', hk', hf⟩
    exact ⟨k', hk', (computes_iff k' n f).mp hf⟩
  · rintro ⟨k', hk', hf⟩
    exact ⟨k', hk', (computes_iff k' n f).mpr hf⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent030.depthBound n = Agent031.depthBound n := by
  rfl

/-- `Agent030.CPWL` (polyhedral subdivision) and `Agent031.CPWL` (local agreement with a
single affine function on a full neighbourhood) genuinely differ: the kink function
`x ↦ max 0 (x 0)` lies in the former but not in the latter, already at `n = 1`. -/
theorem cpwl_ne : ∃ n, Agent030.CPWL n ≠ Agent031.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  have hmem : kink ∈ Agent031.CPWL 1 := h ▸ kink_mem_cpwl030
  exact kink_not_mem_cpwl031 hmem

/-- Left as `sorry`: `ReLUn`/`depthBound` coincide between the two agents (see `relun`,
`depth`), so `statement` reduces to comparing
`(∀ n ≥ 3, Agent030.CPWL n = S n) ↔ (∀ n ≥ 3, Agent031.CPWL n = S n)` for the *common* set
`S n := Agent030.ReLUn n (Agent030.depthBound n) = Agent031.ReLUn n (Agent031.depthBound n)`.
The right-hand side is provably `False` by the same `kink`-style counterexample used for
`cpwl_ne` (extended to any coordinate `n ≥ 3` and using that `depthBound n ≥ 1` there, so
`kink` padded to `n` variables lies in `ReLUn n (depthBound n)` but not in `Agent031.CPWL n`).
But the left-hand side is exactly (an instance of) the paper's Theorem 2 for `Agent030`'s
encoding, which `Agent030` itself leaves as `sorry` — a genuine, unproved, hard theorem. We
have no way to decide it here, so we cannot decide whether the biconditional is `True`
(if `Agent030`'s side is also `False`) or `False` (if it is `True`, which is the mathematically
expected outcome since `Agent030.CPWL` is the faithful polyhedral-subdivision reading). -/
theorem statement :
    (∀ n, 3 ≤ n → Agent030.CPWL n = Agent030.ReLUn n (Agent030.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent031.CPWL n = Agent031.ReLUn n (Agent031.depthBound n)) := by
  sorry

end Bridge_030_031

/-!
# Star comparison: `Agent058` vs `Ref`

`Agent058` matches the reference on the depth bound (syntactically identical
definitions) and takes the same "at most `k` hidden layers" reading of
`ReLU_{n,k}`, but its `CPWL` is the **local-agreement (neighbourhood)** variant:

```
∀ x, ∃ i, ∀ᶠ y in nhds x, f y = (g i).eval y 0
```

On a connected space this forces `f` to be *globally* affine, so it is strictly
stronger than the reference's polyhedral-cover definition and `cpwl` is **false**.
We refute it with `f = fun x => max 0 (x 0)` at `n = 1`.
-/

namespace Star_058

/-! ### The separating witness `x ↦ max 0 (x 0)` on `ℝ¹` -/

/-- The witness function: `ReLU` in one variable.  It is CPWL in the reference
sense but not locally-affine-from-a-finite-family in `Agent058`'s sense. -/
private noncomputable def testFn : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

/-- Normal vectors of the two halfspaces `{x 0 ≤ 0}` and `{-x 0 ≤ 0}`. -/
private def coefs : Fin 2 → (Fin 1 → ℝ) := ![fun _ => 1, fun _ => -1]

/-- The two halfspace pieces covering `ℝ¹`. -/
private def pieces (i : Fin 2) : Set (Fin 1 → ℝ) := {x | (∑ j, coefs i j * x j) ≤ 0}

/-- Coefficient vectors of the two affine pieces `0` and `x ↦ x 0`. -/
private def aCoefs : Fin 2 → (Fin 1 → ℝ) := ![fun _ => 0, fun _ => 1]

/-- The two affine functionals `testFn` agrees with. -/
private def affs (i : Fin 2) : (Fin 1 → ℝ) → ℝ := fun x => (∑ j, aCoefs i j * x j) + 0

private lemma pieces_isPolyhedron (i : Fin 2) : Ref.IsPolyhedron 1 (pieces i) :=
  ⟨1, fun _ => pieces i, fun _ => ⟨coefs i, 0, rfl⟩, by ext x; simp⟩

private lemma affs_isAffine (i : Fin 2) : Ref.IsAffine (affs i) :=
  ⟨aCoefs i, 0, fun _ => rfl⟩

private lemma pieces_cover : (⋃ i, pieces i) = Set.univ := by
  ext x
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  rcases le_total (x 0) 0 with h | h
  · exact Set.mem_iUnion.2 ⟨0, by simpa [pieces, coefs, Fin.sum_univ_one] using h⟩
  · exact Set.mem_iUnion.2 ⟨1, by simpa [pieces, coefs, Fin.sum_univ_one] using h⟩

private lemma agree0 : ∀ x ∈ pieces 0, testFn x = affs 0 x := by
  intro x hx
  have h : x 0 ≤ 0 := by simpa [pieces, coefs, Fin.sum_univ_one] using hx
  show max 0 (x 0) = (∑ j, aCoefs 0 j * x j) + 0
  simp [aCoefs, Fin.sum_univ_one, max_eq_left h]

private lemma agree1 : ∀ x ∈ pieces 1, testFn x = affs 1 x := by
  intro x hx
  have h : 0 ≤ x 0 := by simpa [pieces, coefs, Fin.sum_univ_one] using hx
  show max 0 (x 0) = (∑ j, aCoefs 1 j * x j) + 0
  simp [aCoefs, Fin.sum_univ_one, max_eq_right h]

/-- `testFn` is continuous piecewise-linear in the reference (polyhedral cover) sense. -/
private lemma testFn_mem_ref : testFn ∈ Ref.CPWL 1 := by
  simp only [Ref.CPWL, Set.mem_setOf_eq, Ref.IsCPWL]
  refine ⟨continuous_const.max (continuous_apply 0), 2, pieces, affs,
    pieces_isPolyhedron, affs_isAffine, pieces_cover, ?_⟩
  intro i
  fin_cases i
  · exact agree0
  · exact agree1

/-- `testFn` is **not** in `Agent058.CPWL 1`: local agreement with a finite family
of affine maps fails at the kink `x = 0`. -/
private lemma testFn_not_mem_agent : testFn ∉ Agent058.CPWL 1 := by
  intro hmem
  simp only [Agent058.CPWL, Set.mem_setOf_eq] at hmem
  obtain ⟨-, m, g, hg⟩ := hmem
  obtain ⟨i, hev⟩ := hg 0
  -- Pull the neighbourhood statement back along `t ↦ (fun _ => t)`.
  have hcont : Continuous (fun t : ℝ => (fun _ => t : Fin 1 → ℝ)) :=
    continuous_pi fun _ => continuous_id
  have htend : Filter.Tendsto (fun t : ℝ => (fun _ => t : Fin 1 → ℝ))
      (nhds 0) (nhds (0 : Fin 1 → ℝ)) :=
    hcont.tendsto' 0 0 (funext fun _ => rfl)
  have hev2 := htend.eventually hev
  rw [Metric.eventually_nhds_iff] at hev2
  obtain ⟨ε, hε, hball⟩ := hev2
  -- On the diagonal line the affine map `g i` is `t ↦ t * A + B`.
  have hval : ∀ t : ℝ, (g i).eval (fun _ => t) 0
      = t * ((g i).A.mulVec (fun _ => (1 : ℝ)) 0) + (g i).c 0 := by
    intro t
    have h1 : (fun _ => t : Fin 1 → ℝ) = t • (fun _ => (1 : ℝ)) := by funext j; simp
    show ((g i).A.mulVec (fun _ => t) + (g i).c) 0 = _
    rw [h1, Matrix.mulVec_smul]
    simp
  have hf : ∀ t : ℝ, testFn (fun _ => t) = max 0 t := fun _ => rfl
  have hd : ∀ y : ℝ, |y| < ε → dist y (0 : ℝ) < ε := by
    intro y hy; rwa [Real.dist_eq, sub_zero]
  have e0 := hball (hd 0 (by rwa [abs_zero]))
  have ep := hball (hd (ε / 2) (by rw [abs_of_pos (by linarith)]; linarith))
  have en := hball (hd (-(ε / 2)) (by rw [abs_of_neg (by linarith)]; linarith))
  simp only [hf, hval] at e0 ep en
  rw [max_self] at e0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ ε / 2)] at ep
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0 : ℝ))] at en
  -- `t = 0` forces `B = 0`; adding the `±ε/2` instances forces `ε/2 = 2B = 0`.
  have hB : (g i).c 0 = 0 := by linear_combination -e0
  have hkey : ε / 2 = 2 * ((g i).c 0) := by linear_combination ep + en
  linarith [hkey, hB, hε]

/-! ### The four obligations -/

/-- **Refutation of `cpwl`.**  `Agent058.CPWL` is the neighbourhood-agreement
variant, which is strictly stronger than the reference's polyhedral-cover
definition; `x ↦ max 0 (x 0)` separates them at `n = 1`. -/
theorem cpwl_ne : ∃ n, Agent058.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => testFn_not_mem_agent ?_⟩
  rw [h]
  exact testFn_mem_ref

/-- Both files take "at most `k` hidden layers", but `Agent058` encodes a network
as a width function `ℕ → ℕ` plus a dependent family of layers evaluated by
`netApply`, whereas `Ref` uses a structural recursion `ComputedBy`.  Identifying
the two sets needs a genuine induction translating `netApply`-compositions into
`ComputedBy` witnesses and back (including the `Fin.cast` bookkeeping on the
output coordinate); left as an honest `sorry`. -/
theorem relun (n k : ℕ) : Agent058.ReLUn n k = Ref.ReLUn n k := sorry

/-- The two depth bounds are literally the same expression
`⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent058.depthBound n = Ref.depthBound n := rfl

/-- The left-hand side is false (by `cpwl_ne`'s argument, `Agent058.CPWL n` contains
only globally affine functions, while its `ReLUn` does not), so the iff holds iff the
right-hand side is false too — i.e. deciding it requires *proving or disproving*
`Ref.theorem2`, which is itself `sorry`-ed.  Honest `sorry`. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent058.CPWL n = Agent058.ReLUn n (Agent058.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_058

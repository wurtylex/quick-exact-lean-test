namespace Star_100

/-!
# Star comparison: `Agent100` vs `Ref`

`Agent100.depthBound` is syntactically identical to `Ref.depthBound`.

`Agent100.CPWL` is the *neighbourhood-agreement* reading: `f` is continuous and there is a
finite family of affine `g i` with `∀ x, ∃ i, f =ᶠ[𝓝 x] g i`.  That is strictly stronger
than the reference's polyhedral-cover definition — it has no room for a breakpoint — so
`cpwl` is **false** and is refuted below with `f = fun x => max 0 (x 0)` at `n = 1`.

`Agent100.ReLUn` is "exactly `k` hidden layers" against the reference's "at most `k`"; the
two denote the same set, but only via the padding identity `x = relu x - relu (-x)`, which
is a genuine theorem.  Left as an honest `sorry`.
-/

/-- The refuting witness `ℝ¹ → ℝ`, `x ↦ max 0 (x 0)`: continuous piecewise linear, but not
affine on any neighbourhood of the origin. -/
private noncomputable def w : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

/-- The diagonal embedding `ℝ → ℝ¹`, used to pull a neighbourhood of `0` back to `ℝ`. -/
private def ev (t : ℝ) : Fin 1 → ℝ := fun _ => t

private lemma w_cont : Continuous w := continuous_const.max (continuous_apply 0)

/-- Every halfspace is a polyhedron (a one-fold intersection). -/
private lemma halfspace_isPolyhedron {n : ℕ} {S : Set (Fin n → ℝ)}
    (h : Ref.IsHalfspace n S) : Ref.IsPolyhedron n S :=
  ⟨1, fun _ => S, fun _ => h, by rw [Set.iInter_const]⟩

/-- The witness lies in the reference class: `{x | x 0 ≤ 0}` and `{x | 0 ≤ x 0}` are
halfspaces covering `ℝ¹`, and `w` is affine on each. -/
private lemma w_mem_ref : w ∈ Ref.CPWL 1 := by
  refine ⟨w_cont, 2, ![{x : Fin 1 → ℝ | x 0 ≤ 0}, {x : Fin 1 → ℝ | 0 ≤ x 0}],
    ![fun _ => (0 : ℝ), fun x => x 0], ?_, ?_, ?_, ?_⟩
  · intro i
    refine halfspace_isPolyhedron ?_
    fin_cases i
    · exact ⟨fun _ => 1, 0, by ext x; simp⟩
    · exact ⟨fun _ => -1, 0, by ext x; simp⟩
  · intro i
    fin_cases i
    · exact ⟨fun _ => 0, 0, by intro x; simp⟩
    · exact ⟨fun _ => 1, 0, by intro x; simp⟩
  · refine Set.eq_univ_of_forall fun x => ?_
    rcases le_total (x 0) 0 with h | h
    · exact Set.mem_iUnion.2 ⟨0, by simpa using h⟩
    · exact Set.mem_iUnion.2 ⟨1, by simpa using h⟩
  · intro i x hx
    fin_cases i
    · have hx' : x 0 ≤ 0 := by simpa using hx
      simpa [w] using max_eq_left hx'
    · have hx' : (0 : ℝ) ≤ x 0 := by simpa using hx
      simpa [w] using max_eq_right hx'

/-- The witness does **not** lie in `Agent100.CPWL 1`: local agreement with an affine map at
the origin forces the midpoint identity, which `max 0 ·` violates across `0`. -/
private lemma w_not_mem_agent : w ∉ Agent100.CPWL 1 := by
  intro hmem
  obtain ⟨-, m, g, hg, hall⟩ := hmem
  obtain ⟨i, hev⟩ := hall 0
  obtain ⟨T, hT⟩ := hg i
  -- Affine maps satisfy `g (x + y) + g 0 = g x + g y`.
  have hadd : ∀ x y : Fin 1 → ℝ, g i (x + y) + g i 0 = g i x + g i y := by
    intro x y
    simp only [hT, Agent100.AffineTransform.toFun, Matrix.mulVec_add, Matrix.mulVec_zero,
      Pi.add_apply, Pi.zero_apply]
    ring
  have hz : ev 0 = (0 : Fin 1 → ℝ) := by funext j; rfl
  have hcont : Continuous ev := continuous_pi fun _ => continuous_id
  have hten : Filter.Tendsto ev (nhds 0) (nhds (0 : Fin 1 → ℝ)) := hcont.tendsto' 0 0 hz
  have hev' : ∀ᶠ t in nhds (0 : ℝ), w (ev t) = g i (ev t) := hten.eventually hev
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev'
  have h0 : w (ev 0) = g i (ev 0) :=
    hball (show dist (0 : ℝ) 0 < ε by simpa using hε)
  have h1 : w (ev (ε / 2)) = g i (ev (ε / 2)) :=
    hball (show dist (ε / 2) (0 : ℝ) < ε by
      rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith : (0 : ℝ) < ε / 2)]; linarith)
  have h2 : w (ev (-(ε / 2))) = g i (ev (-(ε / 2))) :=
    hball (show dist (-(ε / 2)) (0 : ℝ) < ε by
      rw [Real.dist_eq, sub_zero, abs_of_neg (by linarith : -(ε / 2) < (0 : ℝ))]; linarith)
  have hsum : ev (ε / 2) + ev (-(ε / 2)) = (0 : Fin 1 → ℝ) := by funext j; simp [ev]
  have hkey := hadd (ev (ε / 2)) (ev (-(ε / 2)))
  rw [hsum, ← hz, ← h0, ← h1, ← h2] at hkey
  simp only [w, ev, max_self] at hkey
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ ε / 2),
    max_eq_left (by linarith : -(ε / 2) ≤ (0 : ℝ))] at hkey
  linarith

/-- **Refutation of `cpwl`.**  `Agent100.CPWL` demands agreement with a single affine map on
a whole neighbourhood of every point, which on connected `ℝⁿ` rules out breakpoints; the
reference only demands agreement on each piece of a polyhedral cover. -/
theorem cpwl_ne : ∃ n, Agent100.CPWL n ≠ Ref.CPWL n :=
  ⟨1, fun h => w_not_mem_agent (by rw [h]; exact w_mem_ref)⟩

/-- `Agent100.ReLUn n k` is "exactly `k` hidden layers", `Ref.ReLUn n k` is "at most `k`".
The sets coincide, but only through the padding identity `x = relu x - relu (-x)`, which is
a real theorem about ReLU networks and not available definitionally. -/
theorem relun (n k : ℕ) : Agent100.ReLUn n k = Ref.ReLUn n k := sorry

/-- Both files write `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`, so this is definitional. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent100.depthBound n = Ref.depthBound n := rfl

/-- The two readings of Theorem 2 are *not* equivalent: by `cpwl_ne` the agent's `CPWL n`
contains only functions that are affine near every point, whereas its `ReLUn n (depthBound n)`
(with `depthBound n ≥ 2`) contains genuine breakpoint functions, so the left side is false;
the right side is the reference Theorem 2, which is true.  Refuting the iff therefore requires
*proving* the reference Theorem 2, which is exactly the `sorry`-ed `Ref.theorem2`.  Honest
`sorry`: neither direction is available without that theorem. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent100.CPWL n = Agent100.ReLUn n (Agent100.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_100

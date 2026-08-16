namespace Bridge_097_098

/- `depthBound`: both agents write the identical expression
`⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1` (`⌈·⌉₊` is notation for `Nat.ceil`), so the two
definitions are literally the same term up to notation. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent097.depthBound n = Agent098.depthBound n := rfl

/-- Ordinary scalar ReLU applied to the unique coordinate of `Fin 1 → ℝ`. -/
def reluFn : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

private theorem reluFn_cont : Continuous reluFn :=
  continuous_const.max (continuous_apply 0)

/-- `reluFn` is a genuine two-piece polyhedral CPWL function, in Agent098's sense. -/
private theorem reluFn_mem_098 : reluFn ∈ Agent098.CPWL 1 := by
  refine ⟨reluFn_cont, 2, ![{x : Fin 1 → ℝ | x 0 ≤ 0}, {x : Fin 1 → ℝ | 0 ≤ x 0}],
    ![Agent098.AffineFn.mk (fun _ => (0:ℝ)) 0, Agent098.AffineFn.mk (fun _ => (1:ℝ)) 0],
    ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact ⟨1, fun _ _ => 1, fun _ => 0, by
        simp only [Matrix.cons_val_zero]
        ext x; simp [Fin.sum_univ_one, forall_const]⟩
    · exact ⟨1, fun _ _ => -1, fun _ => 0, by
        simp only [Matrix.cons_val_one, Matrix.head_cons]
        ext x; simp only [Fin.sum_univ_one, neg_mul, one_mul, forall_const, Set.mem_setOf_eq]
        constructor <;> intro h <;> linarith⟩
  · refine (Set.eq_univ_of_forall (fun x => Set.mem_iUnion.mpr ?_)).symm
    rcases le_total (x 0) 0 with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  · intro i
    fin_cases i
    · intro x hx
      simp only [Matrix.cons_val_zero] at hx ⊢
      simp [reluFn, Agent098.AffineFn.eval, Fin.sum_univ_one, max_eq_left hx]
    · intro x hx
      simp only [Matrix.cons_val_one, Matrix.head_cons] at hx ⊢
      simp [reluFn, Agent098.AffineFn.eval, Fin.sum_univ_one, max_eq_right hx]

/-- `reluFn` fails Agent097's local-agreement condition at `0`: no single affine
function agrees with it on a whole two-sided neighbourhood of `0`, since its slope
differs (`0` vs `1`) on the two sides of the kink. -/
private theorem reluFn_not_mem_097 : reluFn ∉ Agent097.CPWL 1 := by
  rintro ⟨-, m, A, b, hx⟩
  obtain ⟨i, hev⟩ := hx (0 : Fin 1 → ℝ)
  let φ : ℝ → Fin 1 → ℝ := fun t _ => t
  have hcont : Continuous φ := continuous_pi fun _ => continuous_id
  have hφ0 : φ 0 = (0 : Fin 1 → ℝ) := by ext j; simp [φ]
  have htend : Filter.Tendsto φ (nhds (0:ℝ)) (nhds (0 : Fin 1 → ℝ)) := hφ0 ▸ hcont.tendsto 0
  have hev' : ∀ᶠ t in nhds (0:ℝ), max 0 t = A i 0 * t + b i := by
    filter_upwards [htend.eventually hev] with t ht
    simpa [reluFn, φ, Fin.sum_univ_one] using ht
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev'
  have h0 : (0:ℝ) = b i := by
    have := hball (show dist (0:ℝ) 0 < ε by rw [dist_self]; exact hε)
    simpa using this
  have h1 : ε / 2 = A i 0 * (ε / 2) + b i := by
    have hd : dist (ε / 2) 0 < ε := by
      rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith
    have h := hball hd
    rwa [max_eq_right (by linarith : (0:ℝ) ≤ ε / 2)] at h
  have h2 : (0:ℝ) = A i 0 * (-(ε / 2)) + b i := by
    have hd : dist (-(ε / 2)) 0 < ε := by
      rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by linarith)]; linarith
    have h := hball hd
    rwa [max_eq_left (by linarith : -(ε / 2) ≤ (0:ℝ))] at h
  rw [mul_neg] at h2
  linarith [h0, h1, h2]

-- `IsCPWL` (Agent097) only demands *local agreement*: at every point some affine
-- function coincides with `f` on a whole neighbourhood. Agent098's `CPWL` demands a
-- finite *polyhedral cover* on which `f` matches given affine pieces. These are
-- genuinely different classes: ordinary ReLU belongs to the polyhedral class but has
-- no single affine agreement across its kink, so it is excluded from Agent097's class.
-- Hence the two predicates already disagree at `n = 1`.
theorem cpwl_ne : ∃ n, Agent097.CPWL n ≠ Agent098.CPWL n :=
  ⟨1, fun h => reluFn_not_mem_097 (h ▸ reluFn_mem_098)⟩

-- `relun`: bridging `ComputesWithHiddenLayers` (existential `IsAffineTransformation`
-- encoding) with `ReLURepExact` (concrete `AffineTransform` structure encoding) needs
-- an induction on the hidden-layer count converting between the two affine-map
-- encodings; this is genuine work beyond a quick win under the current budget.
theorem relun (n k : ℕ) : Agent097.ReLUn n k = Agent098.ReLUn n k := sorry

-- `statement`: Agent097's own `CPWL` (shown above to force local affine agreement,
-- hence to exclude functions like ReLU with genuine kinks) cannot equal their
-- `ReLUn n (depthBound n)` for `n ≥ 3` (that class contains non-affine one-hidden-layer
-- networks once `depthBound n ≥ 1`), so the left side of the stated `Iff` is false; but
-- settling the right side requires the real mathematical content of Theorem 2 for
-- Agent098's polyhedral formalization, which is out of scope here.
theorem statement :
    (∀ n, 3 ≤ n → Agent097.CPWL n = Agent097.ReLUn n (Agent097.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent098.CPWL n = Agent098.ReLUn n (Agent098.depthBound n)) := sorry

end Bridge_097_098

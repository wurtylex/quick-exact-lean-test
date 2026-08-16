import QuickTest.Formalizations.Thm2_065
import QuickTest.Reference

namespace Star_065

/-!
# Star comparison: `Agent065` vs `Ref`

* `depthBound` is *literally* the same term (`⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`), so `depth`
  is `rfl`.
* `ReLUn` is the "exactly `k` hidden layers" reading (a `ReLUNetwork` structure with a width
  function `dims`), against the reference's "at most `k`".  Same set, but only via the padding
  identity `x = relu x - relu (-x)`; honest `sorry`.
* `CPWL` does **not** agree: `Agent065.CPWL` asks for agreement with one of finitely many
  affine maps on a *neighbourhood* of every point, which on connected `ℝⁿ` forces global
  affineness.  So `cpwl` is false — we prove `cpwl_ne`, and moreover `agent_side_false`.
-/

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent065.depthBound n = Ref.depthBound n := rfl

/-- Honest `sorry`: `Agent065.ReLUn n k` is *exactly* `k` hidden layers while `Ref.ReLUn n k`
is *at most* `k`.  The two sets coincide, but only through the padding identity
`x = relu x - relu (-x)`, which is a real theorem, not a definitional unfolding. -/
theorem relun (n k : ℕ) : Agent065.ReLUn n k = Ref.ReLUn n k := sorry

/-! ### `max 0 (x 0)` is not in `Agent065.CPWL` -/

/-- Neighbourhood agreement with a single affine map at the origin would force
`max 0 t = a * t + b` for all small `t`, which is absurd. -/
private lemma max_not_mem (n : ℕ) :
    (fun x : Fin (n + 1) → ℝ => max 0 (x 0)) ∉ Agent065.CPWL (n + 1) := by
  rintro ⟨-, m, g, hg, hloc⟩
  obtain ⟨i, hi⟩ := hloc 0
  obtain ⟨a, b, hab⟩ := hg i
  rw [Metric.eventually_nhds_iff] at hi
  obtain ⟨r, hr, hball⟩ := hi
  have key : ∀ t : ℝ, |t| < r → max 0 t = (∑ j, a j) * t + b := by
    intro t ht
    have hd : dist (fun _ => t : Fin (n + 1) → ℝ) 0 < r := by
      rw [dist_pi_lt_iff hr]
      intro j
      simpa [Real.dist_eq] using ht
    have h := hball hd
    rw [hab] at h
    simpa [Finset.sum_mul] using h
  have h0 := key 0 (by simpa using hr)
  have h1 := key (r / 2) (by rw [abs_of_pos] <;> linarith)
  have h2 := key (-(r / 2)) (by rw [abs_of_neg] <;> linarith)
  rw [max_self] at h0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ r / 2)] at h1
  rw [max_eq_left (by linarith : -(r / 2) ≤ (0 : ℝ))] at h2
  nlinarith [h0, h1, h2]

/-! ### `max 0 (x 0)` *is* in `Ref.CPWL 1` -/

/-- Every halfspace is a polyhedron (intersection of the one-element family). -/
private lemma poly_of_half {n : ℕ} {S : Set (Fin n → ℝ)} (h : Ref.IsHalfspace n S) :
    Ref.IsPolyhedron n S :=
  ⟨1, fun _ => S, fun _ => h, by rw [Set.iInter_const]⟩

/-- `x ↦ max 0 (x 0)` is CPWL in the reference sense: the two halflines cover `ℝ`. -/
private lemma max_mem_ref : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Ref.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2,
    ![{x : Fin 1 → ℝ | ∑ j, (1 : ℝ) * x j ≤ 0}, {x : Fin 1 → ℝ | ∑ j, (-1 : ℝ) * x j ≤ 0}],
    ![fun _ => 0, fun x => x 0], ?_, ?_, ?_, ?_⟩
  · exact Fin.forall_fin_two.2 ⟨poly_of_half ⟨fun _ => 1, 0, rfl⟩,
      poly_of_half ⟨fun _ => -1, 0, rfl⟩⟩
  · exact Fin.forall_fin_two.2 ⟨⟨0, 0, by simp⟩, ⟨fun _ => 1, 0, by simp⟩⟩
  · refine Set.eq_univ_of_forall fun x => ?_
    rcases le_or_gt (x 0) 0 with hx | hx
    · refine Set.mem_iUnion.2 ⟨0, ?_⟩
      simp only [Matrix.cons_val_zero, Set.mem_setOf_eq, Fin.sum_univ_one, one_mul]
      linarith
    · refine Set.mem_iUnion.2 ⟨1, ?_⟩
      simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, Set.mem_setOf_eq,
        Fin.sum_univ_one, neg_mul, one_mul]
      linarith
  · refine Fin.forall_fin_two.2 ⟨fun x hx => ?_, fun x hx => ?_⟩
    · simp only [Matrix.cons_val_zero, Set.mem_setOf_eq, Fin.sum_univ_one, one_mul] at hx ⊢
      exact max_eq_left (by linarith)
    · simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, Set.mem_setOf_eq,
        Fin.sum_univ_one, neg_mul, one_mul] at hx ⊢
      exact max_eq_right (by linarith)

/-- `Agent065.CPWL` is strictly stronger than `Ref.CPWL`, so the two differ. -/
theorem cpwl_ne : ∃ n, Agent065.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  have hmem : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent065.CPWL 1 := by
    rw [h]; exact max_mem_ref
  exact max_not_mem 0 hmem

/-! ### A ReLU network with any positive number of hidden layers computing `max 0 (x 0)` -/

/-- Widths `3, 1, 1, 1, …`. -/
private def dims3 : ℕ → ℕ
  | 0 => 3
  | _ + 1 => 1

/-- First layer: read off coordinate `0`. -/
private noncomputable def lay0 : Agent065.Affine 3 1 :=
  ⟨Matrix.of fun _ j => if j = 0 then (1 : ℝ) else 0, 0⟩

/-- Every later layer: the identity. -/
private noncomputable def lay1 : Agent065.Affine 1 1 := ⟨1, 0⟩

private noncomputable def lay : (i : ℕ) → Agent065.Affine (dims3 i) (dims3 (i + 1))
  | 0 => lay0
  | _ + 1 => lay1

/-- The network with `K + 1` hidden layers, all of width `1`. -/
private noncomputable def net (K : ℕ) : Agent065.ReLUNetwork 3 (K + 1) where
  dims := dims3
  dims_zero := rfl
  dims_last := rfl
  layer := lay

private lemma lay0_apply (x : Fin 3 → ℝ) : Agent065.Affine.apply lay0 x = fun _ => x 0 := by
  funext j
  simp [lay0, Agent065.Affine.apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private lemma lay1_apply (v : Fin 1 → ℝ) : Agent065.Affine.apply lay1 v = v := by
  funext j
  simp [lay1, Agent065.Affine.apply, Matrix.mulVec, dotProduct, Fin.sum_univ_one,
    Matrix.one_apply]

private lemma net_forward_zero (K : ℕ) (x : Fin 3 → ℝ) : (net K).forward 0 x = x := rfl

/-- From layer `1` on, the activation is constantly `max 0 (x 0)` (relu is idempotent, and
the final layer, which skips the relu, is the identity). -/
private lemma net_forward (K : ℕ) (x : Fin 3 → ℝ) (i : ℕ) :
    (net K).forward (i + 1) x = fun _ => max 0 (x 0) := by
  induction i with
  | zero =>
    show (if 0 + 1 = K + 1 + 1 then Agent065.Affine.apply lay0 ((net K).forward 0 x)
      else Agent065.reluVec (Agent065.Affine.apply lay0 ((net K).forward 0 x)))
        = fun _ => max 0 (x 0)
    rw [if_neg (by omega : ¬ (0 + 1 = K + 1 + 1)), net_forward_zero, lay0_apply]
    funext j
    rfl
  | succ i ih =>
    show (if i + 1 + 1 = K + 1 + 1 then Agent065.Affine.apply lay1 ((net K).forward (i + 1) x)
      else Agent065.reluVec (Agent065.Affine.apply lay1 ((net K).forward (i + 1) x)))
        = fun _ => max 0 (x 0)
    rw [ih, lay1_apply]
    split
    · rfl
    · funext j
      exact max_eq_right (le_max_left 0 (x 0))

private lemma net_output (K : ℕ) (x : Fin 3 → ℝ) : (net K).output x = max 0 (x 0) :=
  congrFun (net_forward K x (K + 1)) _

/-- `max 0 (x 0)` on `ℝ³` lies in `Agent065.ReLUn 3 (K+1)` for every `K`. -/
private lemma relu_mem_relun (K : ℕ) :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent065.ReLUn 3 (K + 1) :=
  ⟨net K, fun x => net_output K x⟩

/-- The `Agent065` reading of Theorem 2 is outright false: its `CPWL` misses `relu`. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent065.CPWL n = Agent065.ReLUn n (Agent065.depthBound n)) := by
  intro h
  have hmem : (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent065.CPWL 3 := by
    rw [h 3 (by norm_num)]
    obtain ⟨K, hK⟩ : ∃ K, Agent065.depthBound 3 = K + 1 := ⟨_, rfl⟩
    rw [hK]
    exact relu_mem_relun K
  exact max_not_mem 2 hmem

/-- The two readings of Theorem 2 are *not* equivalent: the left side is false
(`agent_side_false`), while the right side is the real Theorem 2, which is true.
Honest `sorry`: discharging it needs the true direction of `Ref.theorem2`, which is itself
`sorry`-ed in both files, and routing through it is forbidden. -/
theorem statement_ne :
    ¬ ((∀ n, 3 ≤ n → Agent065.CPWL n = Agent065.ReLUn n (Agent065.depthBound n)) ↔
      (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n))) := by
  intro hiff
  exact agent_side_false (hiff.2 (by sorry))

end Star_065

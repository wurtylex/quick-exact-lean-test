namespace Bridge_095_096

/-! ## `depthBound` : provably equal for `n ≥ 3` (agrees per the spec's easy case). -/

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent095.depthBound n = Agent096.depthBound n := by
  have h1n : (1 : ℕ) ≤ n := by omega
  have h1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub h1n, Nat.cast_one]
  unfold Agent095.depthBound Agent096.depthBound
  rw [h1]

/-! ## `ReLUn` : the two `HiddenLayers` / `ReLUNet` encodings are isomorphic term-by-term
(same alternating-composition structure, only packaged as a `Prop`-inductive vs. a
`Type`-inductive), so `ReLUn` agrees for every `n k`, not just `n ≥ 3`. -/

/-- Convert an `Agent095.Affine` map to an `Agent096.AffMap`; evaluation is preserved. -/
def aff95to96 {a b : ℕ} (T : Agent095.Affine a b) : Agent096.AffMap a b := ⟨T.A, T.c⟩

/-- Convert an `Agent096.AffMap` to an `Agent095.Affine` map; evaluation is preserved. -/
def aff96to95 {a b : ℕ} (T : Agent096.AffMap a b) : Agent095.Affine a b := ⟨T.A, T.c⟩

theorem aff95to96_eval {a b : ℕ} (T : Agent095.Affine a b) (x : Fin a → ℝ) :
    (aff95to96 T).eval x = T.eval x := rfl

theorem aff96to95_eval {a b : ℕ} (T : Agent096.AffMap a b) (x : Fin a → ℝ) :
    (aff96to95 T).eval x = T.eval x := rfl

theorem reluVec_eq {m : ℕ} (x : Fin m → ℝ) : Agent096.reluVec x = Agent095.reluVec x := by
  funext i; rfl

/-- Every `Agent095` network can be replayed as an `Agent096` network computing the same
function (same underlying alternating composition). -/
theorem hidden_to_net {n m k : ℕ} {g : (Fin n → ℝ) → (Fin m → ℝ)}
    (h : Agent095.HiddenLayers k g) :
    ∃ N : Agent096.ReLUNet n m k, ∀ x, N.eval x = g x := by
  induction h with
  | base T => exact ⟨Agent096.ReLUNet.last (aff95to96 T), fun x => aff95to96_eval T x⟩
  | step k T g hg ih =>
      obtain ⟨N', hN'⟩ := ih
      refine ⟨Agent096.ReLUNet.step (aff95to96 T) N', fun x => ?_⟩
      show N'.eval (Agent096.reluVec ((aff95to96 T).eval x)) = g (Agent095.reluVec (T.eval x))
      rw [aff95to96_eval, reluVec_eq, hN']

/-- Every `Agent096` network can be replayed as an `Agent095` network computing the same
function. -/
theorem net_to_hidden {n m k : ℕ} (N : Agent096.ReLUNet n m k) :
    ∃ g : (Fin n → ℝ) → (Fin m → ℝ), Agent095.HiddenLayers k g ∧ ∀ x, N.eval x = g x := by
  induction N with
  | last T =>
      exact ⟨T.eval, Agent095.HiddenLayers.base (aff96to95 T), fun x => (aff96to95_eval T x).symm⟩
  | step T rest ih =>
      obtain ⟨g, hg, hgeq⟩ := ih
      refine ⟨_, Agent095.HiddenLayers.step _ (aff96to95 T) g hg, fun x => ?_⟩
      show rest.eval (Agent096.reluVec (T.eval x)) = g (Agent095.reluVec ((aff96to95 T).eval x))
      rw [aff96to95_eval, reluVec_eq, hgeq]

theorem relun (n k : ℕ) : Agent095.ReLUn n k = Agent096.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨k', hk', g, hg, hfg⟩
    obtain ⟨N, hN⟩ := hidden_to_net hg
    exact ⟨k', hk', N, fun x => (hfg x).trans (congrFun (hN x) 0).symm⟩
  · rintro ⟨k', hk', N, hN⟩
    obtain ⟨g, hg, hgeq⟩ := net_to_hidden N
    exact ⟨k', hk', g, hg, fun x => (hN x).trans (congrFun (hgeq x) 0)⟩

/-! ## `CPWL` : genuinely different. Agent095 uses a global polyhedral cover; Agent096 uses
"locally equals one of finitely many affine maps at every point". The scalar ReLU
`f x = max 0 (x 0)` is a textbook CPWL function (two polyhedral pieces), so it is in
`Agent095.CPWL 1`. But at `x = 0` no single affine map can equal `f` on a whole
neighbourhood (approaching `0` from the negative side forces the affine map to be `0`,
from the positive side it forces it to be the identity), so `f ∉ Agent096.CPWL 1`. -/

private def diag (t : ℝ) : Fin 1 → ℝ := fun _ => t

private theorem diag_cont : Continuous diag := continuous_pi (fun _ => continuous_id)

private theorem aff_eval_diag (T : Agent096.AffMap 1 1) (t : ℝ) :
    T.eval (diag t) 0 = T.A 0 0 * t + T.c 0 := by
  simp [Agent096.AffMap.eval, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_one, diag]

theorem cpwl_ne : ∃ n, Agent095.CPWL n ≠ Agent096.CPWL n := by
  refine ⟨1, fun hset => ?_⟩
  set f : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0) with hf
  have hmem095 : f ∈ Agent095.CPWL 1 := by
    refine ⟨continuous_const.max (continuous_apply 0), 2,
      ![fun _ => (0 : ℝ), fun _ => (1 : ℝ)], ![(0 : ℝ), (0 : ℝ)],
      ![{x : Fin 1 → ℝ | x 0 ≤ 0}, {x : Fin 1 → ℝ | 0 ≤ x 0}], ?_, ?_, ?_, ?_⟩
    · refine Set.eq_univ_iff_forall.mpr fun x => ?_
      rcases le_total (x 0) 0 with h | h
      · exact Set.mem_iUnion.mpr ⟨0, by simpa using h⟩
      · exact Set.mem_iUnion.mpr ⟨1, by simpa using h⟩
    · intro j
      fin_cases j
      · simpa using isClosed_le (continuous_apply (0 : Fin 1)) continuous_const
      · simpa using isClosed_le continuous_const (continuous_apply (0 : Fin 1))
    · intro j
      fin_cases j <;>
        · intro x hx y hy a b ha hb hab
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_setOf_eq] at hx hy ⊢
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          nlinarith
    · intro j
      fin_cases j <;> intro x hx <;>
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_setOf_eq] at hx <;>
        simp [Fin.sum_univ_one, hf]
      · exact max_eq_left hx
      · exact max_eq_right hx
  have hf0 : f ∈ Agent096.CPWL 1 := hset ▸ hmem095
  obtain ⟨-, m, g, hloc⟩ := hf0
  obtain ⟨i, hi⟩ := hloc (fun _ => (0 : ℝ))
  have htendsto : Filter.Tendsto diag (nhds (0 : ℝ)) (nhds (fun _ => (0 : ℝ) : Fin 1 → ℝ)) := by
    have := diag_cont.continuousAt (x := (0 : ℝ))
    simpa [diag] using this
  have hev : ∀ᶠ t in nhds (0 : ℝ), f (diag t) = (g i).eval (diag t) 0 := htendsto.eventually hi
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  have heq : ∀ t : ℝ, dist t 0 < ε → max 0 t = (g i).A 0 0 * t + (g i).c 0 := by
    intro t ht
    have := hball ht
    rwa [aff_eval_diag] at this
  have h1 := heq (ε / 2) (by rw [Real.dist_eq]; rw [abs_of_pos (by linarith)]; linarith)
  have h2 := heq (ε / 4) (by rw [Real.dist_eq]; rw [abs_of_pos (by linarith)]; linarith)
  have h3 := heq (-(ε / 2)) (by rw [Real.dist_eq]; rw [abs_of_neg (by linarith)]; linarith)
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ ε / 2)] at h1
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ ε / 4)] at h2
  rw [max_eq_left (by linarith : -(ε / 2) ≤ 0)] at h3
  nlinarith [h1, h2, h3, hε]

/-! ## `statement` : we can show Agent096's own instantiated claim fails at `n = 1` via the
same kink argument (though `statement` quantifies `n ≥ 3`, so that alone is not conclusive
either way), but resolving the iff in either direction ultimately requires knowing the truth
value of Agent095's (or Agent096's) faithful rendering of the real Theorem 2 for `n ≥ 3` —
i.e. actually formalizing the paper's proof, which is out of scope for a bridge file. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent095.CPWL n = Agent095.ReLUn n (Agent095.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent096.CPWL n = Agent096.ReLUn n (Agent096.depthBound n)) := by
  sorry

end Bridge_095_096

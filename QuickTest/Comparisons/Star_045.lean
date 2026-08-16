import QuickTest.Formalizations.Thm2_045
import QuickTest.Reference

namespace Star_045

/-!
# Comparison of `Agent045` with the reference

* `ReLUn` : both files use the *at most `k` hidden layers* reading, with the same
  alternating-composition predicate.  Only the concrete encoding of an affine map
  differs (`Matrix.mulVec` vs. an explicit sum), so the two sets are equal — proved.
* `depthBound` : literally the same term — proved by `rfl`.
* `CPWL` : `Agent045` asks for agreement with one member of a finite affine family
  *on a neighbourhood of every point*.  On connected `ℝⁿ` that forces `f` to be
  globally affine, so it is strictly stronger than the reference's polyhedral-cover
  definition; refuted via `cpwl_ne`.
-/

/-! ### Dictionary for affine maps -/

private def toRef {a b : ℕ} (T : Agent045.AffineTransform a b) : Ref.Aff a b := ⟨T.A, T.c⟩

private def ofRef {a b : ℕ} (T : Ref.Aff a b) : Agent045.AffineTransform a b := ⟨T.M, T.c⟩

private lemma toRef_eval {a b : ℕ} (T : Agent045.AffineTransform a b) (x : Fin a → ℝ) :
    (toRef T).eval x = T.eval x := by
  funext i
  first
    | rfl
    | simp [toRef, Ref.Aff.eval, Agent045.AffineTransform.eval, Matrix.mulVec, dotProduct]

private lemma ofRef_eval {a b : ℕ} (T : Ref.Aff a b) (x : Fin a → ℝ) :
    (ofRef T).eval x = T.eval x := by
  funext i
  first
    | rfl
    | simp [ofRef, Ref.Aff.eval, Agent045.AffineTransform.eval, Matrix.mulVec, dotProduct]

private lemma reluVec_eq {m : ℕ} (v : Fin m → ℝ) : Agent045.reluVec v = Ref.reluVec v := rfl

/-- The two network predicates agree; only the encoding of the affine layers differs. -/
private lemma computes_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent045.ComputesWithHidden k n f ↔ Ref.ComputedBy n k f := by
  intro k
  induction k with
  | zero =>
      intro n f
      constructor
      · rintro ⟨T, hT⟩
        refine ⟨toRef T, fun x => ?_⟩
        rw [hT, toRef_eval]
      · rintro ⟨T, hT⟩
        refine ⟨ofRef T, fun x => ?_⟩
        rw [hT, ofRef_eval]
  | succ k ih =>
      intro n f
      constructor
      · rintro ⟨m, T, g, hg, hx⟩
        refine ⟨m, toRef T, g, (ih m g).mp hg, fun x => ?_⟩
        rw [hx, toRef_eval, reluVec_eq]
      · rintro ⟨m, T, g, hg, hx⟩
        refine ⟨m, ofRef T, g, (ih m g).mpr hg, fun x => ?_⟩
        rw [hx, ofRef_eval, reluVec_eq]

theorem relun (n k : ℕ) : Agent045.ReLUn n k = Ref.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, (computes_iff j n f).mp h⟩
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, (computes_iff j n f).mpr h⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent045.depthBound n = Ref.depthBound n := rfl

/-! ### `CPWL` : the neighbourhood reading is strictly stronger -/

/-- The witness `f x = max 0 (x 0)` on `ℝ¹`. -/
private noncomputable def fwit : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

private lemma fwit_continuous : Continuous fwit := by
  show Continuous fun x : Fin 1 → ℝ => max 0 (x 0)
  exact continuous_const.max (continuous_apply 0)

/-- The two halfspaces `{x 0 ≤ 0}` and `{-x 0 ≤ 0}`. -/
private def Pw (i : Fin 2) : Set (Fin 1 → ℝ) :=
  {x | (∑ j, (if i = 0 then (1:ℝ) else -1) * x j) ≤ 0}

/-- The two affine pieces `0` and `x ↦ x 0`. -/
private def gw (i : Fin 2) : (Fin 1 → ℝ) → ℝ := fun x => if i = 0 then 0 else x 0

private lemma halfspace_poly {n : ℕ} {S : Set (Fin n → ℝ)} (h : Ref.IsHalfspace n S) :
    Ref.IsPolyhedron n S :=
  ⟨1, fun _ => S, fun _ => h, by ext x; simp⟩

private lemma mem_Pw (i : Fin 2) (x : Fin 1 → ℝ) (hx : x ∈ Pw i) :
    (if i = 0 then (1:ℝ) else -1) * x 0 ≤ 0 := by
  have h : (∑ j, (if i = 0 then (1:ℝ) else -1) * x j) ≤ 0 := hx
  rwa [Fin.sum_univ_one] at h

private lemma fwit_mem_ref : fwit ∈ Ref.CPWL 1 := by
  show Ref.IsCPWL 1 fwit
  refine ⟨fwit_continuous, 2, Pw, gw, ?_, ?_, ?_, ?_⟩
  · exact fun i => halfspace_poly ⟨fun _ => (if i = 0 then (1:ℝ) else -1), 0, rfl⟩
  · intro i
    refine ⟨fun _ => (if i = 0 then (0:ℝ) else 1), 0, fun x => ?_⟩
    by_cases hi : i = 0 <;> simp [gw, hi, Fin.sum_univ_one]
  · refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ?_
    rcases le_total (x 0) 0 with h | h
    · refine ⟨0, ?_⟩
      show (∑ j, (if (0 : Fin 2) = 0 then (1:ℝ) else -1) * x j) ≤ 0
      rw [Fin.sum_univ_one, if_pos rfl]
      linarith
    · refine ⟨1, ?_⟩
      show (∑ j, (if (1 : Fin 2) = 0 then (1:ℝ) else -1) * x j) ≤ 0
      rw [Fin.sum_univ_one, if_neg (by decide : ¬((1 : Fin 2) = 0))]
      linarith
  · intro i x hx
    have h := mem_Pw i x hx
    show max 0 (x 0) = (if i = 0 then (0:ℝ) else x 0)
    by_cases hi : i = 0
    · rw [if_pos hi] at h ⊢
      exact max_eq_left (by linarith)
    · rw [if_neg hi] at h ⊢
      exact max_eq_right (by linarith)

/-- Local agreement with a finite affine family fails for `max 0 (x 0)` at the origin. -/
private lemma fwit_not_mem_agent : fwit ∉ Agent045.CPWL 1 := by
  rintro ⟨-, m, g, haff, hloc⟩
  obtain ⟨i, hi⟩ := hloc (fun _ => (0:ℝ))
  obtain ⟨a, b, hab⟩ := haff i
  have htend : Filter.Tendsto (fun t : ℝ => (fun _ => t : Fin 1 → ℝ)) (nhds 0)
      (nhds (fun _ => (0:ℝ))) := (continuous_pi fun _ => continuous_id).tendsto 0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (htend.eventually hi)
  have key : ∀ t : ℝ, |t| < ε → max 0 t = a 0 * t + b := by
    intro t ht
    have hd : dist t (0:ℝ) < ε := by rw [Real.dist_eq, sub_zero]; exact ht
    have h1 : fwit (fun _ => t) = g i (fun _ => t) := hball hd
    have h2 : g i (fun _ => t) = (∑ j : Fin 1, a j * t) + b := hab _
    rw [Fin.sum_univ_one] at h2
    rw [h2] at h1
    exact h1
  have h0 := key 0 (by simpa using hε)
  rw [max_self, mul_zero, zero_add] at h0
  have h1 := key (ε/2) (by rw [abs_of_pos (by linarith : (0:ℝ) < ε/2)]; linarith)
  have h2 := key (-(ε/2)) (by rw [abs_of_neg (by linarith : -(ε/2) < (0:ℝ))]; linarith)
  rw [← h0, add_zero, max_eq_right (by linarith : (0:ℝ) ≤ ε/2)] at h1
  rw [← h0, add_zero, max_eq_left (by linarith : -(ε/2) ≤ (0:ℝ)), mul_neg] at h2
  linarith

theorem cpwl_ne : ∃ n, Agent045.CPWL n ≠ Ref.CPWL n :=
  ⟨1, fun h => fwit_not_mem_agent (by rw [h]; exact fwit_mem_ref)⟩

/-- Honest `sorry`: the agent's side of the iff is *false* (`Agent045.CPWL n` contains only
globally affine functions, while `Agent045.ReLUn n (depthBound n)` does not), so the iff
holds iff the reference side holds — and the reference side is exactly Theorem 2, which is
`sorry` in `Reference.lean` and not provable here. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent045.CPWL n = Agent045.ReLUn n (Agent045.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_045

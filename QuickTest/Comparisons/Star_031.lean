import QuickTest.Formalizations.Thm2_031
import QuickTest.Reference

namespace Star_031

/-!
# Comparison of `Agent031` against `Ref`

* `ReLUn` and `depthBound` agree on the nose (`relun`, `depth`).
* `CPWL` does **not** agree: `Agent031.CPWL` asks for agreement with one of
  finitely many affine maps on a *neighbourhood* of every point, which on
  connected `ℝⁿ` forces global affineness.  We refute it with `cpwl_ne`.
-/

/-- The two encodings of an affine map evaluate to the same function. -/
private lemma eval_eq {a b : ℕ} (M : Matrix (Fin b) (Fin a) ℝ) (c : Fin b → ℝ)
    (x : Fin a → ℝ) :
    Ref.Aff.eval ⟨M, c⟩ x = Agent031.AffineMap'.eval ⟨M, c⟩ x := by
  funext i; rfl

/-- The two componentwise ReLUs are the same function. -/
private lemma reluVec_eq {m : ℕ} (v : Fin m → ℝ) :
    Ref.reluVec v = Agent031.reluVec v := rfl

/-- The two "exactly `k` hidden layers" predicates agree, by induction on `k`. -/
private lemma computedBy_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Ref.ComputedBy n k f ↔ Agent031.IsReLUComputable n k f := by
  intro k
  induction k with
  | zero =>
    intro n f
    simp only [Ref.ComputedBy, Agent031.IsReLUComputable]
    constructor
    · rintro ⟨⟨M, c⟩, hT⟩
      exact ⟨⟨M, c⟩, fun x => by rw [hT x, eval_eq]⟩
    · rintro ⟨⟨M, c⟩, hT⟩
      exact ⟨⟨M, c⟩, fun x => by rw [hT x, eval_eq]⟩
  | succ k ih =>
    intro n f
    simp only [Ref.ComputedBy, Agent031.IsReLUComputable]
    constructor
    · rintro ⟨m, ⟨M, c⟩, g, hg, hf⟩
      exact ⟨m, ⟨M, c⟩, g, (ih m g).1 hg, fun x => by rw [hf x, eval_eq, reluVec_eq]⟩
    · rintro ⟨m, ⟨M, c⟩, g, hg, hf⟩
      exact ⟨m, ⟨M, c⟩, g, (ih m g).2 hg, fun x => by rw [hf x, eval_eq, reluVec_eq]⟩

theorem relun (n k : ℕ) : Agent031.ReLUn n k = Ref.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, (computedBy_iff j n f).2 h⟩
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, (computedBy_iff j n f).1 h⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent031.depthBound n = Ref.depthBound n := rfl

/-- The witness separating the two notions of `CPWL`: `x ↦ max 0 x₀` on `ℝ¹`. -/
private noncomputable def wit : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

/-- A halfspace is a polyhedron (a one-fold intersection). -/
private lemma halfspace_poly {n : ℕ} {S : Set (Fin n → ℝ)} (h : Ref.IsHalfspace n S) :
    Ref.IsPolyhedron n S :=
  ⟨1, fun _ => S, fun _ => h, (Set.iInter_const S).symm⟩

/-- `wit` is continuous piecewise linear in the reference (polyhedral cover) sense. -/
private lemma mem_ref : wit ∈ Ref.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2,
    ![{x | (∑ i, (1 : ℝ) * x i) ≤ 0}, {x | (∑ i, (-1 : ℝ) * x i) ≤ 0}],
    ![fun _ => (0 : ℝ), fun x => x 0], ?_, ?_, ?_, ?_⟩
  · intro i
    refine halfspace_poly ?_
    fin_cases i
    · exact ⟨fun _ => 1, 0, rfl⟩
    · exact ⟨fun _ => -1, 0, rfl⟩
  · intro i
    fin_cases i
    · exact ⟨fun _ => 0, 0, fun x => by simp⟩
    · exact ⟨fun _ => 1, 0, fun x => by simp [Fin.sum_univ_one]⟩
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    rcases le_or_gt (x 0) 0 with h | h
    · refine ⟨0, ?_⟩
      show (∑ i, (1 : ℝ) * x i) ≤ 0
      rw [Fin.sum_univ_one]; linarith
    · refine ⟨1, ?_⟩
      show (∑ i, (-1 : ℝ) * x i) ≤ 0
      rw [Fin.sum_univ_one]; linarith
  · intro i
    fin_cases i
    · intro x hx
      have hx' : (∑ j, (1 : ℝ) * x j) ≤ 0 := hx
      rw [Fin.sum_univ_one] at hx'
      show max 0 (x 0) = 0
      exact max_eq_left (by linarith)
    · intro x hx
      have hx' : (∑ j, (-1 : ℝ) * x j) ≤ 0 := hx
      rw [Fin.sum_univ_one] at hx'
      show max 0 (x 0) = x 0
      exact max_eq_right (by linarith)

/-- `wit` is *not* in `Agent031.CPWL 1`: near `0` it would have to be affine, but
`max 0 ·` is not affine on any neighbourhood of `0`. -/
private lemma not_mem_agent : wit ∉ Agent031.CPWL 1 := by
  intro hmem
  obtain ⟨-, m, T, h⟩ := hmem
  obtain ⟨i, ε, hε, hy⟩ := h 0
  have key : ∀ c : ℝ, |c| < ε → max 0 c = (T i).A 0 0 * c + (T i).bias 0 := by
    intro c hc
    have hd : dist (fun _ : Fin 1 => c) (0 : Fin 1 → ℝ) < ε :=
      (dist_pi_lt_iff hε).2 fun j => by simpa [Real.dist_eq] using hc
    have hh := hy _ hd
    simpa [wit, Agent031.AffineMap'.eval, Fin.sum_univ_one] using hh
  have h0 := key 0 (by simpa using hε)
  have h1 := key (ε / 2) (by rw [abs_of_pos (by linarith : (0:ℝ) < ε / 2)]; linarith)
  have h2 := key (-(ε / 2)) (by rw [abs_of_neg (by linarith : -(ε / 2) < (0:ℝ))]; linarith)
  rw [max_self, mul_zero] at h0
  rw [max_eq_right (by linarith : (0:ℝ) ≤ ε / 2)] at h1
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0:ℝ)), mul_neg] at h2
  linarith

/-- `Agent031.CPWL` is strictly stronger than `Ref.CPWL`: the neighbourhood
formulation is refuted at `n = 1` by `wit = fun x => max 0 (x 0)`. -/
theorem cpwl_ne : ∃ n, Agent031.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun hEq => not_mem_agent ?_⟩
  rw [hEq]
  exact mem_ref

/-- Honest `sorry`.  `cpwl_ne` shows the two `CPWL`s differ, and in fact the
left-hand side of this iff is false (`Agent031.CPWL n` contains only globally
affine functions, while `ReLUn n (depthBound n)` contains `max 0 ·`), so the iff
is equivalent to the reference Theorem 2 itself — which is `sorry`-ed upstream
and cannot be discharged here without proving the paper's main result. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent031.CPWL n = Agent031.ReLUn n (Agent031.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_031

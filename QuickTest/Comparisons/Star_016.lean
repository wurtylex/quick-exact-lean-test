import QuickTest.Formalizations.Thm2_016
import QuickTest.Reference

namespace Star_016

/-!
# Star comparison: `Agent016` vs `Ref`

* `depthBound` : *identical* (`⌈·⌉₊` is notation for `Nat.ceil`), so `depth` is `rfl`.
* `ReLUn`      : both files use **at most `k`** hidden layers; the only difference is
  that `Ref.ComputedBy` is a structural recursion and `Agent016.ComputesHidden` is an
  inductive predicate.  They are equivalent, and `relun` is proved below.
* `CPWL`       : `Agent016` uses *local* (neighbourhood) agreement with a finite family
  of affine maps.  On connected `ℝⁿ` that forces global affineness, so it is strictly
  stronger than the reference's polyhedral-cover definition; `cpwl_ne` is proved below.
-/

/-! ### `ReLUn` -/

private lemma computes_of_computedBy :
    ∀ (n k : ℕ) (f : (Fin n → ℝ) → ℝ), Ref.ComputedBy n k f → Agent016.ComputesHidden n k f := by
  intro n k
  induction k generalizing n with
  | zero =>
    intro f hf
    have hf' : ∃ T : Ref.Aff n 1, ∀ x, f x = T.eval x 0 := hf
    obtain ⟨T, hT⟩ := hf'
    have hfe : f = fun x => Agent016.applyAffine ((T.M, T.c) : Agent016.AffineT n 1) x 0 := by
      funext x; exact hT x
    rw [hfe]
    exact Agent016.ComputesHidden.zero _
  | succ k ih =>
    intro f hf
    have hf' : ∃ (m : ℕ) (T : Ref.Aff n m) (g : (Fin m → ℝ) → ℝ),
        Ref.ComputedBy m k g ∧ ∀ x, f x = g (Ref.reluVec (T.eval x)) := hf
    obtain ⟨m, T, g, hg, hfx⟩ := hf'
    have hfe : f = fun x =>
        g (Agent016.reluVec (Agent016.applyAffine ((T.M, T.c) : Agent016.AffineT n m) x)) := by
      funext x; exact hfx x
    rw [hfe]
    exact Agent016.ComputesHidden.succ _ (ih m g hg)

private lemma computedBy_of_computes {n k : ℕ} {f : (Fin n → ℝ) → ℝ} :
    Agent016.ComputesHidden n k f → Ref.ComputedBy n k f := by
  intro h
  induction h with
  | zero T => exact ⟨⟨T.1, T.2⟩, fun _ => rfl⟩
  | succ T _ ih => exact ⟨_, ⟨T.1, T.2⟩, _, ih, fun _ => rfl⟩

/-- The two `ReLUn`s agree: both mean "at most `k` hidden layers". -/
theorem relun (n k : ℕ) : Agent016.ReLUn n k = Ref.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨j, hj, h⟩; exact ⟨j, hj, computedBy_of_computes h⟩
  · rintro ⟨j, hj, h⟩; exact ⟨j, hj, computes_of_computedBy n j f h⟩

/-! ### `depthBound` -/

/-- Both files write `⌈Real.logb 3 (n - 1)⌉₊ + 1`, character for character. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent016.depthBound n = Ref.depthBound n := rfl

/-! ### `CPWL` : the neighbourhood definition is strictly stronger -/

private lemma poly_of_half {n : ℕ} {S : Set (Fin n → ℝ)} (h : Ref.IsHalfspace n S) :
    Ref.IsPolyhedron n S :=
  ⟨1, fun _ => S, fun _ => h, (Set.iInter_const S).symm⟩

/-- `x ↦ max 0 (x 0)` is CPWL in the reference (polyhedral-cover) sense on `ℝ¹`. -/
private lemma mem_ref : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Ref.CPWL 1 := by
  refine ⟨Continuous.max continuous_const (continuous_apply 0), 2,
      ![{x : Fin 1 → ℝ | (∑ i, (1:ℝ) * x i) ≤ 0},
        {x : Fin 1 → ℝ | (∑ i, (-1:ℝ) * x i) ≤ 0}],
      ![fun _ => (0:ℝ), fun x => x 0], ?_, ?_, ?_, ?_⟩
  · intro i
    refine poly_of_half ?_
    fin_cases i
    · exact ⟨fun _ => (1:ℝ), 0, rfl⟩
    · exact ⟨fun _ => (-1:ℝ), 0, rfl⟩
  · intro i
    fin_cases i
    · exact ⟨fun _ => (0:ℝ), 0, by intro x; simp⟩
    · exact ⟨fun _ => (1:ℝ), 0, by intro x; simp⟩
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    rcases le_or_gt (x 0) 0 with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h.le⟩
  · intro i x hx
    fin_cases i
    · exact max_eq_left (by simpa using hx)
    · exact max_eq_right (by simpa using hx)

/-- `x ↦ max 0 (x 0)` is **not** in `Agent016.CPWL 1`: neighbourhood agreement at the
origin would force `max 0 t = a * t + b` on a whole interval around `0`. -/
private lemma not_mem_agent : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∉ Agent016.CPWL 1 := by
  rintro ⟨-, m, g, hg, hloc⟩
  obtain ⟨i, hev⟩ := hloc 0
  obtain ⟨a, c, hgi⟩ := hg i
  have hs : Filter.Tendsto (fun t : ℝ => (fun _ => t : Fin 1 → ℝ)) (nhds 0) (nhds 0) :=
    (continuous_pi fun _ => continuous_id).tendsto' 0 0 (by funext j; rfl)
  have key : ∀ᶠ t : ℝ in nhds 0, max 0 t = a 0 * t + c := by
    filter_upwards [hs.eventually hev] with t ht
    have h2 := ht.trans (hgi fun _ => t)
    simpa only [Fin.sum_univ_one] using h2
  rw [Metric.eventually_nhds_iff] at key
  obtain ⟨ε, hε, hkey⟩ := key
  have e0 := hkey (show dist (0:ℝ) 0 < ε by simpa using hε)
  have ep := hkey (show dist (ε/2) (0:ℝ) < ε by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
  have en := hkey (show dist (-(ε/2)) (0:ℝ) < ε by
    rw [Real.dist_eq, sub_zero, abs_of_neg (by linarith)]; linarith)
  rw [max_self] at e0
  rw [max_eq_right (by linarith : (0:ℝ) ≤ ε/2)] at ep
  rw [max_eq_left (by linarith : -(ε/2) ≤ (0:ℝ))] at en
  linarith

/-- **Refutation.** `Agent016.CPWL` (local/neighbourhood agreement) is strictly smaller
than `Ref.CPWL` (polyhedral cover): `x ↦ max 0 (x 0)` separates them at `n = 1`. -/
theorem cpwl_ne : ∃ n, Agent016.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  exact not_mem_agent ((Set.ext_iff.mp h (fun x : Fin 1 → ℝ => max 0 (x 0))).mpr mem_ref)

/-! ### The statement

`statement` is in fact **false**: the reference side holds (Theorem 2 of the paper) while
the `Agent016` side fails, because `Agent016.CPWL n` contains only globally affine maps
whereas `ReLUn n (depthBound n)` contains e.g. `x ↦ max 0 (x 0)`.  Refuting the `↔`
nevertheless requires *proving* the reference's Theorem 2, which is itself `sorry`-ed in
`Reference.lean` and is the entire content of the paper.  So this one is left open. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent016.CPWL n = Agent016.ReLUn n (Agent016.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_016

/-!
# Star comparison: `Agent082` vs `Ref`

* `ReLUn`  — same definition up to renaming (`AffineMap'`/`Aff`, `NetComputes`/`ComputedBy`),
  and both take **at most** `k` hidden layers.  Proved.
* `depthBound` — literally the same term (`⌈·⌉₊` *is* `Nat.ceil`).  Proved by `rfl`.
* `CPWL` — `Agent082` uses *local agreement on a neighbourhood* with a finite affine family.
  On connected `ℝⁿ` that forces global affineness, so it is strictly stronger than the
  reference's polyhedral-cover definition.  Refuted via `cpwl_ne`.
-/

namespace Star_082

/-! ### `ReLUn`: the two network predicates agree -/

/-- `Agent082.NetComputes` and `Ref.ComputedBy` are the same predicate: both peel off the
first affine map and ReLU, and the two affine-map structures carry the same data. -/
private lemma netComputes_iff :
    ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ), Agent082.NetComputes n k f ↔ Ref.ComputedBy n k f := by
  intro k
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨T, hT⟩
      exact ⟨⟨T.A, T.c⟩, hT⟩
    · rintro ⟨T, hT⟩
      exact ⟨⟨T.M, T.c⟩, hT⟩
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, T, g, hg, hf⟩
      exact ⟨m, ⟨T.A, T.c⟩, g, (ih m g).mp hg, hf⟩
    · rintro ⟨m, T, g, hg, hf⟩
      exact ⟨m, ⟨T.M, T.c⟩, g, (ih m g).mpr hg, hf⟩

theorem relun (n k : ℕ) : Agent082.ReLUn n k = Ref.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, (netComputes_iff j n f).mp h⟩
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, (netComputes_iff j n f).mpr h⟩

/-! ### `depthBound`: identical terms -/

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent082.depthBound n = Ref.depthBound n := rfl

/-! ### `CPWL`: the neighbourhood definition is strictly stronger -/

private lemma isPolyhedron_of_halfspace {n : ℕ} {S : Set (Fin n → ℝ)}
    (h : Ref.IsHalfspace n S) : Ref.IsPolyhedron n S :=
  ⟨1, fun _ => S, fun _ => h, (Set.iInter_const S).symm⟩

private lemma mem_ball_of (ε t : ℝ) (h1 : -ε < t) (h2 : t < ε) :
    t ∈ Metric.ball (0 : ℝ) ε := by
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
  exact ⟨h1, h2⟩

/-- `x ↦ max 0 (x 0)` is CPWL in the reference sense: the two halfspaces `x 0 ≤ 0` and
`-x 0 ≤ 0` cover `ℝ¹`, and on them `f` is `0` and `x 0` respectively. -/
private lemma f_mem_ref : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Ref.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2,
    ![{x : Fin 1 → ℝ | ∑ i, (1 : ℝ) * x i ≤ 0}, {x : Fin 1 → ℝ | ∑ i, (-1 : ℝ) * x i ≤ 0}],
    ![fun _ : Fin 1 → ℝ => (0 : ℝ), fun x : Fin 1 → ℝ => x 0], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact isPolyhedron_of_halfspace ⟨fun _ => 1, 0, rfl⟩
    · exact isPolyhedron_of_halfspace ⟨fun _ => -1, 0, rfl⟩
  · intro i
    fin_cases i
    · exact ⟨0, 0, by simp⟩
    · exact ⟨fun _ => 1, 0, by simp⟩
  · ext x
    simp only [Set.mem_univ, iff_true, Set.mem_iUnion]
    rcases le_total (x 0) 0 with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  · intro i x hx
    fin_cases i
    · show max 0 (x 0) = 0
      exact max_eq_left (by simpa using hx)
    · show max 0 (x 0) = x 0
      exact max_eq_right (by simpa using hx)

/-- `x ↦ max 0 (x 0)` is **not** in `Agent082.CPWL 1`: agreement with a single affine map on a
whole neighbourhood of `0` forces `b = 0` (at `0`), `a 0 = 1` (at `ε/2`) and `a 0 = -1`
(at `-ε/2`). -/
private lemma f_not_mem_agent :
    (fun x : Fin 1 → ℝ => max 0 (x 0)) ∉ Agent082.CPWL 1 := by
  rintro ⟨-, m, g, hg, hloc⟩
  obtain ⟨j, U, hU, hUeq⟩ := hloc 0
  obtain ⟨a, b, hab⟩ := hg j
  have hcont : Continuous (fun t : ℝ => (fun _ : Fin 1 => t)) :=
    continuous_pi fun _ => continuous_id
  have hpre : (fun t : ℝ => (fun _ : Fin 1 => t)) ⁻¹' U ∈ nhds (0 : ℝ) :=
    hcont.continuousAt.preimage_mem_nhds hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  have key : ∀ t : ℝ, -ε < t → t < ε → max 0 t = a 0 * t + b := by
    intro t h1 h2
    have ht : (fun _ : Fin 1 => t) ∈ U := hball (mem_ball_of ε t h1 h2)
    have h := hUeq _ ht
    rw [hab] at h
    simpa using h
  have h0 := key 0 (by linarith) hε
  have h1 := key (ε / 2) (by linarith) (by linarith)
  have h2 := key (-(ε / 2)) (by linarith) (by linarith)
  rw [max_self] at h0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ ε / 2)] at h1
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0 : ℝ))] at h2
  nlinarith [h0, h1, h2]

/-- `Agent082.CPWL` is strictly stronger than `Ref.CPWL`: already at `n = 1` the ReLU
function itself separates them. -/
theorem cpwl_ne : ∃ n, Agent082.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => f_not_mem_agent ?_⟩
  rw [h]
  exact f_mem_ref

/-! ### The statement

Honest `sorry`.  The agent side is *false* (`Agent082.CPWL n` contains only globally affine
functions, while `Ref.ReLUn n (depthBound n)` contains `x ↦ max 0 (x 0)`), so the iff is in
fact false — but deriving `False` from the iff needs the *reference* side, which is exactly
Theorem 2 of the paper, `sorry`-ed in `Ref` and out of reach here.  So neither `statement`
nor `statement_ne` is provable within this comparison; we leave the positive form open
rather than launder a `sorry` through `Ref.theorem2`. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent082.CPWL n = Agent082.ReLUn n (Agent082.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_082

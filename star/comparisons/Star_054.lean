/-!
# Star comparison 054 vs the reference

`Agent054` differs from `Ref` in exactly one place that matters: its pieces are
**closed convex** sets rather than **polyhedra**.  Every polyhedron is closed and
convex, so `Ref.CPWL n ⊆ Agent054.CPWL n` (proved below as `cpwl_subset`).  The
converse is a genuine theorem (a continuous finite selection of affine functions
is affine on each cell of the hyperplane arrangement `{aᵢ = aⱼ}`, hence
polyhedrally piecewise linear), which is well beyond the budget here.

Everything else matches definitionally: `NetComputes k n f` is `Ref.ComputedBy
n k f` up to `funext` and the renaming of the affine-map structure, `ReLUn` is
"at most `k`" on both sides, and `depthBound` is literally the same function.
-/

namespace Star_054

/-! ### Networks: the two definitions agree -/

/-- `Agent054.NetComputes` and `Ref.ComputedBy` are the same predicate: the
recursions have the same shape, the affine-map structures are isomorphic, and
the two `relu`s are definitionally `max 0 ·`. -/
private theorem net_iff (k : ℕ) : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent054.NetComputes k n f ↔ Ref.ComputedBy n k f := by
  induction k with
  | zero =>
      intro n f
      show (∃ T : Agent054.AffineMap n 1, f = fun x => T.eval x 0) ↔
        (∃ T : Ref.Aff n 1, ∀ x, f x = T.eval x 0)
      constructor
      · rintro ⟨T, rfl⟩
        exact ⟨⟨T.A, T.c⟩, fun x => rfl⟩
      · rintro ⟨T, hT⟩
        exact ⟨⟨T.M, T.c⟩, funext fun x => hT x⟩
  | succ k ih =>
      intro n f
      show (∃ (m : ℕ) (T : Agent054.AffineMap n m) (g : (Fin m → ℝ) → ℝ),
            Agent054.NetComputes k m g ∧ f = fun x => g (Agent054.reluVec (T.eval x))) ↔
        (∃ (m : ℕ) (T : Ref.Aff n m) (g : (Fin m → ℝ) → ℝ),
            Ref.ComputedBy m k g ∧ ∀ x, f x = g (Ref.reluVec (T.eval x)))
      constructor
      · rintro ⟨m, T, g, hg, rfl⟩
        exact ⟨m, ⟨T.A, T.c⟩, g, (ih m g).1 hg, fun x => rfl⟩
      · rintro ⟨m, T, g, hg, hf⟩
        exact ⟨m, ⟨T.M, T.c⟩, g, (ih m g).2 hg, funext fun x => hf x⟩

/-! ### Pieces: polyhedra are closed and convex -/

private lemma continuous_lin {n : ℕ} (a : Fin n → ℝ) :
    Continuous fun x : Fin n → ℝ => ∑ i, a i * x i :=
  continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_apply i)

private lemma convex_halfspace_sum {n : ℕ} (a : Fin n → ℝ) (b : ℝ) :
    Convex ℝ {x : Fin n → ℝ | ∑ i, a i * x i ≤ b} := by
  intro x hx y hy p q hp hq hpq
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  have h : ∑ i, a i * (p • x + q • y) i
      = p * (∑ i, a i * x i) + q * (∑ i, a i * y i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hb : p * b + q * b = b := by rw [← add_mul, hpq, one_mul]
  have h1 : p * (∑ i, a i * x i) ≤ p * b := mul_le_mul_of_nonneg_left hx hp
  have h2 : q * (∑ i, a i * y i) ≤ q * b := mul_le_mul_of_nonneg_left hy hq
  rw [h]
  linarith

private lemma halfspace_closed_convex {n : ℕ} {S : Set (Fin n → ℝ)}
    (h : Ref.IsHalfspace n S) : IsClosed S ∧ Convex ℝ S := by
  obtain ⟨a, b, rfl⟩ := h
  exact ⟨isClosed_le (continuous_lin a) continuous_const,
    convex_halfspace_sum a b⟩

private lemma polyhedron_closed_convex {n : ℕ} {S : Set (Fin n → ℝ)}
    (h : Ref.IsPolyhedron n S) : IsClosed S ∧ Convex ℝ S := by
  obtain ⟨m, H, hH, rfl⟩ := h
  exact ⟨isClosed_iInter fun i => (halfspace_closed_convex (hH i)).1,
    convex_iInter fun i => (halfspace_closed_convex (hH i)).2⟩

private lemma isAffine_to {n : ℕ} {g : (Fin n → ℝ) → ℝ} (h : Ref.IsAffine g) :
    Agent054.IsAffineFun n g := by
  obtain ⟨a, b, hb⟩ := h
  exact ⟨a, b, funext hb⟩

/-- The easy half of `cpwl`: a polyhedral cover is in particular a cover by
closed convex sets, so every reference-CPWL function is agent-CPWL. -/
theorem cpwl_subset (n : ℕ) : Ref.CPWL n ⊆ Agent054.CPWL n := by
  intro f hf
  simp only [Ref.CPWL, Ref.IsCPWL, Set.mem_setOf_eq] at hf
  obtain ⟨hcont, m, P, g, hP, hg, hcov, hfg⟩ := hf
  simp only [Agent054.CPWL, Set.mem_setOf_eq]
  exact ⟨hcont, m, P, g, fun i => (polyhedron_closed_convex (hP i)).2,
    fun i => (polyhedron_closed_convex (hP i)).1, hcov,
    fun i => isAffine_to (hg i), fun i x hx => hfg i x hx⟩

/-! ### The four obligations -/

/-- Both sides are the honest piecewise-linearity condition; they really are
equal, but the inclusion `Agent054.CPWL n ⊆ Ref.CPWL n` needs the theorem that a
continuous function which is a finite selection of affine functions is affine on
each cell of the arrangement `{aᵢ = aⱼ}` (a connectedness argument on the cells),
which does not fit in this file.  The other inclusion is `cpwl_subset` above. -/
theorem cpwl (n : ℕ) : Agent054.CPWL n = Ref.CPWL n := sorry

theorem relun (n k : ℕ) : Agent054.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent054.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, (net_iff j n f).1 h⟩
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, (net_iff j n f).2 h⟩

/-- Both files define `depthBound n = ⌈Real.logb 3 (n - 1)⌉₊ + 1` verbatim. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent054.depthBound n = Ref.depthBound n := rfl

/-- Depends on `cpwl`: with `relun` and `depth` in hand the two statements
reduce to `Agent054.CPWL n = S n` versus `Ref.CPWL n = S n` for the common set
`S n = Ref.ReLUn n (Ref.depthBound n)`, and `cpwl_subset` only gives one
inclusion, which is not enough for either direction of the iff. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent054.CPWL n = Agent054.ReLUn n (Agent054.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_054

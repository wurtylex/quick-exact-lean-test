/-!
# Star comparison 068 vs. the reference

`Agent068` is in the *polyhedral-subdivision* family: `CPWL n` asks for
continuity plus a **finite** cover of `ℝⁿ` by regions on each of which `f`
agrees with an affine functional.  The only deviation from `Ref` is the shape
of the regions: `Ref` asks for polyhedra (finite intersections of closed
halfspaces), `Agent068` asks merely for *convex* sets.

* Every polyhedron is convex, so `Ref.CPWL n ⊆ Agent068.CPWL n` — proved below
  (`ref_subset_agent`).
* The reverse inclusion is a genuine theorem: if a continuous `f` is a
  selection from finitely many affine maps `g₁,…,g_m` (which is what the convex
  cover gives, the convexity itself being unused), then the arrangement of the
  hyperplanes `{gᵢ = gⱼ}` cuts `ℝⁿ` into finitely many polyhedral cells, and on
  the interior of each cell the sets `{f = gᵢ}` are disjoint, closed and cover a
  connected set, so exactly one of them is everything.  That is a real
  hyperplane-arrangement argument, far beyond the budget here, so `cpwl` is
  left as an honest `sorry` — the statement is believed **true**, not refuted.

`depthBound` is literally the same definition on both sides.
-/

namespace Star_068

/-- The sublevel set of `x ↦ ∑ i, a i * x i` is convex, proved directly from the
definition of `Convex`. -/
private lemma convex_halfspace_sum {n : ℕ} (a : Fin n → ℝ) (b : ℝ) :
    Convex ℝ {x : Fin n → ℝ | ∑ i, a i * x i ≤ b} := by
  intro x hx y hy p q hp hq hpq
  have hx' : ∑ i, a i * x i ≤ b := hx
  have hy' : ∑ i, a i * y i ≤ b := hy
  have key : ∑ i, a i * (p • x + q • y) i
      = p * (∑ i, a i * x i) + q * (∑ i, a i * y i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hb : p * b + q * b = b := by rw [← add_mul, hpq, one_mul]
  show ∑ i, a i * (p • x + q • y) i ≤ b
  rw [key]
  linarith [mul_le_mul_of_nonneg_left hx' hp, mul_le_mul_of_nonneg_left hy' hq]

/-- A closed affine halfspace in the sense of `Ref` is convex. -/
private lemma convex_of_isHalfspace {n : ℕ} {S : Set (Fin n → ℝ)}
    (h : Ref.IsHalfspace n S) : Convex ℝ S := by
  obtain ⟨a, b, rfl⟩ := h
  exact convex_halfspace_sum a b

/-- A polyhedron in the sense of `Ref` is convex: it is an intersection of
halfspaces, and convexity is preserved by arbitrary intersections. -/
private lemma convex_of_isPolyhedron {n : ℕ} {S : Set (Fin n → ℝ)}
    (h : Ref.IsPolyhedron n S) : Convex ℝ S := by
  obtain ⟨m, H, hH, rfl⟩ := h
  exact convex_iInter fun i => convex_of_isHalfspace (hH i)

/-- The two notions of "affine functional `ℝⁿ → ℝ`" are the *same* proposition,
letter for letter (`∑ i, a i * x i` is notation for `Finset.univ.sum …`). -/
private lemma isAffine_iff {n : ℕ} (g : (Fin n → ℝ) → ℝ) :
    Ref.IsAffine g ↔ Agent068.IsAffineFun n g := Iff.rfl

/-- The easy inclusion: a polyhedral subdivision is in particular a convex one. -/
private lemma ref_subset_agent (n : ℕ) : Ref.CPWL n ⊆ Agent068.CPWL n := by
  intro f hf
  obtain ⟨hc, m, P, g, hP, hg, hcov, hagree⟩ := hf
  exact ⟨hc, m, g, P, fun i => (isAffine_iff _).1 (hg i),
    fun i => convex_of_isPolyhedron (hP i), hcov, hagree⟩

/-- The hard inclusion, isolated so that the reason for the `sorry` is visible:
a finite *convex* subdivision can be refined to a finite *polyhedral* one, via
the arrangement of the hyperplanes `{gᵢ = gⱼ}`.  True, but a real theorem. -/
private lemma agent_subset_ref (n : ℕ) : Agent068.CPWL n ⊆ Ref.CPWL n := by
  sorry -- needs the hyperplane-arrangement refinement argument; out of budget

/-- `CPWL` agrees.  Both sides are "continuous + finite subdivision with an
affine functional on each piece"; only the shape of the pieces differs
(polyhedral vs. convex), and those give the same class of functions. -/
theorem cpwl (n : ℕ) : Agent068.CPWL n = Ref.CPWL n :=
  Set.Subset.antisymm (agent_subset_ref n) (ref_subset_agent n)

/-- `ReLUn` agrees.  Both sides use the "at most `k` hidden layers" reading, but
the network *encodings* are unrelated: `Ref` uses honest `Fin`-indexed matrices
`Aff a b`, while `Agent068` uses ambient `Vec = ℕ → ℝ` layers with widths
`width : ℕ → ℕ`, `width 0 = n`, `width (k+1) = 1`, and evaluation truncated to
`Finset.range (width i)`.  Translating between them means, in each direction,
building a network of the other kind and proving by induction on the depth that
the two forward passes agree — with the `Agent068` side additionally needing
that coordinates beyond `width i` never influence the output.  Doable but long. -/
theorem relun (n k : ℕ) : Agent068.ReLUn n k = Ref.ReLUn n k := by
  sorry -- genuine encoding-translation induction (Vec-with-widths ↔ Fin-matrices)

/-- `depthBound` agrees: both files write `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`,
so this is definitional. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent068.depthBound n = Ref.depthBound n := rfl

/-- The two Theorem-2 statements are equivalent.  Given `cpwl`, `relun` and
`depth` this would be immediate, but `cpwl` and `relun` are themselves `sorry`,
so proving `statement` from them would launder those `sorry`s; it is recorded
honestly here instead. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent068.CPWL n = Agent068.ReLUn n (Agent068.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
  sorry -- would follow from `cpwl`/`relun`/`depth`, both of which are still open

end Star_068

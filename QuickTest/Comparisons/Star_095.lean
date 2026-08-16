import QuickTest.Formalizations.Thm2_095
import QuickTest.Reference

namespace Star_095

/-!
# Comparison of `Agent095` against `Ref`

`Agent095` is a *subdivision* formalization, not a neighbourhood-agreement one:
its `CPWL n` asks for a finite cover of `ℝⁿ` by **closed convex** sets on each of
which `f` agrees with an affine functional, while `Ref.CPWL n` asks for a finite
cover by **polyhedra**.  Since every polyhedron is closed and convex, we get
`Ref.CPWL n ⊆ Agent095.CPWL n` outright (`ref_cpwl_subset` below).  The reverse
inclusion is true but is a genuine theorem (a continuous selection of finitely
many affine maps is polyhedrally piecewise linear), so `cpwl` is left `sorry`.

The network classes match exactly — both read `ReLU_{n,k}` as "**at most** `k`
hidden layers", and both peel layers off the input side — so `relun` is proved.
-/

/-! ### Halfspaces and polyhedra are closed and convex -/

/-- A closed affine halfspace `{x | ∑ i, a i * x i ≤ b}` is convex, straight from
the definition of `Convex`. -/
private lemma convex_halfspace_sum {n : ℕ} (a : Fin n → ℝ) (b : ℝ) :
    Convex ℝ {x : Fin n → ℝ | (∑ i, a i * x i) ≤ b} := by
  intro x hx y hy p q hp hq hpq
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  have hxy : (∑ i, a i * (p • x + q • y) i)
      = p * (∑ i, a i * x i) + q * (∑ i, a i * y i) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hxy]
  have h1 : p * (∑ i, a i * x i) ≤ p * b := mul_le_mul_of_nonneg_left hx hp
  have h2 : q * (∑ i, a i * y i) ≤ q * b := mul_le_mul_of_nonneg_left hy hq
  nlinarith [hpq]

private lemma halfspace_closed_convex {n : ℕ} {S : Set (Fin n → ℝ)}
    (h : Ref.IsHalfspace n S) : IsClosed S ∧ Convex ℝ S := by
  obtain ⟨a, b, rfl⟩ := h
  have hcont : Continuous fun x : Fin n → ℝ => ∑ i, a i * x i :=
    continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_apply i)
  exact ⟨isClosed_le hcont continuous_const, convex_halfspace_sum a b⟩

private lemma polyhedron_closed_convex {n : ℕ} {S : Set (Fin n → ℝ)}
    (h : Ref.IsPolyhedron n S) : IsClosed S ∧ Convex ℝ S := by
  obtain ⟨m, H, hH, rfl⟩ := h
  exact ⟨isClosed_iInter fun i => (halfspace_closed_convex (hH i)).1,
    convex_iInter fun i => (halfspace_closed_convex (hH i)).2⟩

/-- The easy half of `cpwl`: a polyhedral subdivision is in particular a
subdivision into closed convex pieces. -/
theorem ref_cpwl_subset (n : ℕ) : Ref.CPWL n ⊆ Agent095.CPWL n := by
  rintro f ⟨hcont, m, P, g, hP, hg, hcov, hagree⟩
  simp only [Ref.IsAffine] at hg
  choose a b hab using hg
  refine ⟨hcont, m, a, b, P, hcov, fun j => (polyhedron_closed_convex (hP j)).1,
    fun j => (polyhedron_closed_convex (hP j)).2, fun j x hx => ?_⟩
  rw [hagree j x hx, hab j x]

/-! ### The network classes agree -/

/-- Every output coordinate of an `Agent095` network with `k` hidden layers is a
`Ref` network with `k` hidden layers. -/
private lemma hidden_to_ref {k n m : ℕ} {g : (Fin n → ℝ) → (Fin m → ℝ)}
    (h : Agent095.HiddenLayers k g) : ∀ i, Ref.ComputedBy n k (fun x => g x i) := by
  induction h with
  | base T =>
      intro i
      refine ⟨⟨Matrix.of fun _ j => T.A i j, fun _ => T.c i⟩, fun x => ?_⟩
      first
        | rfl
        | simp [Ref.Aff.eval, Agent095.Affine.eval, Matrix.mulVec, Matrix.of_apply]
  | step k' T G hG ih =>
      intro i
      refine ⟨_, ⟨T.A, T.c⟩, fun y => G y i, ih i, fun x => ?_⟩
      first
        | rfl
        | simp [Ref.Aff.eval, Agent095.Affine.eval, Ref.reluVec, Ref.relu,
            Agent095.reluVec, Agent095.relu]

/-- Conversely, a `Ref` network with `k` hidden layers is an `Agent095` one. -/
private lemma ref_to_computed : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Ref.ComputedBy n k f → Agent095.ComputedByReLUNetwork n k f := by
  intro k
  induction k with
  | zero =>
      intro n f hf
      obtain ⟨T, hT⟩ := hf
      exact ⟨Agent095.Affine.eval ⟨T.M, T.c⟩, Agent095.HiddenLayers.base _, hT⟩
  | succ k ih =>
      intro n f hf
      obtain ⟨m, T, g, hg, hfg⟩ := hf
      obtain ⟨G, hG, hgG⟩ := ih m g hg
      have hrelu : ∀ x : Fin n → ℝ, Ref.reluVec (T.eval x)
          = Agent095.reluVec ((⟨T.M, T.c⟩ : Agent095.Affine n m).eval x) := by
        intro x
        first
          | rfl
          | (funext j
             simp [Ref.reluVec, Ref.relu, Agent095.reluVec, Agent095.relu,
               Ref.Aff.eval, Agent095.Affine.eval])
      refine ⟨_, Agent095.HiddenLayers.step k (⟨T.M, T.c⟩ : Agent095.Affine n m) G hG,
        fun x => ?_⟩
      rw [hfg x, hrelu x, hgG]

/-! ### The four obligations -/

/-- Not proved: `Agent095.CPWL ⊆ Ref.CPWL` requires upgrading an arbitrary finite
closed-convex subdivision to a polyhedral one, which is a real theorem (the
inclusion `ref_cpwl_subset` above is the half that is elementary). -/
theorem cpwl (n : ℕ) : Agent095.CPWL n = Ref.CPWL n := sorry

theorem relun (n k : ℕ) : Agent095.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent095.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hjk, G, hG, hf⟩
    refine ⟨j, hjk, ?_⟩
    have hfe : f = fun x => G x 0 := funext hf
    rw [hfe]
    exact hidden_to_ref hG 0
  · rintro ⟨j, hjk, hj⟩
    exact ⟨j, hjk, ref_to_computed j n f hj⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent095.depthBound n = Ref.depthBound n := by
  have h : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  unfold Agent095.depthBound Ref.depthBound
  rw [h]

/-- Not proved: with `relun` and `depth` in hand this reduces to the two `CPWL`
notions agreeing, i.e. exactly the missing half of `cpwl`; routing it through the
`sorry`-ed `theorem2` on either side would prove nothing. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent095.CPWL n = Agent095.ReLUn n (Agent095.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_095

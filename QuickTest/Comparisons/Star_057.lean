import QuickTest.Formalizations.Thm2_057
import QuickTest.Reference

namespace Star_057

/-!
`Agent057` is the *polyhedral subdivision* family: its `CPWL` is the honest
"continuous + finite polyhedral cover + affine on each piece" condition, exactly
like `Ref.CPWL`.  The only differences are bookkeeping:

* pieces/halfspaces are indexed by an arbitrary `Fintype` rather than `Fin m`;
* affine data is packaged as bundled `→ₗ[ℝ]` / `→ᵃ[ℝ]` maps rather than as
  explicit coefficient vectors.

Both are dictionary translations, so all four obligations are provable.
-/

/-! ### Dictionary between coefficient vectors and bundled maps -/

/-- The linear functional `x ↦ ∑ i, a i * x i`. -/
noncomputable def linOfCoef {n : ℕ} (a : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, a i * x i
  map_add' u v := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.mul_sum, mul_comm, mul_left_comm]

@[simp] lemma linOfCoef_apply {n : ℕ} (a x : Fin n → ℝ) :
    linOfCoef a x = ∑ i, a i * x i := rfl

/-- The affine functional `x ↦ (∑ i, a i * x i) + b`. -/
noncomputable def affOfCoef {n : ℕ} (a : Fin n → ℝ) (b : ℝ) : (Fin n → ℝ) →ᵃ[ℝ] ℝ where
  toFun x := (∑ i, a i * x i) + b
  linear := linOfCoef a
  map_vadd' p v := by
    simp only [vadd_eq_add, Pi.add_apply, linOfCoef_apply, mul_add, Finset.sum_add_distrib]
    ring

@[simp] lemma affOfCoef_apply {n : ℕ} (a : Fin n → ℝ) (b : ℝ) (x : Fin n → ℝ) :
    affOfCoef a b x = (∑ i, a i * x i) + b := rfl

/-- Every bundled linear functional on `ℝⁿ` has a coefficient vector. -/
private lemma linear_coef {n : ℕ} (L : (Fin n → ℝ) →ₗ[ℝ] ℝ) :
    ∃ c : Fin n → ℝ, ∀ x, L x = ∑ j, c j * x j := by
  refine ⟨fun j => L (fun i => if j = i then 1 else 0), fun x => ?_⟩
  rw [LinearMap.pi_apply_eq_sum_univ L x]
  exact Finset.sum_congr rfl fun j _ => by rw [smul_eq_mul, mul_comm]

/-- Every bundled affine functional on `ℝⁿ` is `Ref.IsAffine`. -/
private lemma isAffine_of_affineMap {n : ℕ} (A : (Fin n → ℝ) →ᵃ[ℝ] ℝ) :
    Ref.IsAffine (fun x => A x) := by
  obtain ⟨c, hc⟩ := linear_coef A.linear
  refine ⟨c, A 0, fun x => ?_⟩
  have h : A x = A.linear x + A 0 := by simpa using A.map_vadd 0 x
  show A x = (∑ i, c i * x i) + A 0
  rw [h, hc x]

/-! ### Polyhedra -/

private lemma ref_isPolyhedron {n : ℕ} {S : Set (Fin n → ℝ)}
    (h : Agent057.IsPolyhedron n S) : Ref.IsPolyhedron n S := by
  obtain ⟨ι, hι, a, b, hS⟩ := h
  haveI := hι
  obtain ⟨e⟩ : Nonempty (Fin (Fintype.card ι) ≃ ι) := ⟨(Fintype.equivFin ι).symm⟩
  refine ⟨Fintype.card ι, fun j => {x | a (e j) x ≤ b (e j)}, fun j => ?_, ?_⟩
  · obtain ⟨c, hc⟩ := linear_coef (a (e j))
    exact ⟨c, b (e j), by ext x; simp only [Set.mem_setOf_eq, hc]⟩
  · rw [hS]
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact ⟨fun hx j => hx (e j), fun hx i => by simpa using hx (e.symm i)⟩

private lemma agent_isPolyhedron {n : ℕ} {S : Set (Fin n → ℝ)}
    (h : Ref.IsPolyhedron n S) : Agent057.IsPolyhedron n S := by
  obtain ⟨m, H, hH, hS⟩ := h
  choose a b hab using hH
  refine ⟨Fin m, inferInstance, fun i => linOfCoef (a i), b, ?_⟩
  rw [hS]
  ext x
  simp only [Set.mem_iInter, hab, Set.mem_setOf_eq, linOfCoef_apply]

/-! ### The obligations -/

/-- Both files define `CPWL` as continuity plus a finite polyhedral cover with
affine agreement; only the indexing and the packaging of the affine data differ. -/
theorem cpwl (n : ℕ) : Agent057.CPWL n = Ref.CPWL n := by
  ext f
  constructor
  · rintro ⟨hcont, ι, hι, S, A, hpoly, hcover, hagree⟩
    haveI := hι
    obtain ⟨e⟩ : Nonempty (Fin (Fintype.card ι) ≃ ι) := ⟨(Fintype.equivFin ι).symm⟩
    refine ⟨hcont, Fintype.card ι, fun j => S (e j), fun j x => A (e j) x,
      fun j => ref_isPolyhedron (hpoly (e j)), fun j => isAffine_of_affineMap (A (e j)), ?_,
      fun j x hx => hagree (e j) x hx⟩
    ext x
    have hx : x ∈ ⋃ i, S i := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨e.symm i, by simpa using hi⟩
  · rintro ⟨hcont, m, P, g, hpoly, haff, hcover, hagree⟩
    choose a b hab using haff
    refine ⟨hcont, Fin m, inferInstance, P, fun i => affOfCoef (a i) (b i),
      fun i => agent_isPolyhedron (hpoly i), hcover, fun i x hx => ?_⟩
    exact (hagree i x hx).trans ((hab i x).trans (affOfCoef_apply (a i) (b i) x).symm)

/-- Each coordinate of a network computed by `Agent057.ComputesReLU` is computed
by a `Ref.ComputedBy` network of the same depth. -/
private lemma computedBy_coord {n m k : ℕ} {F : (Fin n → ℝ) → (Fin m → ℝ)}
    (h : Agent057.ComputesReLU n m k F) : ∀ i : Fin m, Ref.ComputedBy n k (fun x => F x i) := by
  induction h with
  | base T => exact fun i => ⟨⟨Matrix.of fun _ j => T.A i j, fun _ => T.c i⟩, fun x => rfl⟩
  | step T g _ ih => exact fun i => ⟨_, ⟨T.A, T.c⟩, fun y => g y i, ih i, fun x => rfl⟩

/-- Conversely, a `Ref.ComputedBy` network is a one-output `Agent057` network. -/
private lemma computes_of_computedBy : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Ref.ComputedBy n k f → Agent057.ComputesReLU n 1 k (fun x _ => f x) := by
  intro k
  induction k with
  | zero =>
      intro n f hf
      obtain ⟨T, hT⟩ := hf
      have h : (fun (x : Fin n → ℝ) (_ : Fin 1) => f x) = (⟨T.M, T.c⟩ : Agent057.AffMap n 1).eval := by
        funext x i
        have hi : i = 0 := Subsingleton.elim i 0
        subst hi
        exact hT x
      rw [h]
      exact Agent057.ComputesReLU.base _
  | succ k ih =>
      intro n f hf
      obtain ⟨p, T, g, hg, hfx⟩ := hf
      have h : (fun (x : Fin n → ℝ) (_ : Fin 1) => f x)
          = (fun (y : Fin p → ℝ) (_ : Fin 1) => g y) ∘ Agent057.reluVec ∘
              (⟨T.M, T.c⟩ : Agent057.AffMap n p).eval := by
        funext x i
        exact hfx x
      rw [h]
      exact Agent057.ComputesReLU.step _ _ (ih p g hg)

/-- Both files read `ReLUn n k` as "at most `k` hidden layers"; the encodings
(inductive with `Fin 1`-valued output vs. recursion with scalar output) agree. -/
theorem relun (n k : ℕ) : Agent057.ReLUn n k = Ref.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, computedBy_coord h 0⟩
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, computes_of_computedBy j n f h⟩

/-- The two depth bounds are literally the same expression. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent057.depthBound n = Ref.depthBound n := rfl

theorem statement :
    (∀ n, 3 ≤ n → Agent057.CPWL n = Agent057.ReLUn n (Agent057.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
  have key : ∀ n, 3 ≤ n →
      ((Agent057.CPWL n = Agent057.ReLUn n (Agent057.depthBound n)) ↔
        (Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n))) := by
    intro n hn
    rw [cpwl n, depth n hn, relun n (Ref.depthBound n)]
  exact ⟨fun h n hn => (key n hn).1 (h n hn), fun h n hn => (key n hn).2 (h n hn)⟩

end Star_057

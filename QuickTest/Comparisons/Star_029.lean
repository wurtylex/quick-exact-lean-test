import QuickTest.Formalizations.Thm2_029
import QuickTest.Reference

namespace Star_029

/-!
# Star comparison: `Agent029` vs `Ref`

`Agent029` is a member of the *polyhedral subdivision* family: its `CPWL n` is
continuity plus a finite cover of `ℝⁿ` by polyhedra on each of which `f` agrees
with an affine functional — exactly the reference condition, up to two cosmetic
repackagings:

* a polyhedron is written as one simultaneous system `{x | ∀ i, ⟪aᵢ, x⟫ ≤ bᵢ}`
  rather than as an intersection `⋂ i, Hᵢ` of halfspaces, and
* the affine pieces are existentially quantified *per piece* (`IsAffineOn f (P i)`)
  rather than supplied as one global family `g : Fin m → ((Fin n → ℝ) → ℝ)`.

Both gaps are closed by `Classical.choice` (`choose`), so `cpwl` is provable.
`depthBound` is literally the same expression, so `depth` is `rfl`.
`ReLUn` is the "exactly `k` hidden layers" reading (and with a different,
`ℕ`-indexed internal encoding of the layer values), so `relun` is genuinely hard.
-/

/-- The two spellings of "polyhedron" agree: a simultaneous finite system of
affine inequalities is the same set as a finite intersection of halfspaces. -/
private lemma poly_iff {n : ℕ} (S : Set (Fin n → ℝ)) :
    Agent029.IsPolyhedron S ↔ Ref.IsPolyhedron n S := by
  constructor
  · rintro ⟨m, a, b, rfl⟩
    refine ⟨m, fun i => {x | (∑ j, a i j * x j) ≤ b i}, fun i => ⟨a i, b i, rfl⟩, ?_⟩
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
  · rintro ⟨m, H, hH, rfl⟩
    have hH' : ∀ i, ∃ (a : Fin n → ℝ) (b : ℝ), H i = {x | (∑ j, a j * x j) ≤ b} := hH
    choose a b hab using hH'
    refine ⟨m, a, b, ?_⟩
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro h i
      have hi := h i
      rw [hab i] at hi
      exact hi
    · intro h i
      rw [hab i]
      exact h i

/-- The two `CPWL` definitions denote the same set of functions. -/
theorem cpwl (n : ℕ) : Agent029.CPWL n = Ref.CPWL n := by
  ext f
  show (Continuous f ∧ ∃ (m : ℕ) (P : Fin m → Set (Fin n → ℝ)),
        (∀ i, Agent029.IsPolyhedron (P i)) ∧ (⋃ i, P i) = Set.univ ∧
        (∀ i, Agent029.IsAffineOn f (P i))) ↔
      (Continuous f ∧ ∃ (m : ℕ) (P : Fin m → Set (Fin n → ℝ))
          (g : Fin m → ((Fin n → ℝ) → ℝ)),
        (∀ i, Ref.IsPolyhedron n (P i)) ∧ (∀ i, Ref.IsAffine (g i)) ∧
          (⋃ i, P i) = Set.univ ∧ ∀ i, ∀ x ∈ P i, f x = g i x)
  constructor
  · rintro ⟨hc, m, P, hP, hcov, haff⟩
    have haff' : ∀ i, ∃ (w : Fin n → ℝ) (c : ℝ), ∀ x ∈ P i,
        f x = (∑ j, w j * x j) + c := haff
    choose w c hwc using haff'
    exact ⟨hc, m, P, fun i x => (∑ j, w i j * x j) + c i,
      fun i => (poly_iff _).1 (hP i), fun i => ⟨w i, c i, fun _ => rfl⟩, hcov, hwc⟩
  · rintro ⟨hc, m, P, g, hP, hg, hcov, hfg⟩
    refine ⟨hc, m, P, fun i => (poly_iff _).2 (hP i), hcov, ?_⟩
    intro i
    obtain ⟨a, b, hab⟩ := hg i
    show ∃ (w : Fin n → ℝ) (c : ℝ), ∀ x ∈ P i, f x = (∑ j, w j * x j) + c
    exact ⟨a, b, fun x hx => by rw [hfg i x hx, hab x]⟩

/-- Not proved: `Agent029.ReLUn` asks for **exactly** `k` hidden layers (with an
`ℕ`-indexed internal encoding of the layer values), while `Ref.ReLUn` asks for
**at most** `k`.  The two sets do coincide, but only via the padding identity
`x = relu x - relu (-x)`, which is a real theorem and out of budget here. -/
theorem relun (n k : ℕ) : Agent029.ReLUn n k = Ref.ReLUn n k := sorry

/-- Both files define the depth bound by the same expression
`⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`, so this is definitional. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent029.depthBound n = Ref.depthBound n := rfl

/-- Not proved: with `cpwl` and `depth` in hand this reduces exactly to the
`ReLUn` comparison at `k = depthBound n`, i.e. to `relun`, which is `sorry`-ed
above.  Routing it through either file's `theorem2` would prove nothing, since
both are themselves `sorry`-ed. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent029.CPWL n = Agent029.ReLUn n (Agent029.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_029

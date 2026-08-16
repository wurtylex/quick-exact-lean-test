/-!
# Star comparison: `Agent042` vs `Ref`

`Agent042` is in the *polyhedral subdivision* family: its `CPWL` is the honest
condition "continuous, plus a finite polyhedral cover of `ℝⁿ` on each piece of
which `f` is affine", exactly like the reference.  The only differences are
presentational:

* a polyhedron is packaged as the solution set `{x | ∀ j, ⟪a j, x⟫ ≤ b j}` of a
  finite inequality system, rather than as a finite intersection `⋂ j, H j` of
  halfspaces — the same sets, see `poly_iff`;
* the affine piece is carried as data `(A i, c i)` rather than as a function
  `g i` together with a proof `Ref.IsAffine (g i)`.

So `cpwl` is genuinely true and is proved below.  `depthBound` is literally the
same definition on both sides, so `depth` is `rfl`.  `relun` is the usual
exactly-`k` versus at-most-`k` mismatch and is left as an honest `sorry`.
-/

namespace Star_042

/-- The two polyhedron notions coincide: a finite system of affine inequalities
is exactly a finite intersection of closed affine halfspaces. -/
private lemma poly_iff {n : ℕ} (P : Set (Fin n → ℝ)) :
    Agent042.IsPolyhedron P ↔ Ref.IsPolyhedron n P := by
  constructor
  · rintro ⟨m, a, b, rfl⟩
    refine ⟨m, fun j => {x | (∑ i, a j i * x i) ≤ b j}, fun j => ⟨a j, b j, rfl⟩, ?_⟩
    ext x
    simp [Set.mem_iInter]
  · rintro ⟨m, H, hH, rfl⟩
    choose a b hab using hH
    refine ⟨m, a, b, ?_⟩
    ext x
    simp [Set.mem_iInter, hab]

/-- The `CPWL` classes agree: both are "continuous + finite polyhedral cover with
an affine piece on each cell". -/
theorem cpwl (n : ℕ) : Agent042.CPWL n = Ref.CPWL n := by
  ext f
  simp only [Agent042.CPWL, Ref.CPWL, Ref.IsCPWL, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hcont, m, P, A, c, hP, hcov, heq⟩
    exact ⟨hcont, m, P, fun i x => (∑ k, A i k * x k) + c i,
      fun i => (poly_iff _).1 (hP i), fun i => ⟨A i, c i, fun _ => rfl⟩, hcov, heq⟩
  · rintro ⟨hcont, m, P, g, hP, hg, hcov, heq⟩
    choose a b hab using hg
    refine ⟨hcont, m, P, a, b, fun i => (poly_iff _).2 (hP i), hcov, ?_⟩
    intro i x hx
    rw [heq i x hx, hab i x]

/-- Honest `sorry`: `Agent042.ReLUn n k` asks for **exactly** `k` hidden layers
(a list of `k + 1` affine layers, run through a dimension-tagged forward pass),
while `Ref.ReLUn n k` asks for **at most** `k`.  The two sets are equal, but only
via the padding identity `x = relu x - relu (-x)`, which is a real theorem about
ReLU networks and not a definitional unfolding. -/
theorem relun (n k : ℕ) : Agent042.ReLUn n k = Ref.ReLUn n k := sorry

/-- Both files define the depth bound by the same expression
`⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`, so this is definitional. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent042.depthBound n = Ref.depthBound n := rfl

/-- The whole statement comparison is reducible to the `ReLUn` comparison: the
`CPWL` sides and the depth bounds already match. -/
private lemma statement_of_relun
    (h : ∀ n, 3 ≤ n → Agent042.ReLUn n (Agent042.depthBound n) = Ref.ReLUn n (Ref.depthBound n)) :
    (∀ n, 3 ≤ n → Agent042.CPWL n = Agent042.ReLUn n (Agent042.depthBound n)) ↔
      (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
  constructor
  · intro H n hn
    rw [← cpwl n, ← h n hn]
    exact H n hn
  · intro H n hn
    rw [cpwl n, h n hn]
    exact H n hn

/-- Honest `sorry`: by `statement_of_relun` this needs exactly the `ReLUn`
comparison `relun`, which is itself unproved (exactly-`k` versus at-most-`k`). -/
theorem statement :
    (∀ n, 3 ≤ n → Agent042.CPWL n = Agent042.ReLUn n (Agent042.depthBound n)) ↔
      (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_042

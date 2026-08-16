namespace Star_014

/-!
# Comparison of `Agent014` against `Ref`

`Agent014` is in the *polyhedral subdivision* family: its `CPWL` is continuity plus a
finite family of pieces, each a genuine polyhedron (finite intersection of half-spaces
`⟨normal j, x⟩ ≤ bound j`) carrying an affine function, the regions covering `ℝⁿ`.
This is the same condition as `Ref.CPWL`; the only differences are bookkeeping:

* the index set is an arbitrary `Fintype` rather than `Fin m`;
* a piece bundles its region and its affine map in a structure `PWLPiece`;
* the affine map is a `1 × n` matrix evaluated at row `0` rather than `∑ aᵢ xᵢ + b`;
* the region is written `{x | ∀ j, ⟨normal j, x⟩ ≤ bound j}` rather than `⋂ j, Hⱼ`.

All four are translated below, so `cpwl` is *proved*.

`depthBound` is literally the same expression, so `depth` is `rfl`.

`ReLUn` differs genuinely: `Agent014` says **exactly** `k` hidden layers, `Ref` says
**at most** `k`.  These sets are equal, but only via the padding identity
`x = relu x - relu (-x)`, which is a real theorem; `relun` is left as an honest `sorry`.
-/

/-- Evaluating a `1 × n` affine map at row `0` is the affine functional
`x ↦ ∑ k, A 0 k * x k + c 0`. -/
private lemma agent_eval_zero {n : ℕ} (T : Agent014.AffineT n 1) (x : Fin n → ℝ) :
    T.eval x 0 = (∑ k, T.A 0 k * x k) + T.c 0 := rfl

/-- The two `CPWL` definitions agree: both are "continuous + finite polyhedral cover on
each piece of which `f` is affine". -/
theorem cpwl (n : ℕ) : Agent014.CPWL n = Ref.CPWL n := by
  ext f
  simp only [Agent014.CPWL, Ref.CPWL, Set.mem_setOf_eq, Agent014.IsCPWL, Ref.IsCPWL]
  constructor
  · -- `Agent014 → Ref`: re-index the `Fintype` by `Fin (card ι)` and unbundle the pieces.
    rintro ⟨hcont, ι, hι, pieces, hcov, hagree⟩
    letI := hι
    obtain ⟨e⟩ : Nonempty (ι ≃ Fin (Fintype.card ι)) := ⟨Fintype.equivFin ι⟩
    refine ⟨hcont, Fintype.card ι, fun i => (pieces (e.symm i)).region,
      fun i x => (pieces (e.symm i)).aff.eval x 0, ?_, ?_, ?_, ?_⟩
    · -- each region is a finite intersection of half-spaces
      intro i
      refine ⟨(pieces (e.symm i)).numConstraints,
        fun j => {x | (∑ k, (pieces (e.symm i)).normal j k * x k) ≤
          (pieces (e.symm i)).bound j},
        fun j => ⟨(pieces (e.symm i)).normal j, (pieces (e.symm i)).bound j, rfl⟩, ?_⟩
      ext x
      simp [Agent014.PWLPiece.region, Set.mem_iInter]
    · -- each piece's map is an affine functional
      intro i
      exact ⟨fun k => (pieces (e.symm i)).aff.A 0 k, (pieces (e.symm i)).aff.c 0,
        fun x => agent_eval_zero _ x⟩
    · -- the re-indexed regions still cover `ℝⁿ`
      rw [Set.eq_univ_iff_forall]
      intro x
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (Set.eq_univ_iff_forall.1 hcov x)
      exact Set.mem_iUnion.2 ⟨e i, by simpa using hi⟩
    · intro i x hx
      exact hagree _ x hx
  · -- `Ref → Agent014`: bundle the polyhedra and the affine functionals into `PWLPiece`s.
    rintro ⟨hcont, m, P, g, hP, hg, hcov, hagree⟩
    choose mc H hH hPeq using hP
    choose a b hab using hH
    choose ga gb hgab using hg
    have hreg : ∀ i, {x : Fin n → ℝ | ∀ j, (∑ k, a i j k * x k) ≤ b i j} = P i := by
      intro i
      rw [hPeq i]
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter, hab]
    refine ⟨hcont, Fin m, inferInstance,
      fun i => ⟨⟨Matrix.of fun _ k => ga i k, fun _ => gb i⟩, mc i, a i, b i⟩, ?_, ?_⟩
    · rw [← hcov]
      exact Set.iUnion_congr hreg
    · intro i x hx
      have hxP : x ∈ P i := by rw [← hreg i]; exact hx
      rw [hagree i x hxP, hgab i x, agent_eval_zero]
      simp

/-- `Agent014.ReLUn n k` is "**exactly** `k` hidden layers"; `Ref.ReLUn n k` is "**at most**
`k`".  The two sets coincide, but only through the padding identity
`x = relu x - relu (-x)`, which is a genuine theorem about ReLU networks and is not
available here. -/
theorem relun (n k : ℕ) : Agent014.ReLUn n k = Ref.ReLUn n k := by
  sorry -- honest: needs layer padding `x = relu x - relu (-x)`, a real theorem.

/-- Both files define the depth bound by the same expression `⌈logb 3 (n-1)⌉₊ + 1`. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent014.depthBound n = Ref.depthBound n := rfl

/-- The two statements of Theorem 2 are equivalent.  This uses `cpwl` and `depth` (both
proved above) together with `relun` (still a `sorry`), so it inherits that dependency. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent014.CPWL n = Agent014.ReLUn n (Agent014.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
  have key : ∀ n, 3 ≤ n →
      (Agent014.CPWL n = Agent014.ReLUn n (Agent014.depthBound n) ↔
        Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
    intro n hn
    rw [cpwl n, depth n hn, relun n (Ref.depthBound n)]
  exact ⟨fun h n hn => (key n hn).1 (h n hn), fun h n hn => (key n hn).2 (h n hn)⟩

end Star_014

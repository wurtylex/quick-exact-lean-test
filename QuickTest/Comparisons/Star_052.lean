import QuickTest.Formalizations.Thm2_052
import QuickTest.Reference

/-!
# Star comparison: `Agent052` vs `Ref`

`Agent052` is in the **polyhedral subdivision** family.  Its `CPWL n` is the
same honest condition as `Ref.CPWL n`: continuous, plus a finite family of
closed polyhedra covering `ℝⁿ` on each of which `f` agrees with an affine
function.  The only difference is bookkeeping — `Agent052` carries a halfspace
as *data* (`structure Halfspace` with fields `a`, `b`) and an affine piece as a
`1 × n` `AffMap`, where `Ref` carries sets plus the predicates `IsHalfspace`
/ `IsAffine`.  That is a genuine equality of sets, and `cpwl` is proved below
(the reverse direction needs `choose` to extract the halfspace and affine
coefficient data from `Ref`'s existentials).

`depthBound` is character-for-character the same definition, so `depth` is
`rfl`.

The real gap is `ReLUn`.  Both files quantify "at most `k`" on the outside, but
the inner predicates recurse from opposite ends: `Ref.ComputedBy` peels the
**first** affine map (`f x = g (reluVec (T.eval x))`), while
`Agent052.Represents` is stated via `netEval`, which peels the **last** one and
threads a global width function `w : ℕ → ℕ` together with two casts along
`w 0 = n` and `w (k+1) = 1`.  Converting between the two is a real
reassociation induction over dependent widths, not a definitional unfolding, so
`relun` is left as an honest `sorry`, and with it `statement`.
-/

namespace Star_052

/-! ### CPWL -/

/-- A polyhedron of `Agent052` (an intersection of the sets cut out by a finite
family of `Halfspace` records) is a `Ref.IsPolyhedron`. -/
private lemma isPolyhedron_polyhedron {n m : ℕ} (H : Fin m → Agent052.Halfspace n) :
    Ref.IsPolyhedron n (Agent052.Polyhedron H) :=
  ⟨m, fun j => (H j).set, fun j => ⟨(H j).a, (H j).b, rfl⟩, rfl⟩

/-- Evaluating a `1 × n` `AffMap` at output coordinate `0` is an affine
functional in `Ref`'s sense. -/
private lemma isAffine_affMap {n : ℕ} (T : Agent052.AffMap n 1) :
    Ref.IsAffine (fun x => T.eval x 0) :=
  ⟨fun j => T.A 0 j, T.c 0, fun _ => rfl⟩

/-- The two `CPWL` predicates agree: `Agent052` stores the halfspaces and the
affine pieces as raw data, `Ref` stores sets and functions together with
`IsHalfspace` / `IsAffine` proofs. -/
private lemma cpwl_iff (n : ℕ) (f : (Fin n → ℝ) → ℝ) :
    f ∈ Agent052.CPWL n ↔ f ∈ Ref.CPWL n := by
  simp only [Agent052.CPWL, Ref.CPWL, Ref.IsCPWL, Set.mem_setOf_eq]
  constructor
  · -- `Agent052 → Ref`: forget the data, keep the induced sets and functions.
    rintro ⟨hc, m, mi, H, g, hcov, hf⟩
    exact ⟨hc, m, fun i => Agent052.Polyhedron (H i), fun i x => (g i).eval x 0,
      fun i => isPolyhedron_polyhedron (H i), fun i => isAffine_affMap (g i), hcov, hf⟩
  · -- `Ref → Agent052`: choose halfspace and affine coefficients.
    rintro ⟨hc, m, P, g, hP, hg, hcov, hf⟩
    simp only [Ref.IsPolyhedron] at hP
    choose mi HH hHS hPeq using hP
    simp only [Ref.IsHalfspace] at hHS
    choose a b hab using hHS
    simp only [Ref.IsAffine] at hg
    choose ga gb hgab using hg
    -- the chosen halfspace records cut out exactly the sets `HH i j`
    have hset : ∀ (i : Fin m) (j : Fin (mi i)),
        (Agent052.Halfspace.set ⟨a i j, b i j⟩ : Set (Fin n → ℝ)) = HH i j :=
      fun i j => (hab i j).symm
    have hpe : ∀ i : Fin m,
        Agent052.Polyhedron (fun j => (⟨a i j, b i j⟩ : Agent052.Halfspace n)) = P i := by
      intro i
      ext x
      rw [hPeq i]
      simp only [Agent052.Polyhedron, Set.mem_iInter, hset i]
    refine ⟨hc, m, mi, fun i j => ⟨a i j, b i j⟩,
      fun i => ⟨Matrix.of fun _ k => ga i k, fun _ => gb i⟩, ?_, ?_⟩
    · exact (Set.iUnion_congr hpe).trans hcov
    · intro i x hx
      have hx' : x ∈ P i := by rw [← hpe i]; exact hx
      exact (hf i x hx').trans (hgab i x)

theorem cpwl (n : ℕ) : Agent052.CPWL n = Ref.CPWL n := by
  ext f
  exact cpwl_iff n f

/-! ### ReLUn -/

/-- The two `ReLUn` sets are in fact equal — both are "at most `k` hidden
layers" over the same notion of ReLU network — but the inner predicates are
built by opposite recursions: `Ref.ComputedBy` strips the first affine map,
`Agent052.Represents` is defined through `netEval`, which strips the last one
and carries a width function `w : ℕ → ℕ` plus casts along `w 0 = n` and
`w (k+1) = 1`.  Relating them is a reassociation induction on the layer chain
with dependent width coercions, i.e. a real theorem; it is left as an honest
`sorry`. -/
theorem relun (n k : ℕ) : Agent052.ReLUn n k = Ref.ReLUn n k := by
  -- Missing lemma, in both directions:
  -- `Agent052.netEval w layers (k+1) x`-form networks ↔ `Ref.ComputedBy n k`,
  -- by induction reassociating the composition from the output end to the
  -- input end (and transporting along `w 0 = n`, `w (k+1) = 1`).
  sorry

/-! ### Depth bound -/

/-- Both files write `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`, so this is `rfl`. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent052.depthBound n = Ref.depthBound n := rfl

/-! ### The statement -/

/-- `cpwl` and `depth` line up both ends of the two equalities, so the iff is
equivalent to `Agent052.ReLUn n (depthBound n) = Ref.ReLUn n (depthBound n)`
for `n ≥ 3` — exactly the `relun` gap.  Routing through the `sorry`-ed `relun`
(or through either file's `sorry`-ed `theorem2`, which the spec forbids) would
prove nothing, so this is an honest `sorry`. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent052.CPWL n = Agent052.ReLUn n (Agent052.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
  sorry

end Star_052

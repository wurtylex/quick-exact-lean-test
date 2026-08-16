import QuickTest.Formalizations.Thm2_001
import QuickTest.Reference

/-!
# Star comparison: `Agent001` vs `Ref`

`Agent001` is in the "polyhedral subdivision" family: its `IsCPWL` is the same
honest condition as `Ref.IsCPWL`, except that the affine pieces are carried as
raw data `(a : Fin m → Fin n → ℝ, b : Fin m → ℝ)` instead of as functions
`g : Fin m → ((Fin n → ℝ) → ℝ)` together with a proof `IsAffine (g i)`.  That
is a genuine equality of sets, and `cpwl` is proved below.

The only real gap is `ReLUn`: `Agent001` says **exactly** `k` hidden layers,
`Ref` says **at most** `k`.  The easy inclusion (`exactly ⊆ at most`) is proved
as `relun_subset`; the converse needs the padding identity
`x = relu x - relu (-x)`, which is a theorem, not a definitional unfolding.
-/

namespace Star_001

/-! ### Shared vocabulary

`IsHalfspace` and `IsPolyhedron` are literally the same definition in both
files, so they are definitionally equal. -/

private lemma halfspace_iff (n : ℕ) (S : Set (Fin n → ℝ)) :
    Agent001.IsHalfspace n S ↔ Ref.IsHalfspace n S := Iff.rfl

private lemma polyhedron_iff (n : ℕ) (S : Set (Fin n → ℝ)) :
    Agent001.IsPolyhedron n S ↔ Ref.IsPolyhedron n S := Iff.rfl

/-! ### CPWL -/

/-- The two `IsCPWL` predicates agree: `Agent001` inlines the affine pieces as
coefficient data, `Ref` packages them as functions plus an `IsAffine` proof. -/
private lemma isCPWL_iff (n : ℕ) (f : (Fin n → ℝ) → ℝ) :
    Agent001.IsCPWL n f ↔ Ref.IsCPWL n f := by
  constructor
  · rintro ⟨hc, m, P, a, b, hP, hcov, hf⟩
    refine ⟨hc, m, P, fun i x => (∑ j, a i j * x j) + b i, ?_, ?_, hcov, hf⟩
    · intro i; exact (polyhedron_iff n _).1 (hP i)
    · intro i; exact ⟨a i, b i, fun _ => rfl⟩
  · rintro ⟨hc, m, P, g, hP, hg, hcov, hf⟩
    simp only [Ref.IsAffine] at hg
    choose a b hab using hg
    refine ⟨hc, m, P, a, b, ?_, hcov, ?_⟩
    · intro i; exact (polyhedron_iff n _).2 (hP i)
    · intro i x hx; exact (hf i x hx).trans (hab i x)

theorem cpwl (n : ℕ) : Agent001.CPWL n = Ref.CPWL n := by
  ext f
  exact isCPWL_iff n f

/-! ### ReLUn -/

/-- The base cases agree: a `1 × n` matrix plus a translation is the same thing
as a coefficient vector plus a constant. -/
private lemma computedBy_zero_iff {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    Ref.ComputedBy n 0 f ↔ ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x, f x = (∑ i, a i * x i) + b := by
  constructor
  · rintro ⟨T, hT⟩
    exact ⟨fun j => T.M 0 j, T.c 0, fun x => hT x⟩
  · rintro ⟨a, b, hab⟩
    exact ⟨⟨Matrix.of fun _ j => a j, fun _ => b⟩, fun x => hab x⟩

/-- `Agent001.IsReLUNet n k` (exactly `k` hidden layers) implies
`Ref.ComputedBy n k` (also exactly `k`); the two recursions are the same, only
the affine-map structure and the base case are packaged differently. -/
private lemma isReLUNet_to_computedBy (k : ℕ) : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent001.IsReLUNet n k f → Ref.ComputedBy n k f := by
  induction k with
  | zero => intro n f h; exact (computedBy_zero_iff f).2 h
  | succ k ih =>
      rintro n f ⟨m, T, g, hg, hx⟩
      exact ⟨m, ⟨T.A, T.c⟩, g, ih m g hg, fun x => hx x⟩

/-- The easy inclusion: "exactly `k` hidden layers" is a special case of
"at most `k` hidden layers". -/
theorem relun_subset (n k : ℕ) : Agent001.ReLUn n k ⊆ Ref.ReLUn n k :=
  fun _ hf => ⟨k, le_rfl, isReLUNet_to_computedBy k n _ hf⟩

/-- The two `ReLUn` sets are in fact equal, but the converse of `relun_subset`
needs the padding identity `x = relu x - relu (-x)` to promote a network with
`j < k` hidden layers to one with exactly `k`.  That is a real theorem about
ReLU networks (build `k - j` identity layers of width `2`), not a definitional
unfolding, so it is left as an honest `sorry`. -/
theorem relun (n k : ℕ) : Agent001.ReLUn n k = Ref.ReLUn n k := by
  apply Set.Subset.antisymm (relun_subset n k)
  -- Missing lemma: `Ref.ComputedBy n j f → j ≤ k → Agent001.IsReLUNet n k f`,
  -- i.e. layer padding via `x = relu x - relu (-x)`.
  sorry

/-! ### Depth bound -/

/-- `Agent001.depthBound` casts `n - 1` in `ℕ`, `Ref.depthBound` subtracts `1`
in `ℝ`; for `n ≥ 1` these agree. -/
private lemma cast_pred (n : ℕ) (hn : 1 ≤ n) : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
  rw [Nat.cast_sub hn, Nat.cast_one]

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent001.depthBound n = Ref.depthBound n := by
  unfold Agent001.depthBound Ref.depthBound
  rw [cast_pred n (by omega)]

/-! ### The statement -/

/-- Both sides of the iff say "CPWL_n equals the depth-bounded ReLU class".
`cpwl` and `depth` line up the two ends, so the iff is *equivalent* to
`Agent001.ReLUn n (depthBound n) = Ref.ReLUn n (depthBound n)` on the relevant
`n` — which is exactly the `relun` gap above.  Rather than route through the
`sorry`-ed `relun` (or through either file's `sorry`-ed `theorem2`, which the
spec forbids), this is left as an honest `sorry`: the missing ingredient is
again layer padding. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent001.CPWL n = Agent001.ReLUn n (Agent001.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
  sorry

end Star_001

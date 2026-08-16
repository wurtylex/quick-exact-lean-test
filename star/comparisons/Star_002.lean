/-!
# Star comparison: `Agent002` vs `Ref`

`Agent002` lands squarely in the *pointwise affine selection* family: its `IsCPWL`
asks for a finite family of affine maps such that **every point has a neighbourhood**
on which `f` agrees with one member.  On connected `ℝⁿ` that condition forces `f` to
be globally affine, so it is strictly stronger than the reference's polyhedral-cover
definition and `cpwl` is **false**; we prove `cpwl_ne`.

`depthBound` agrees on the nose (both are `⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1`), so
`depth` is `rfl`.

`ReLUn` is "exactly `k`" here versus "at most `k`" in the reference; these denote the
same set but only through the padding identity `x = relu x - relu (-x)`, which is a
genuine theorem.  Left as an honest `sorry`.
-/

namespace Star_002

/-! ### The separating witness `x ↦ max 0 (x 0)` on `ℝ¹` -/

/-- The one-dimensional ReLU, viewed as a function `ℝ¹ → ℝ`. -/
private noncomputable def fwit : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

private theorem fwit_continuous : Continuous fwit :=
  continuous_const.max (continuous_apply 0)

/-- The halfspace `{x | x 0 ≤ 0}`, written in the reference's normal form. -/
private def S0 : Set (Fin 1 → ℝ) := {x | (∑ i, (fun _ => (1 : ℝ)) i * x i) ≤ 0}

/-- The halfspace `{x | -x 0 ≤ 0}`, written in the reference's normal form. -/
private def S1 : Set (Fin 1 → ℝ) := {x | (∑ i, (fun _ => (-1 : ℝ)) i * x i) ≤ 0}

/-- A single halfspace is a polyhedron (`m = 1`, constant intersection). -/
private lemma halfspace_poly {n : ℕ} {S : Set (Fin n → ℝ)} (h : Ref.IsHalfspace n S) :
    Ref.IsPolyhedron n S :=
  ⟨1, fun _ => S, fun _ => h, (Set.iInter_const S).symm⟩

/-- `fwit` is CPWL in the reference sense: the two halfspaces `S0`, `S1` cover `ℝ¹`
and `fwit` agrees with `0` on the first and with `x ↦ x 0` on the second. -/
private theorem fwit_mem_ref : fwit ∈ Ref.CPWL 1 := by
  refine ⟨fwit_continuous, 2, ![S0, S1], ![fun _ => 0, fun x => x 0], ?_, ?_, ?_, ?_⟩
  · refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · exact halfspace_poly ⟨fun _ => 1, 0, rfl⟩
    · exact halfspace_poly ⟨fun _ => -1, 0, rfl⟩
  · refine Fin.forall_fin_two.mpr ⟨⟨fun _ => 0, 0, ?_⟩, ⟨fun _ => 1, 0, ?_⟩⟩
    · intro x; simp
    · intro x; simp
  · rw [Set.eq_univ_iff_forall]
    intro x
    rw [Set.mem_iUnion]
    rcases le_total (x 0) 0 with hx | hx
    · exact ⟨0, by simpa [S0] using hx⟩
    · exact ⟨1, by simpa [S1] using hx⟩
  · refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · intro x hx
      simp only [Matrix.cons_val_zero, S0, Set.mem_setOf_eq] at hx
      simp only [Fin.sum_univ_one, one_mul] at hx
      simpa [fwit] using max_eq_left hx
    · intro x hx
      simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, S1,
        Set.mem_setOf_eq, Fin.sum_univ_one, neg_mul, one_mul, neg_nonpos] at hx
      simpa [fwit] using max_eq_right hx

/-- `fwit` is *not* CPWL in `Agent002`'s sense: local agreement with a single affine
map at the kink `0` is impossible. -/
private theorem fwit_not_mem_agent : fwit ∉ Agent002.CPWL 1 := by
  rintro ⟨-, m, g, hg⟩
  obtain ⟨i, ε, hε, h⟩ := hg 0
  obtain ⟨a, b, key⟩ :
      ∃ a b : ℝ, ∀ t : ℝ, (g i).eval (fun _ => t) 0 = a * t + b :=
    ⟨(g i).A 0 0, (g i).c 0, by
      intro t
      simp [Agent002.Affine.eval, Matrix.mulVec, dotProduct, Fin.sum_univ_one]⟩
  -- On the whole `ε`-ball around `0`, `max 0 t` must equal the affine map `a * t + b`.
  have hval : ∀ t : ℝ, |t| < ε → max 0 t = a * t + b := by
    intro t ht
    have hy : dist (fun _ : Fin 1 => t) (0 : Fin 1 → ℝ) < ε := by
      rw [dist_pi_lt_iff hε]
      intro j
      simpa [Real.dist_eq] using ht
    have hthis := h _ hy
    rw [key] at hthis
    have hf : fwit (fun _ : Fin 1 => t) = max 0 t := rfl
    rwa [hf] at hthis
  obtain ⟨d, hd, hdε⟩ : ∃ d : ℝ, 0 < d ∧ d < ε := ⟨ε / 2, by linarith, by linarith⟩
  have e0 : b = 0 := by
    have h' := hval 0 (by simpa using hε)
    simp at h'
    linarith
  have epos : d = a * d + b := by
    have h' := hval d (by rw [abs_of_pos hd]; linarith)
    rwa [max_eq_right hd.le] at h'
  have eneg : (0 : ℝ) = a * (-d) + b := by
    have h' := hval (-d) (by rw [abs_of_neg (by linarith : -d < 0)]; linarith)
    rwa [max_eq_left (by linarith : -d ≤ 0)] at h'
  linarith

/-! ### The four obligations -/

/-- `Agent002.CPWL` is **strictly stronger** than `Ref.CPWL`: the neighbourhood-agreement
formulation excludes the one-dimensional ReLU, which the reference admits. -/
theorem cpwl_ne : ∃ n, Agent002.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun hEq => fwit_not_mem_agent ?_⟩
  rw [hEq]
  exact fwit_mem_ref

/-- `Agent002.ReLUn n k` is the "exactly `k` hidden layers" reading, `Ref.ReLUn n k` the
"at most `k`" reading.  The two sets do coincide, but only via the padding identity
`x = relu x - relu (-x)`, which is a real theorem about ReLU networks and is not
available here. -/
theorem relun (n k : ℕ) : Agent002.ReLUn n k = Ref.ReLUn n k := by
  sorry -- honest: needs `ReLUn n j ⊆ ReLUn n (j+1)` via `x = relu x - relu (-x)`.

/-- The depth bounds are literally the same expression, `⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1`
(`Nat.ceil` is exactly the `⌈·⌉₊` notation), so no bridge lemma is needed. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent002.depthBound n = Ref.depthBound n := rfl

/-- The two theorem statements are **not** equivalent.  `Agent002`'s side is false:
by the argument in `fwit_not_mem_agent` (which works verbatim in any dimension, using
the coordinate `x 0`) `Agent002.CPWL n` contains only globally affine functions, whereas
`Agent002.ReLUn n (depthBound n)` — with `depthBound n ≥ 1` — contains non-affine
functions.  The reference's side is Theorem 2 itself, which is true.  So the correct
shape is `statement_ne`, but establishing it requires *proving* `Ref.theorem2`, which is
`sorry`-ed in the reference and out of reach here; routing through `Ref.theorem2` would
prove nothing.  Hence an honest `sorry`. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent002.CPWL n = Agent002.ReLUn n (Agent002.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
  sorry -- honest: false, but refuting it is exactly `Ref.theorem2`, which is unproved.

end Star_002

namespace Bridge_026_027

/-!
## Summary of the comparison between `Agent026` and `Agent027`

* `depthBound` — both agents use the *literal same* expression
  `⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1`. **PROVED** (`rfl`-level equality).

* `CPWL` — Agent026 uses a genuine polyhedral-subdivision definition (family (a) in the
  spec): a finite family of polyhedra (finite intersections of affine half-spaces)
  covering all of `ℝⁿ`, with `f` agreeing with a fixed affine formula on each piece,
  globally (no local/neighbourhood condition). Agent027 uses the "local agreement"
  definition (family (b)): `f` is continuous and there's a finite set of affine
  functions such that *every point* has a whole neighbourhood on which `f` coincides
  with one of them. These are genuinely different: `wf := fun x => max 0 (x 0)` is
  Agent026-CPWL (two half-spaces `x 0 ≤ 0`/`x 0 ≥ 0`) but fails Agent027's definition at
  `x = 0`, since no single affine function can agree with `wf` on a whole neighbourhood
  of `0` (it would have to equal the identity for small positive first coordinate and the
  zero function for small negative first coordinate simultaneously — impossible for an
  affine function of one variable, pinned down by three points). More generally, on the
  connected domain `ℝⁿ`, Agent027's condition actually forces `f` to be *globally* equal
  to a single affine function (finitely many open "agreement" sets, pairwise disjoint
  since two affine functions agreeing on a nonempty open set must coincide everywhere,
  covering a connected space), so Agent027's `CPWL n` is really just the affine
  functions — a much smaller class than genuine piecewise-linear functions. **REFUTED**
  (`cpwl_ne`).

* `ReLUn` — Agent026's `ReLUn n k` is "representable with *at most* `k` hidden layers"
  (`∃ k' ≤ k, …`, via the `NetParams`/`Σ h, …` recursive type); Agent027's is "*exactly*
  `k` hidden layers" (via `ComputesWithLayers`). As the spec anticipates, these coincide
  only via a padding argument (any `k' ≤ k`-layer network can be re-expressed with
  exactly `k` layers, using `x = ReLU x - ReLU (-x)` componentwise to build
  identity-acting layers, by induction on `k - k'`) that nobody has proved. Building that
  induction from scratch, with all the accompanying width bookkeeping, is out of scope
  for a single bridge link, so `relun` is left `sorry`.

  On top of that: `Agent027.AffineMap.apply` (line 40 of `Thm2_027.lean`) is defined via
  `T.A *ᵥ x + T.bias`, and that `*ᵥ` notation triggers a Mathlib elaboration failure
  (`Mathlib.Tactic.subscriptTerm` not implemented) in this environment.
  `Agent027.ComputesWithLayers` and hence `Agent027.ReLUn` are built directly on top of
  `AffineMap.apply`, so the actual *value* computed by any Agent027 network is not
  trustworthy even where the surrounding declarations still elaborate (as opaque names)
  — any argument that needs to unfold what a network *computes* is blocked, independent
  of the missing padding lemma. This does **not** affect `cpwl` or `depth`, since
  `Agent027.CPWL` and `Agent027.depthBound` never go through `AffineMap`.

* `statement` — reduces (after using `depth`, and noting `cpwl` is false) to a genuinely
  open question about each agent's *own* internal claim (`CPWL n = ReLUn n (depthBound
  n)`), i.e. to reproving the real Theorem 2 for each encoding — for Agent026 this is
  simply the paper's theorem, unproved anywhere in these files; for Agent027 it is
  additionally blocked by the `*ᵥ` issue above. Left `sorry`.
-/

/-! ### `depth`: the two depth bounds are the literal same expression -/

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent026.depthBound n = Agent027.depthBound n := by
  simp only [Agent026.depthBound, Agent027.depthBound]

/-! ### `cpwl_ne`: the two `CPWL` definitions genuinely differ -/

/-- The witness: the one-dimensional ReLU function, as a function of `Fin 1 → ℝ`. It is
honestly piecewise affine in Agent026's polyhedral sense, but has a genuine kink at `0`,
so it fails Agent027's "agrees with a single affine functional on a whole neighbourhood
of every point" reading there. -/
private noncomputable def wf : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

private lemma wf_continuous : Continuous wf :=
  continuous_const.max (continuous_apply 0)

private def P0 : Set (Fin 1 → ℝ) := {x | x 0 ≤ 0}
private def P1 : Set (Fin 1 → ℝ) := {x | 0 ≤ x 0}

private def A0 : Fin 1 → ℝ := fun _ => 0
private def A1 : Fin 1 → ℝ := fun _ => 1

private lemma P0_isPolyhedron : Agent026.IsPolyhedron P0 := by
  refine ⟨1, fun _ j => (1 : ℝ), fun _ => 0, ?_⟩
  ext x
  simp only [P0, Set.mem_setOf_eq, Set.mem_iInter, Fin.forall_fin_one, Fin.sum_univ_one,
    one_mul]

private lemma P1_isPolyhedron : Agent026.IsPolyhedron P1 := by
  refine ⟨1, fun _ j => (-1 : ℝ), fun _ => 0, ?_⟩
  ext x
  simp only [P1, Set.mem_setOf_eq, Set.mem_iInter, Fin.forall_fin_one, Fin.sum_univ_one]
  constructor <;> intro h <;> linarith

private lemma P_cover : (⋃ i, (![P0, P1] : Fin 2 → Set (Fin 1 → ℝ)) i) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  rcases le_total (x 0) 0 with h | h
  · exact ⟨0, by simpa [P0] using h⟩
  · exact ⟨1, by simpa [P1] using h⟩

private lemma wf_mem_026 : wf ∈ Agent026.CPWL 1 := by
  refine ⟨wf_continuous, 2, (![P0, P1] : Fin 2 → Set (Fin 1 → ℝ)),
    (![A0, A1] : Fin 2 → (Fin 1 → ℝ)), (![(0 : ℝ), 0] : Fin 2 → ℝ), ?_, P_cover, ?_⟩
  · intro i
    fin_cases i
    · exact P0_isPolyhedron
    · exact P1_isPolyhedron
  · intro i x hx
    fin_cases i
    · have hx0 : x 0 ≤ 0 := by simpa [P0] using hx
      simp only [wf, Matrix.cons_val_zero, A0, Fin.sum_univ_one, mul_zero, zero_add]
      exact max_eq_left hx0
    · have hx0 : 0 ≤ x 0 := by simpa [P1] using hx
      simp only [wf, Matrix.cons_val_one, Matrix.cons_val_zero, A1, Fin.sum_univ_one,
        one_mul, add_zero]
      exact max_eq_right hx0

/-- No single globally-affine function `g` from Agent027's finite family can agree with
`wf` on a whole neighbourhood of `0`: three points inside any candidate ball (`ε/3`,
`2ε/3`, `-ε/3`) force incompatible values of the linear coefficient. -/
private lemma wf_not_mem_027 : wf ∉ Agent027.CPWL 1 := by
  rintro ⟨-, S, hS, hcov⟩
  obtain ⟨g, hgS, hev⟩ := hcov (fun _ => (0 : ℝ))
  obtain ⟨a, c, hgeq⟩ := hS g hgS
  have hcont : Continuous (fun (t : ℝ) (_ : Fin 1) => t) :=
    continuous_pi (fun _ => continuous_id)
  have hev' : ∀ᶠ t in nhds (0 : ℝ), wf (fun _ => t) = g (fun _ => t) :=
    (hcont.tendsto 0).eventually hev
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev'
  have h1 : dist (ε / 3) (0 : ℝ) < ε := by
    rw [Real.dist_0_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < ε / 3)]; linarith
  have h2 : dist (2 * (ε / 3)) (0 : ℝ) < ε := by
    rw [Real.dist_0_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < 2 * (ε / 3))]; linarith
  have h3 : dist (-(ε / 3)) (0 : ℝ) < ε := by
    rw [Real.dist_0_eq_abs, abs_of_neg (by linarith : -(ε / 3) < (0 : ℝ))]; linarith
  have e1 := hball h1
  have e2 := hball h2
  have e3 := hball h3
  simp only [wf, hgeq, Fin.sum_univ_one] at e1 e2 e3
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ ε / 3)] at e1
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ 2 * (ε / 3))] at e2
  rw [max_eq_left (by linarith : -(ε / 3) ≤ (0 : ℝ))] at e3
  have hcontra : ε / 3 = 0 := by linear_combination (-3 : ℝ) * e1 + 2 * e2 + e3
  linarith

theorem cpwl_ne : ∃ n, Agent026.CPWL n ≠ Agent027.CPWL n :=
  ⟨1, fun h => wf_not_mem_027 (h ▸ wf_mem_026)⟩

/-! ### `relun`: genuinely open (padding lemma, plus the `*ᵥ` elaboration issue) -/

-- `Agent026.ReLUn n k` is "at most `k` hidden layers" while `Agent027.ReLUn n k` is
-- "exactly `k` hidden layers". These agree only via a general padding lemma (any
-- `k' ≤ k`-layer network can be re-expressed with exactly `k` layers, by induction on
-- `k - k'`, using the ReLU identity `x = ReLU x - ReLU (-x)` to build identity-acting
-- layers) that is not proved anywhere in either source file; supplying it here is out of
-- scope for a single bridge link. Independently, `Agent027.ReLUn` is built on
-- `Agent027.AffineMap.apply`, whose body (`T.A *ᵥ x + T.bias`) triggers a Mathlib
-- elaboration failure (`Mathlib.Tactic.subscriptTerm` not implemented) in this
-- environment, so even reasoning about what an Agent027 network *computes* is blocked,
-- independent of the missing padding lemma.
theorem relun (n k : ℕ) : Agent026.ReLUn n k = Agent027.ReLUn n k := sorry

/-! ### `statement`: depends on the same open gaps as `relun`, plus `cpwl_ne` above -/

-- Since `cpwl_ne` shows the two `CPWL` definitions differ, `statement` cannot be reduced
-- to a bridging fact between the two files: settling it requires independently deciding
-- the truth value of each agent's own internal claim `CPWL n = ReLUn n (depthBound n)`.
-- For Agent026 (the mathematically faithful polyhedral encoding) that claim is simply
-- the paper's real Theorem 2, unproved anywhere in `Thm2_026.lean`. For Agent027 it is
-- additionally blocked by the `*ᵥ` elaboration issue described above. Genuinely new
-- mathematics, out of scope for a single bridge link.
theorem statement :
    (∀ n, 3 ≤ n → Agent026.CPWL n = Agent026.ReLUn n (Agent026.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent027.CPWL n = Agent027.ReLUn n (Agent027.depthBound n)) := sorry

end Bridge_026_027

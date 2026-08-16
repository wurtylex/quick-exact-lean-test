namespace Bridge_042_043

/-!
## Summary of the comparison

* `depthBound`: **identical** definitions (`⌈Real.logb 3 ((n:ℝ)-1)⌉₊ + 1`, where `⌈·⌉₊` is
  notation for `Nat.ceil`) — proved by unfolding.
* `CPWL`: **genuinely different**. Agent042 uses an honest global polyhedral subdivision.
  Agent043 uses "at every point there is a *full open metric ball* on which `f` agrees with
  one member of a fixed finite family of affine functions". The function
  `f x = max 0 (x 0)` (the ReLU of the first coordinate) is a textbook CPWL function: it is
  in `Agent042.CPWL 1` via the subdivision `{x0 ≥ 0} ∪ {x0 ≤ 0}`. But it is *not* in
  `Agent043.CPWL 1`: no single affine function can agree with it on a full neighbourhood of
  `0`, because every ball around `0` contains points where `f` behaves like `x0` and points
  where it behaves like `0`, which are different affine functions. So `cpwl` is refuted.
* `ReLUn`: Agent042 uses "*exactly* `k` hidden layers" (`layers.length = k + 1`), Agent043
  uses "*at most* `k` hidden layers" (`∃ k' ≤ k, …`). These are provably equal only via a
  "padding" construction (turning a `k'`-hidden-layer network into an exactly-`k` one, `k ≥
  k'`, using the identity `x = relu x - relu (-x)` to let extra layers act as the identity)
  composed with a translation between Agent042's `List AffineLayer` encoding and Agent043's
  recursive `NetworkComputes` encoding. Both pieces are real, nontrivial constructions that
  nobody has formalized (see `BRIDGE_SPEC.md`); we were not able to complete them, nor find a
  genuine counterexample (we believe the sets actually coincide mathematically), so `relun`
  is left as `sorry`.
* `statement`: depends on the (unresolved) `relun` equivalence, and — even granting that —
  on the actual truth value of Agent042's own literal theorem statement (a nontrivial
  instance of the paper's real theorem for the "exactly k" reading), which is far beyond the
  scope of a single bridge file. Left as `sorry`.
-/

/-- Both agents write the depth bound with the identical formula
`⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1` (the notation `⌈·⌉₊` unfolds to `Nat.ceil`), so the two
definitions are syntactically the same function of `n` and the bound `hn` is not even needed. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent042.depthBound n = Agent043.depthBound n := by
  simp only [Agent042.depthBound, Agent043.depthBound]

/-- `Agent042.CPWL` is the honest global polyhedral-subdivision definition; `Agent043.CPWL`
requires local agreement with an affine function on a *full open metric ball* around every
point. The ReLU-of-a-coordinate function `f x = max 0 (x 0)` lies in the former (subdivide
`ℝ¹` into `{x0 ≥ 0}` and `{x0 ≤ 0}`) but not the latter: no affine function can match `f` on
a full ball around `0`, since such a ball always contains points with `x0 > 0` (where
matching forces the affine function to be `x0`) and points with `x0 < 0` (where matching
forces it to be `0`) simultaneously. -/
theorem cpwl_ne : ∃ n, Agent042.CPWL n ≠ Agent043.CPWL n := by
  refine ⟨1, fun hEq => ?_⟩
  have hmem042 : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent042.CPWL 1 := by
    refine ⟨continuous_const.max (continuous_apply 0), 2,
      ![{x : Fin 1 → ℝ | 0 ≤ x 0}, {x : Fin 1 → ℝ | x 0 ≤ 0}],
      ![(fun _ : Fin 1 => (1 : ℝ)), (fun _ : Fin 1 => (0 : ℝ))],
      ![(0 : ℝ), (0 : ℝ)], ?_, ?_, ?_⟩
    · intro i
      fin_cases i
      · refine ⟨1, ![fun _ : Fin 1 => (-1 : ℝ)], ![(0 : ℝ)], ?_⟩
        ext x
        simp only [Matrix.cons_val_zero, Set.mem_setOf_eq]
        constructor
        · intro h j
          fin_cases j
          simp only [Matrix.cons_val_zero, Fin.sum_univ_one]
          linarith
        · intro h
          have h0 := h 0
          simp only [Matrix.cons_val_zero, Fin.sum_univ_one] at h0
          linarith
      · refine ⟨1, ![fun _ : Fin 1 => (1 : ℝ)], ![(0 : ℝ)], ?_⟩
        ext x
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Set.mem_setOf_eq]
        constructor
        · intro h j
          fin_cases j
          simp only [Matrix.cons_val_zero, Fin.sum_univ_one]
          linarith
        · intro h
          have h0 := h 0
          simp only [Matrix.cons_val_zero, Fin.sum_univ_one] at h0
          linarith
    · ext x
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      rcases le_or_lt 0 (x 0) with h | h
      · exact ⟨0, by
          simp only [Matrix.cons_val_zero, Set.mem_setOf_eq]
          linarith⟩
      · exact ⟨1, by
          simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Set.mem_setOf_eq]
          linarith⟩
    · intro i
      fin_cases i
      · intro x hx
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_setOf_eq] at hx
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.sum_univ_one]
        rw [max_eq_right_iff.mpr hx]
        ring
      · intro x hx
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_setOf_eq] at hx
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.sum_univ_one]
        rw [max_eq_left_iff.mpr hx]
        ring
  have hmem043 : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent043.CPWL 1 := by
    rw [← hEq]; exact hmem042
  obtain ⟨-, N, A, c, hloc⟩ := hmem043
  obtain ⟨r, hr, i, hi⟩ := hloc (0 : Fin 1 → ℝ)
  have key : ∀ v : ℝ, |v| < r → max 0 v = A i 0 * v + c i := by
    intro v hv
    have hd : dist (fun _ : Fin 1 => v) (0 : Fin 1 → ℝ) < r := by
      rw [dist_pi_lt_iff hr]
      intro b
      show dist v (0 : ℝ) < r
      rw [Real.dist_eq]
      simpa using hv
    have hh := hi (fun _ : Fin 1 => v) hd
    simp only [Fin.sum_univ_one] at hh
    exact hh
  have hr2 : |r / 2| < r := by rw [abs_of_pos (by linarith : (0:ℝ) < r / 2)]; linarith
  have hr4 : |r / 4| < r := by rw [abs_of_pos (by linarith : (0:ℝ) < r / 4)]; linarith
  have hrn2 : |(-(r / 2))| < r := by
    rw [abs_neg, abs_of_pos (by linarith : (0:ℝ) < r / 2)]; linarith
  have h1 := key (r / 2) hr2
  have h2 := key (r / 4) hr4
  have h3 := key (-(r / 2)) hrn2
  rw [max_eq_right_iff.mpr (by linarith : (0:ℝ) ≤ r / 2)] at h1
  rw [max_eq_right_iff.mpr (by linarith : (0:ℝ) ≤ r / 4)] at h2
  rw [max_eq_left_iff.mpr (by linarith : -(r / 2) ≤ (0:ℝ))] at h3
  have hb : c i = 0 := by linear_combination h1 - 2 * h2
  have e1 : r / 2 = 2 * c i := by linear_combination h1 + h3
  linarith [e1, hb, hr]

/- `Agent042.ReLUn n k` requires networks with *exactly* `k` hidden layers (a `List
AffineLayer` of length `k + 1`); `Agent043.ReLUn n k` allows *at most* `k` (`∃ k' ≤ k, …`).
These two readings are reconciled only via a "padding" construction: any network with `k' ≤
k` hidden layers can be extended to one with exactly `k` hidden layers by inserting `k - k'`
extra layers that act as the identity, using `x = relu x - relu (-x)` on a doubled-width
copy of the signal. That construction (plus a translation between Agent042's `List
AffineLayer` representation and Agent043's recursive `NetworkComputes` representation of
"exactly `k`" networks) is exactly the open lemma flagged in BRIDGE_SPEC.md ("nobody has
proved that lemma"); we believe the two sets are in fact equal for every `n k`, so no
counterexample exists to refute this, but formalizing the padding + encoding-translation
argument is a substantial undertaking beyond what we could complete here. -/
theorem relun (n k : ℕ) : Agent042.ReLUn n k = Agent043.ReLUn n k := by
  sorry

/- This is blocked by two independent hard problems: (1) the `relun` equivalence above is
open, and (2) even granting it, resolving the `↔` requires knowing the truth value of at
least one side's literal theorem statement. We already know `Agent043`'s own statement is
false as formalized: at `n = 3`, `depthBound = 2`, and `max 0 (x 0)` lies in
`Agent043.ReLUn 3 2` (it needs only 1 hidden layer) but not in `Agent043.CPWL 3` (by the same
local-agreement argument as in `cpwl_ne`, applied at the origin). Resolving the biconditional
would then require determining whether `Agent042`'s own statement is also false (which would
prove `statement`) or true (which would prove `statement_ne`) — i.e. deciding a nontrivial
instance of the paper's actual theorem, which is out of scope for a single bridge file. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent042.CPWL n = Agent042.ReLUn n (Agent042.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent043.CPWL n = Agent043.ReLUn n (Agent043.depthBound n)) := by
  sorry

end Bridge_042_043

namespace Bridge_074_075

/-! ## `depth`

Both formalizations write the depth bound with the literally identical real-valued formula
`⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1` (`Nat.ceil` and the `⌈·⌉₊` notation are the same function),
so this is definitional. -/

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent074.depthBound n = Agent075.depthBound n := by
  simp only [Agent074.depthBound, Agent075.depthBound]

/-! ## `cpwl` : REFUTED.

`Agent074.CPWL` is the standard *global* polyhedral-subdivision reading: a finite cover of
`ℝⁿ` by closed polyhedra on each of which `f` agrees with an affine function. `Agent075.CPWL`
instead demands that `f` agree with *one globally affine function* on a full two-sided open
neighbourhood of *every* point. A genuinely kinked function such as `x ↦ max 0 (x 0)` is CPWL
under the first reading (split `ℝ` at `0`), but cannot be CPWL under the second: any open
neighbourhood of `0` contains points on both sides of the kink, and no single affine function
can match `max 0 t` on both a right- and a left-interval around `0` (two points on the right
already force the affine function to be the identity `t ↦ t`, which then fails on the left).
We witness this at `n = 1`. -/

def kink : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

/-- The two half-lines of `ℝ` (as subsets of `Fin 1 → ℝ`) used to cover `kink`. -/
def halfP : Bool → Set (Fin 1 → ℝ)
  | true => {x | x 0 ≤ 0}
  | false => {x | 0 ≤ x 0}

/-- The two affine pieces `kink` agrees with on `halfP true` / `halfP false`. -/
def halfG : Bool → (Fin 1 → ℝ) → ℝ
  | true => fun _ => 0
  | false => fun x => x 0

theorem kink_mem_074 : kink ∈ Agent074.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), Bool, inferInstance, halfP, ?_, ?_, ?_⟩
  · intro i
    cases i with
    | true =>
        refine ⟨Unit, inferInstance, fun _ _ => (1 : ℝ), fun _ => 0, ?_⟩
        ext x
        simp only [halfP, Set.mem_setOf_eq, Fin.sum_univ_one]
        constructor
        · intro h _; linarith
        · intro h; linarith [h ()]
    | false =>
        refine ⟨Unit, inferInstance, fun _ _ => (-1 : ℝ), fun _ => 0, ?_⟩
        ext x
        simp only [halfP, Set.mem_setOf_eq, Fin.sum_univ_one]
        constructor
        · intro h _; linarith
        · intro h; linarith [h ()]
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    rcases le_total (x 0) 0 with h | h
    · exact ⟨true, by simp only [halfP, Set.mem_setOf_eq]; exact h⟩
    · exact ⟨false, by simp only [halfP, Set.mem_setOf_eq]; exact h⟩
  · intro i
    cases i with
    | true =>
        refine ⟨halfG true, ⟨0, 0, fun x => by simp [halfG]⟩, fun x hx => ?_⟩
        have hx' : x 0 ≤ 0 := hx
        show max 0 (x 0) = 0
        exact max_eq_left_iff.mpr hx'
    | false =>
        refine ⟨halfG false, ⟨fun _ => 1, 0, fun x => by simp [halfG, Fin.sum_univ_one]⟩,
          fun x hx => ?_⟩
        have hx' : 0 ≤ x 0 := hx
        show max 0 (x 0) = x 0
        exact max_eq_right_iff.mpr hx'

/-- The constant-in-`Fin 1`-coordinate embedding `ℝ → (Fin 1 → ℝ)`, used to probe a two-sided
neighbourhood of `0` in `Fin 1 → ℝ` via a single real parameter. -/
def c0 : ℝ → Fin 1 → ℝ := fun t _ => t

theorem c0_cont : Continuous c0 := continuous_pi (fun _ => continuous_id)

theorem c0_zero : c0 0 = (0 : Fin 1 → ℝ) := by funext j; rfl

theorem cpwl_ne : ∃ n, Agent074.CPWL n ≠ Agent075.CPWL n := by
  refine ⟨1, fun hset => ?_⟩
  have hmem075 : kink ∈ Agent075.CPWL 1 := by rw [← hset]; exact kink_mem_074
  obtain ⟨-, m, g, hg_affine, hg_cover⟩ := hmem075
  obtain ⟨i, U, hU, heq⟩ := hg_cover (0 : Fin 1 → ℝ)
  obtain ⟨w, b, hgi⟩ := hg_affine i
  have hgi' : ∀ t : ℝ, g i (c0 t) = w 0 * t + b := by
    intro t; rw [hgi]; simp [c0, Fin.sum_univ_one]
  have htendsto : Filter.Tendsto c0 (nhds (0 : ℝ)) (nhds (0 : Fin 1 → ℝ)) :=
    c0_cont.tendsto' 0 (0 : Fin 1 → ℝ) c0_zero
  have hpre : c0 ⁻¹' U ∈ nhds (0 : ℝ) := Filter.tendsto_def.mp htendsto U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  have hmemU : ∀ t : ℝ, |t| < ε → c0 t ∈ U := by
    intro t ht
    exact hball (by simp only [Metric.mem_ball, Real.dist_eq, sub_zero]; exact ht)
  have e1 : max 0 (ε / 2) = w 0 * (ε / 2) + b := by
    have h : kink (c0 (ε / 2)) = g i (c0 (ε / 2)) :=
      heq (hmemU (ε / 2) (by rw [abs_of_pos (show (0:ℝ) < ε / 2 by linarith)]; linarith))
    rw [hgi'] at h; exact h
  have e2 : max 0 (ε / 4) = w 0 * (ε / 4) + b := by
    have h : kink (c0 (ε / 4)) = g i (c0 (ε / 4)) :=
      heq (hmemU (ε / 4) (by rw [abs_of_pos (show (0:ℝ) < ε / 4 by linarith)]; linarith))
    rw [hgi'] at h; exact h
  have e3 : max 0 (-(ε / 2)) = w 0 * (-(ε / 2)) + b := by
    have h : kink (c0 (-(ε / 2))) = g i (c0 (-(ε / 2))) :=
      heq (hmemU (-(ε / 2)) (by rw [abs_of_neg (show -(ε / 2) < (0:ℝ) by linarith)]; linarith))
    rw [hgi'] at h; exact h
  rw [max_eq_right_iff.mpr (show (0:ℝ) ≤ ε / 2 by linarith)] at e1
  rw [max_eq_right_iff.mpr (show (0:ℝ) ≤ ε / 4 by linarith)] at e2
  rw [max_eq_left_iff.mpr (show -(ε / 2) ≤ (0:ℝ) by linarith)] at e3
  have hw : w 0 = 1 := by
    have hcancel : ε / 4 * (1 - w 0) = 0 := by linear_combination e1 - e2
    have hε4 : ε / 4 ≠ 0 := ne_of_gt (by linarith)
    rcases mul_eq_zero.mp hcancel with h | h
    · exact absurd h hε4
    · linarith
  have hb : b = 0 := by rw [hw] at e2; linarith
  rw [hw, hb] at e3
  linarith

/-! ## `relun` : LEFT AS `sorry`.

`Agent074.ReLUn n k` reads "*at most* `k` hidden layers" while `Agent075.ReLUn n k` reads
"*exactly* `k`". These two readings do describe the same sets of functions -- a network with
fewer layers can be padded out to exactly `k` layers, since the identity
`relu v - relu (-v) = v` lets one affine+ReLU layer simulate an affine pass-through -- but
formalizing that padding construction means building, by induction on `k - k'`, an explicit
wider `ReLUNet` that composes this trick at every extra layer. That induction is real work
and does not fit in a short bridge file, so we leave it `sorry` rather than fake it. -/
theorem relun (n k : ℕ) : Agent074.ReLUn n k = Agent075.ReLUn n k := by
  sorry

/-! ## `statement` : LEFT AS `sorry`.

Both `Agent074.theorem2` and `Agent075.theorem2` are themselves `sorry`d in the source files.
The left-hand side of the iff is exactly the paper's Theorem 2 phrased in Agent074's
(faithful, global-polyhedral) terms -- an open formalization question this bridge cannot
settle. The right-hand side is very plausibly false: generalizing the `cpwl_ne` argument
above to any `n ≥ 3` (by varying only the first coordinate and holding the rest fixed at `0`)
shows `Agent075.CPWL n` excludes ReLU-representable kinked functions such as
`x ↦ max 0 (x 0)`, which do lie in `Agent075.ReLUn n (Agent075.depthBound n)`; so the
right-hand universal statement is refutable. But turning "RHS is false" into a proof of the
negated iff still requires knowing the truth value of the left-hand side, i.e. reproving
Theorem 2 itself for Agent074's definitions, which is out of scope here. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent074.CPWL n = Agent074.ReLUn n (Agent074.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent075.CPWL n = Agent075.ReLUn n (Agent075.depthBound n)) := by
  sorry

end Bridge_074_075

namespace Bridge_028_029

/-!
## Summary of the comparison

The key structural difference between the two files is in `CPWL`:

* `Agent028.CPWL n` requires a *single* affine function to agree with `f` on a full
  topological neighbourhood of *every* point (`∀ x, ∃ i, ∀ᶠ y in nhds x, f y = (T i).eval y`
  for some fixed finite family `T`). Call this the "local agreement" reading.
* `Agent029.CPWL n` requires a finite cover of `ℝ^n` by polyhedra, on each of which `f`
  agrees with an affine function *on the whole (closed) polyhedron*, allowing different
  affine pieces to meet along a shared boundary. This is the genuine piecewise-affine
  reading, and is the one that matches the paper.

Because `ℝ^n` is connected, the `Agent028` reading is in fact far more restrictive than
intended: at a "kink" point of a genuine CPWL function (e.g. `x ↦ max 0 (x i)` at `x = 0`),
no single affine function agrees with `f` on any full neighbourhood, however small — one
side of the kink forces the affine function to be `0`, the other side forces it to be the
coordinate projection, and these disagree arbitrarily close to the kink. So the scalar
ReLU-type function `witness`, which certainly is a genuine CPWL function (`Agent029.CPWL`),
is *not* a member of `Agent028.CPWL`. This one example is enough to refute `cpwl`.
-/

/-- A distinguished coordinate index (index `0`), used to build the ReLU-type witness
function below. Needs `1 ≤ n` for `Fin n` to be nonempty. -/
def idx0 {n : ℕ} (hn : 1 ≤ n) : Fin n := ⟨0, hn⟩

/-- The scalar ReLU-type function `x ↦ max 0 (x (idx0 hn))`. It is a genuine CPWL function
(piecewise affine, with a kink at the hyperplane `x (idx0 hn) = 0`), but it is *not* locally
affine at the kink, so it separates `Agent028.CPWL` from `Agent029.CPWL`. -/
noncomputable def witness {n : ℕ} (hn : 1 ≤ n) : (Fin n → ℝ) → ℝ :=
  fun x => max 0 (x (idx0 hn))

theorem witness_continuous {n : ℕ} (hn : 1 ≤ n) : Continuous (witness hn) :=
  continuous_const.max (continuous_apply (idx0 hn))

/-- `max 0 t = t` when `0 ≤ t`, proved from first principles to avoid relying on the exact
name of the (possibly differently-named) standard lemma. -/
theorem max_zero_of_nonneg {t : ℝ} (h : 0 ≤ t) : max (0 : ℝ) t = t :=
  le_antisymm (max_le h le_rfl) (le_max_right 0 t)

/-- `max 0 t = 0` when `t ≤ 0`. -/
theorem max_zero_of_nonpos {t : ℝ} (h : t ≤ 0) : max (0 : ℝ) t = 0 :=
  le_antisymm (max_le le_rfl h) (le_max_left 0 t)

/-- `∑ j, (if j = z then c else 0) * x j = c * x z`, the basic "single nonzero term" sum
identity used repeatedly below (for polyhedron/affine witnesses and for extracting
coordinates of an affine functional). -/
theorem sum_ite_eq_self_smul {m : ℕ} (z : Fin m) (c : ℝ) (x : Fin m → ℝ) :
    ∑ j, (if j = z then c else 0) * x j = c * x z := by
  rw [Finset.sum_eq_single z]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg hb]; ring
  · intro h
    exact absurd (Finset.mem_univ z) h

/-- The analogous identity for a function obtained by `Function.update`ing the zero
function at a single coordinate `z`. -/
theorem sum_update_zero {m : ℕ} (z : Fin m) (w : Fin m → ℝ) (t : ℝ) :
    ∑ j, w j * (Function.update (0 : Fin m → ℝ) z t) j = w z * t := by
  rw [Finset.sum_eq_single z]
  · rw [Function.update_self]
  · intro b _ hb
    rw [Function.update_of_ne hb]; ring
  · intro h
    exact absurd (Finset.mem_univ z) h

/-- `Agent028.AffineFunc.eval` unfolded, as a rewritable equation. -/
theorem eval028_eq {n : ℕ} (T : Agent028.AffineFunc n) (x : Fin n → ℝ) :
    T.eval x = (∑ j, T.w j * x j) + T.b := rfl

/-! ### `witness` is genuinely CPWL for Agent029 -/

theorem is_polyhedron_le {n : ℕ} (hn : 1 ≤ n) :
    Agent029.IsPolyhedron {x : Fin n → ℝ | x (idx0 hn) ≤ 0} := by
  refine ⟨1, fun _ j => if j = idx0 hn then (1 : ℝ) else 0, fun _ => 0, ?_⟩
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hx j
    rw [sum_ite_eq_self_smul, one_mul]
    exact hx
  · intro hx
    have h1 := hx 0
    rwa [sum_ite_eq_self_smul, one_mul] at h1

theorem is_polyhedron_ge {n : ℕ} (hn : 1 ≤ n) :
    Agent029.IsPolyhedron {x : Fin n → ℝ | 0 ≤ x (idx0 hn)} := by
  refine ⟨1, fun _ j => if j = idx0 hn then (-1 : ℝ) else 0, fun _ => 0, ?_⟩
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hx j
    rw [sum_ite_eq_self_smul]
    linarith
  · intro hx
    have h1 := hx 0
    rw [sum_ite_eq_self_smul] at h1
    linarith

theorem is_affine_on_le {n : ℕ} (hn : 1 ≤ n) :
    Agent029.IsAffineOn (witness hn) {x : Fin n → ℝ | x (idx0 hn) ≤ 0} := by
  refine ⟨0, 0, ?_⟩
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  have hw : witness hn x = 0 := by
    show max (0 : ℝ) (x (idx0 hn)) = 0
    exact max_zero_of_nonpos hx
  rw [hw]
  simp

theorem is_affine_on_ge {n : ℕ} (hn : 1 ≤ n) :
    Agent029.IsAffineOn (witness hn) {x : Fin n → ℝ | 0 ≤ x (idx0 hn)} := by
  refine ⟨fun j => if j = idx0 hn then (1 : ℝ) else 0, 0, ?_⟩
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  have hw : witness hn x = x (idx0 hn) := by
    show max (0 : ℝ) (x (idx0 hn)) = x (idx0 hn)
    exact max_zero_of_nonneg hx
  rw [hw, sum_ite_eq_self_smul]
  ring

theorem witness_mem_029 {n : ℕ} (hn : 1 ≤ n) : witness hn ∈ Agent029.CPWL n := by
  refine ⟨witness_continuous hn, 2,
    (fun i => if i = 0 then {x : Fin n → ℝ | x (idx0 hn) ≤ 0}
              else {x : Fin n → ℝ | 0 ≤ x (idx0 hn)}),
    ?_, ?_, ?_⟩
  · intro i
    dsimp only
    by_cases hi : i = 0
    · rw [if_pos hi]; exact is_polyhedron_le hn
    · rw [if_neg hi]; exact is_polyhedron_ge hn
  · apply Set.eq_univ_of_forall
    intro x
    rw [Set.mem_iUnion]
    rcases le_or_lt (x (idx0 hn)) 0 with h | h
    · refine ⟨0, ?_⟩
      dsimp only
      rw [if_pos rfl]
      exact h
    · refine ⟨1, ?_⟩
      dsimp only
      rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]
      exact le_of_lt h
  · intro i
    dsimp only
    by_cases hi : i = 0
    · rw [if_pos hi]; exact is_affine_on_le hn
    · rw [if_neg hi]; exact is_affine_on_ge hn

/-! ### `witness` is not locally affine at `0`, so it fails Agent028's reading -/

theorem witness_not_mem_028 {n : ℕ} (hn : 1 ≤ n) : witness hn ∉ Agent028.CPWL n := by
  rintro ⟨-, ι, _inst, T, hloc⟩
  obtain ⟨i, hev⟩ := hloc (0 : Fin n → ℝ)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  -- Step 1: evaluating at the origin pins down the constant term of `T i` to be `0`.
  have h0 : witness hn (0 : Fin n → ℝ) = (T i).eval (0 : Fin n → ℝ) :=
    hball (0 : Fin n → ℝ) (Metric.mem_ball_self hε)
  have hzero_witness : witness hn (0 : Fin n → ℝ) = 0 := by
    show max (0 : ℝ) ((0 : Fin n → ℝ) (idx0 hn)) = 0
    simp
  have hzero_eval : (T i).eval (0 : Fin n → ℝ) = (T i).b := by
    rw [eval028_eq]; simp
  have hc0 : (T i).b = 0 := by
    have h0' := h0
    rw [hzero_witness, hzero_eval] at h0'
    exact h0'.symm
  -- Step 2: two more points, at `± ε / 2` along the distinguished coordinate, both lying
  -- in the ball where `witness` must agree with the (now constant-free) affine map `T i`.
  set yp : Fin n → ℝ := Function.update (0 : Fin n → ℝ) (idx0 hn) (ε / 2) with hyp_def
  set ym : Fin n → ℝ := Function.update (0 : Fin n → ℝ) (idx0 hn) (-(ε / 2)) with hym_def
  have hyp_ball : yp ∈ Metric.ball (0 : Fin n → ℝ) ε := by
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro b
    by_cases hb : b = idx0 hn
    · subst hb
      show dist (yp (idx0 hn)) ((0 : Fin n → ℝ) (idx0 hn)) < ε
      rw [hyp_def, Function.update_self]
      show dist (ε / 2) (0 : ℝ) < ε
      rw [Real.dist_eq, show (ε / 2 - 0 : ℝ) = ε / 2 by ring, abs_of_pos (by linarith)]
      linarith
    · show dist (yp b) ((0 : Fin n → ℝ) b) < ε
      rw [hyp_def, Function.update_of_ne hb]
      simpa using hε
  have hym_ball : ym ∈ Metric.ball (0 : Fin n → ℝ) ε := by
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro b
    by_cases hb : b = idx0 hn
    · subst hb
      show dist (ym (idx0 hn)) ((0 : Fin n → ℝ) (idx0 hn)) < ε
      rw [hym_def, Function.update_self]
      show dist (-(ε / 2)) (0 : ℝ) < ε
      rw [Real.dist_eq, show (-(ε / 2) - 0 : ℝ) = -(ε / 2) by ring, abs_neg,
        abs_of_pos (by linarith)]
      linarith
    · show dist (ym b) ((0 : Fin n → ℝ) b) < ε
      rw [hym_def, Function.update_of_ne hb]
      simpa using hε
  have hp : witness hn yp = (T i).eval yp := hball yp hyp_ball
  have hm : witness hn ym = (T i).eval ym := hball ym hym_ball
  have hwp : witness hn yp = ε / 2 := by
    show max (0 : ℝ) (yp (idx0 hn)) = ε / 2
    rw [hyp_def, Function.update_self]
    exact max_zero_of_nonneg (by linarith)
  have hwm : witness hn ym = 0 := by
    show max (0 : ℝ) (ym (idx0 hn)) = 0
    rw [hym_def, Function.update_self]
    exact max_zero_of_nonpos (by linarith)
  have hep : (T i).eval yp = (T i).w (idx0 hn) * (ε / 2) := by
    rw [eval028_eq, hc0, add_zero, hyp_def]
    exact sum_update_zero (idx0 hn) (T i).w (ε / 2)
  have hem : (T i).eval ym = (T i).w (idx0 hn) * (-(ε / 2)) := by
    rw [eval028_eq, hc0, add_zero, hym_def]
    exact sum_update_zero (idx0 hn) (T i).w (-(ε / 2))
  rw [hwp, hep] at hp
  rw [hwm, hem] at hm
  -- `hp : ε / 2 = w * (ε / 2)` and `hm : 0 = w * (-(ε / 2))` together force `ε / 2 = 0`,
  -- contradicting `hε : 0 < ε`.
  have hring : (T i).w (idx0 hn) * (-(ε / 2)) = -((T i).w (idx0 hn) * (ε / 2)) := by ring
  rw [hring] at hm
  have key : (T i).w (idx0 hn) * (ε / 2) = 0 := by linarith
  linarith [hp.trans key]

/-- **`cpwl` obligation — REFUTED.** `Agent028.CPWL` uses a "local agreement at every
point" reading of piecewise-affine, which (by connectedness of `ℝ^n`) forbids any genuine
kink; `Agent029.CPWL` uses the correct polyhedral-subdivision reading, which allows kinks
where distinct affine pieces meet. The scalar ReLU-type `witness` function witnesses the
difference already at `n = 1`. -/
theorem cpwl_ne : ∃ n, Agent028.CPWL n ≠ Agent029.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  exact witness_not_mem_028 (le_refl 1) (by rw [h]; exact witness_mem_029 (le_refl 1))

/-- **`depth` obligation — PROVED.** Both agents encode `⌈log_3(n-1)⌉ + 1` via
`Real.logb 3` and `Nat.ceil`; the only difference is whether `n - 1` is subtracted in `ℕ`
first (Agent028) or in `ℝ` directly (Agent029). For `n ≥ 3` (in particular `n ≥ 1`), `ℕ`
subtraction agrees with `ℝ` subtraction after casting, by `Nat.cast_sub`. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent028.depthBound n = Agent029.depthBound n := by
  unfold Agent028.depthBound Agent029.depthBound
  have h1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have h1n : (1 : ℕ) ≤ n := by omega
    rw [Nat.cast_sub h1n, Nat.cast_one]
  rw [h1]

/-- **`relun` obligation — left `sorry`.** Agent028's `ReLUn n k` means "representable
with *at most* `k` hidden layers" (`∃ k' ≤ k, IsReLUNetFun k' n 1 f`), while Agent029's
`ReLUn n k` means "representable with *exactly* `k` hidden layers" via a structurally
different concrete network encoding (recursive peeling vs. an explicit `widths`/`layers`
record folded with `List.foldl`). Proving these sets equal for all `n k` needs (1) a
by-induction structural correspondence between `Agent028.IsReLUNetFun k n 1` and
`Agent029.Network n k`-representability at the *same* depth `k`, and (2) the "padding"
lemma (via `x = ReLU x - ReLU (-x)` simulating an identity layer) letting a `k' ≤ k` layer
network be re-expressed with exactly `k` layers, since Agent028's set is a union over
`k' ≤ k` while Agent029's is not. Neither ingredient is established in either source file
(the spec notes nobody has proved the padding lemma), and both are substantial enough that
getting them wrong silently would be worse than leaving this open. -/
theorem relun (n k : ℕ) : Agent028.ReLUn n k = Agent029.ReLUn n k := sorry

/-- **`statement` obligation — left `sorry`.** Using `witness_not_mem_028`, one can show
`Agent028.CPWL n ≠ Agent028.ReLUn n (Agent028.depthBound n)` for every `n ≥ 3` (the
witness has 1 hidden layer, and `Agent028.depthBound n ≥ 1` always, so it lies in the
right-hand side; it does not lie in `Agent028.CPWL n`). So Agent028's rendering of
Theorem 2 is *provably false*, and the stated `Iff` reduces to the negation of Agent029's
rendering. Deciding that negation requires proving or disproving genuine Theorem 2 for
Agent029's own (faithful, polyhedral) encoding — i.e. the paper's actual, highly nontrivial
result — which is well beyond the scope of a single bridge file. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent028.CPWL n = Agent028.ReLUn n (Agent028.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent029.CPWL n = Agent029.ReLUn n (Agent029.depthBound n)) := sorry

end Bridge_028_029

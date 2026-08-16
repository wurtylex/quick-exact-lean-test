namespace Bridge_031_032

/-
Summary of the comparison between `Agent031` and `Agent032`:

* `depthBound` is defined by the *literally identical* formula
  `⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1` in both files, so `depth` is immediate.
* `ReLUn`/`IsReLUComputable` (`031`) and `ReLUn`/`ReLUComputable` (`032`) use the same
  "alternating affine / componentwise-ReLU" recursive scheme and the same "at most k
  hidden layers" reading; the only difference is that the affine-map structure is
  called `AffineMap'` with field `bias` in `031` and field `c` in `032`. These are
  literally the same data under renaming, so `relun` is provable via an explicit
  conversion between the two `AffineMap'` types.
* `CPWL` genuinely differs:
  - `032` uses a finite polyhedral subdivision with `f` affine on each piece (the
    standard, faithful reading of "continuous piecewise linear").
  - `031` uses local agreement: every point has an *entire metric ball* around it on
    which `f` coincides with **one single** member of a fixed finite family of affine
    maps. Because `ℝ^n` is connected and two affine maps that agree on a nonempty open
    set must be equal everywhere, this forces `031`'s `CPWL n` to consist only of
    *globally* affine functions (a kink, such as `x ↦ max 0 (x 0)`, has no single affine
    map matching it on a whole neighbourhood of the kink locus). In particular the
    ReLU-shaped function is `032`-CPWL but not `031`-CPWL, so the two sets differ. This
    is proved concretely below at `n = 1` (`cpwl_ne`).
-/

/-- Convert an `Agent031`-style affine map to an `Agent032`-style one; same data, the
`bias` field is just called `c` on the other side. -/
def toB {a b : ℕ} (T : Agent031.AffineMap' a b) : Agent032.AffineMap' a b :=
  ⟨T.A, T.bias⟩

/-- Convert an `Agent032`-style affine map to an `Agent031`-style one. -/
def toA {a b : ℕ} (T : Agent032.AffineMap' a b) : Agent031.AffineMap' a b :=
  ⟨T.A, T.c⟩

lemma toB_eval {a b : ℕ} (T : Agent031.AffineMap' a b) (x : Fin a → ℝ) :
    (toB T).eval x = T.eval x := by
  funext i
  simp [toB, Agent031.AffineMap'.eval, Agent032.AffineMap'.eval]

lemma toA_eval {a b : ℕ} (T : Agent032.AffineMap' a b) (x : Fin a → ℝ) :
    (toA T).eval x = T.eval x := by
  funext i
  simp [toA, Agent031.AffineMap'.eval, Agent032.AffineMap'.eval]

/-- `reluVec` is the same formula (`componentwise max 0`) in both files. -/
lemma reluVec_eq {m : ℕ} (v : Fin m → ℝ) :
    Agent031.reluVec v = Agent032.reluVec v := by
  funext i
  simp [Agent031.reluVec, Agent032.reluVec, Agent031.relu, Agent032.relu]

/-- The two "computable by a ReLU network with exactly `k` hidden layers" predicates
agree, for every input dimension. Proved by induction on `k` (with the dimension `n`
and the function `f` generalized, since the recursive step changes dimension to an
auxiliary width `m`). -/
theorem reluComputable_iff :
    ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
      Agent031.IsReLUComputable n k f ↔ Agent032.ReLUComputable n k f := by
  intro k
  induction k with
  | zero =>
      intro n f
      constructor
      · rintro ⟨T, hT⟩
        exact ⟨toB T, fun x => by rw [hT x, toB_eval T x]⟩
      · rintro ⟨T, hT⟩
        exact ⟨toA T, fun x => by rw [hT x, toA_eval T x]⟩
  | succ k ih =>
      intro n f
      constructor
      · rintro ⟨m, T, g, hg, hf⟩
        refine ⟨m, toB T, g, (ih m g).mp hg, fun x => ?_⟩
        rw [hf x, toB_eval T x, reluVec_eq (T.eval x)]
      · rintro ⟨m, T, g, hg, hf⟩
        refine ⟨m, toA T, g, (ih m g).mpr hg, fun x => ?_⟩
        rw [hf x, ← toA_eval T x, ← reluVec_eq ((toA T).eval x)]

theorem relun (n k : ℕ) : Agent031.ReLUn n k = Agent032.ReLUn n k := by
  unfold Agent031.ReLUn Agent032.ReLUn
  ext f
  constructor
  · rintro ⟨k', hk', hf⟩
    exact ⟨k', hk', (reluComputable_iff k' n f).mp hf⟩
  · rintro ⟨k', hk', hf⟩
    exact ⟨k', hk', (reluComputable_iff k' n f).mpr hf⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent031.depthBound n = Agent032.depthBound n := by
  simp only [Agent031.depthBound, Agent032.depthBound]

/-- The one-dimensional "kink" function `x ↦ max 0 (x 0)`, the canonical example of a
genuinely (non-affinely) piecewise-linear function. -/
def kink : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

theorem cpwl_ne : ∃ n, Agent031.CPWL n ≠ Agent032.CPWL n := by
  refine ⟨1, fun hEq => ?_⟩
  have hcont : Continuous kink := continuous_const.max (continuous_apply 0)
  -- `kink` is in `Agent032`'s CPWL via the polyhedral subdivision `{x0 ≤ 0} ∪ {x0 ≥ 0}`.
  have hmemB : kink ∈ Agent032.CPWL 1 := by
    refine ⟨hcont, Bool, inferInstance,
      fun b => if b then {x : Fin 1 → ℝ | 0 ≤ x 0} else {x : Fin 1 → ℝ | x 0 ≤ 0},
      ?_, ?_, ?_⟩
    · intro b
      cases b with
      | false =>
          refine ⟨1, fun _ _ => 1, fun _ => 0, ?_⟩
          ext x
          constructor
          · intro hx j; simpa [Fin.sum_univ_one] using hx
          · intro hx; simpa [Fin.sum_univ_one] using hx 0
      | true =>
          refine ⟨1, fun _ _ => -1, fun _ => 0, ?_⟩
          ext x
          constructor
          · intro hx j
            simp only [Fin.sum_univ_one]
            have hx' : (0:ℝ) ≤ x 0 := hx
            linarith
          · intro hx
            have h0 := hx 0
            simp only [Fin.sum_univ_one] at h0
            show (0:ℝ) ≤ x 0
            linarith
    · ext x
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      rcases le_total (x 0) 0 with h | h
      · exact ⟨false, by simpa using h⟩
      · exact ⟨true, by simpa using h⟩
    · intro b
      cases b with
      | false =>
          refine ⟨fun _ => 0, 0, ?_⟩
          intro x hx
          have hx' : x 0 ≤ 0 := hx
          show max (0:ℝ) (x 0) = (∑ i : Fin 1, (0:ℝ) * x i) + 0
          simp only [zero_mul, Finset.sum_const_zero, add_zero]
          exact max_eq_left_iff.mpr hx'
      | true =>
          refine ⟨fun _ => 1, 0, ?_⟩
          intro x hx
          have hx' : (0:ℝ) ≤ x 0 := hx
          show max (0:ℝ) (x 0) = (∑ i : Fin 1, (1:ℝ) * x i) + 0
          simp only [one_mul, Fin.sum_univ_one, add_zero]
          exact max_eq_right_iff.mpr hx'
  -- Transport this membership across the assumed equality to `Agent031`'s CPWL.
  have hmemA : kink ∈ Agent031.CPWL 1 := by rw [hEq]; exact hmemB
  obtain ⟨-, m, T, hT⟩ := hmemA
  obtain ⟨i, ε, hεpos, hball⟩ := hT (fun _ => (0:ℝ))
  have heval : ∀ y : Fin 1 → ℝ,
      (T i).eval y 0 = (T i).A 0 0 * y 0 + (T i).bias 0 := by
    intro y
    show (∑ j : Fin 1, (T i).A 0 j * y j) + (T i).bias 0
        = (T i).A 0 0 * y 0 + (T i).bias 0
    rw [Fin.sum_univ_one]
  have hd : ∀ v : ℝ, dist (fun _ : Fin 1 => v) (fun _ : Fin 1 => (0:ℝ)) = |v| := by
    intro v; rw [dist_pi_const, Real.dist_eq, sub_zero]
  have hd1 : dist (fun _ : Fin 1 => (-(ε/2) : ℝ)) (fun _ : Fin 1 => (0:ℝ)) < ε := by
    rw [hd, abs_neg, abs_of_pos (show (0:ℝ) < ε/2 by linarith)]; linarith
  have hd2 : dist (fun _ : Fin 1 => (-(ε/4) : ℝ)) (fun _ : Fin 1 => (0:ℝ)) < ε := by
    rw [hd, abs_neg, abs_of_pos (show (0:ℝ) < ε/4 by linarith)]; linarith
  have hd3 : dist (fun _ : Fin 1 => (ε/2 : ℝ)) (fun _ : Fin 1 => (0:ℝ)) < ε := by
    rw [hd, abs_of_pos (show (0:ℝ) < ε/2 by linarith)]; linarith
  have h1 : max (0:ℝ) (-(ε/2)) = (T i).A 0 0 * (-(ε/2)) + (T i).bias 0 := by
    have hb := hball (fun _ : Fin 1 => (-(ε/2) : ℝ)) hd1
    rw [heval] at hb; exact hb
  have h2 : max (0:ℝ) (-(ε/4)) = (T i).A 0 0 * (-(ε/4)) + (T i).bias 0 := by
    have hb := hball (fun _ : Fin 1 => (-(ε/4) : ℝ)) hd2
    rw [heval] at hb; exact hb
  have h3 : max (0:ℝ) (ε/2) = (T i).A 0 0 * (ε/2) + (T i).bias 0 := by
    have hb := hball (fun _ : Fin 1 => (ε/2 : ℝ)) hd3
    rw [heval] at hb; exact hb
  rw [max_eq_left_iff.mpr (show -(ε/2) ≤ (0:ℝ) by linarith)] at h1
  rw [max_eq_left_iff.mpr (show -(ε/4) ≤ (0:ℝ) by linarith)] at h2
  rw [max_eq_right_iff.mpr (show (0:ℝ) ≤ ε/2 by linarith)] at h3
  -- Two negative-side points force the affine map to be identically 0 ...
  have ha0 : (T i).A 0 0 = 0 := by linarith
  have hc0 : (T i).bias 0 = 0 := by linarith
  -- ... which contradicts the positive-side point, where `kink` equals `ε / 2 ≠ 0`.
  rw [ha0, hc0] at h3
  linarith

/-
`statement` (SORRY). Using the argument behind `cpwl_ne`, `Agent031`'s own claim
`∀ n ≥ 3, CPWL n = ReLUn n (depthBound n)` is in fact FALSE under its own definitions:
e.g. at `n = 3`, `depthBound 3 = 2`, and `ReLUn 3 2` contains genuinely non-affine
functions (a single-hidden-layer ReLU unit), while `Agent031.CPWL 3` — by the same
connectedness argument used above — consists only of *globally* affine functions. So
the left side of the stated `Iff` is provably `False`.

Determining the right side requires knowing whether `Agent032`'s own claim (which,
since `Agent032`'s definitions are the faithful ones, is essentially the actual content
of Theorem 2 of the paper) is true. Proving that in general is the substantial
mathematical content of arXiv:2505.14338 itself and is out of scope for a single bridge
file: it needs both directions well beyond what is established here (that ReLU networks
are polyhedrally piecewise-linear, and the paper's matching depth upper bound). Without
resolving the right side we can conclude neither the `Iff` nor its negation, so this is
left as `sorry`.
-/
theorem statement :
    (∀ n, 3 ≤ n → Agent031.CPWL n = Agent031.ReLUn n (Agent031.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent032.CPWL n = Agent032.ReLUn n (Agent032.depthBound n)) := by
  sorry

end Bridge_031_032

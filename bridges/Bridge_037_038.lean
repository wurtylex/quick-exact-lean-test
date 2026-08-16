namespace Bridge_037_038

/-!
## Summary of findings

* `depth`: PROVED. Both agents write the depth bound as literally
  `Nat.ceil (Real.logb 3 ((n:ℝ) - 1)) + 1` (038's `⌈·⌉₊` is notation for `Nat.ceil`), so the
  two `depthBound` functions are definitionally equal.
* `cpwl`: REFUTED (`cpwl_ne`). Agent037's `CPWL` is a genuine polyhedral-subdivision
  definition (finite cover by polyhedra, `f` affine on each piece), while Agent038's `CPWL`
  demands *local* agreement with a single affine functional on a whole metric neighborhood of
  every point. The function `x ↦ max 0 (x 0)` is in the former (cover by the two halfspaces
  `x 0 ≤ 0` / `x 0 ≥ 0`) but not the latter: no single affine function can match it on any
  neighborhood of `0`, since arbitrarily close to `0` it takes both the `0` branch and the
  `x 0` branch.
* `relun`: PROVED. Agent037's `ReLUn` allows *at most* `k` hidden layers, Agent038's demands
  *exactly* `k`. These coincide via the padding trick `v = max 0 v - max 0 (-v)`, which lets
  any exactly-`k'` network be turned into an exactly-`(k'+1)` network computing the same
  function by prepending an "identity" layer built from two ReLUs. Combined with a
  representation-level translation between Agent037's `Matrix`-based `AffineMap` and
  Agent038's function-based `Affine` (they are definitionally the same data), this gives full
  set equality.
* `statement`: SORRY. Since `cpwl_ne` shows Agent037's and Agent038's `CPWL` are genuinely
  different sets (even restricted to n ≥ 3, since the counterexample only uses coordinate 0),
  the two rendering-equivalences `CPWL_n = ReLUn_n(depthBound n)` are not obviously
  equivalent to each other via a formal manipulation; resolving `statement` reduces to
  actually deciding the truth of Theorem 2 (or its negation) for at least one of the two
  specific encodings, which is the paper's real mathematical content and out of scope here.

Faithfulness verdict: **Agent037** is the more faithful rendering of Theorem 2. Its `CPWL` is
the standard polyhedral-subdivision notion of a CPWL function. Agent038's local-agreement
`CPWL` is a strictly different (and, on a connected domain, much more restrictive) notion:
`relu(x₀)` itself fails to be `CPWL038`, even though it is manifestly the piecewise-linear
"hinge" function that motivates the whole paper.
-/

/-! ### `depth` -/

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent037.depthBound n = Agent038.depthBound n := by
  simp only [Agent037.depthBound, Agent038.depthBound]

/-! ### `cpwl` : refuted -/

private lemma dist_const_fin1 (t : ℝ) :
    dist (fun _ : Fin 1 => t) (fun _ : Fin 1 => (0 : ℝ)) = |t| := by
  rw [dist_pi_const, Real.dist_eq, sub_zero]

theorem cpwl_ne : ∃ n, Agent037.CPWL n ≠ Agent038.CPWL n := by
  refine ⟨1, ?_⟩
  intro heq
  set f : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0) with hfdef
  have hmem037 : f ∈ Agent037.CPWL 1 := by
    refine ⟨continuous_const.max (continuous_apply 0), 2,
      ![{x : Fin 1 → ℝ | x 0 ≤ 0}, {x : Fin 1 → ℝ | 0 ≤ x 0}],
      ![(fun _ : Fin 1 → ℝ => (0 : ℝ)), (fun x : Fin 1 → ℝ => x 0)],
      ?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i
      · refine ⟨1, fun _ _ => (1 : ℝ), fun _ => 0, ?_⟩
        ext x
        simp only [Set.mem_setOf_eq, Matrix.cons_val_zero]
        constructor
        · intro h j
          fin_cases j
          simpa [Fin.sum_univ_one] using h
        · intro h
          have h0 := h 0
          simpa [Fin.sum_univ_one] using h0
      · refine ⟨1, fun _ _ => (-1 : ℝ), fun _ => 0, ?_⟩
        ext x
        simp only [Set.mem_setOf_eq, Matrix.cons_val_one, Matrix.cons_val_zero,
          Matrix.head_cons]
        constructor
        · intro h j
          fin_cases j
          simp only [Fin.sum_univ_one]
          linarith
        · intro h
          have h0 := h 0
          simp only [Fin.sum_univ_one] at h0
          linarith
    · intro i
      fin_cases i
      · exact ⟨fun _ => 0, 0, fun x => by simp⟩
      · exact ⟨fun _ => 1, 0, fun x => by simp [Fin.sum_univ_one]⟩
    · intro x
      rcases le_or_lt (x 0) 0 with h | h
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h.le⟩
    · intro i
      fin_cases i
      · intro x hx
        simp only [Matrix.cons_val_zero, Set.mem_setOf_eq] at hx
        show max (0 : ℝ) (x 0) = 0
        exact max_eq_left_iff.mpr hx
      · intro x hx
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons,
          Set.mem_setOf_eq] at hx
        show max (0 : ℝ) (x 0) = x 0
        exact max_eq_right_iff.mpr hx
  have hmem038 : f ∈ Agent038.CPWL 1 := by rw [← heq]; exact hmem037
  obtain ⟨_, r, a, haff, hloc⟩ := hmem038
  obtain ⟨i, ε, hε, hmatch⟩ := hloc (fun _ : Fin 1 => (0 : ℝ))
  obtain ⟨coef, b, hab⟩ := haff i
  have hai : ∀ y : Fin 1 → ℝ, a i y = coef 0 * y 0 + b := by
    intro y
    rw [hab y, Fin.sum_univ_one]
  have key : ∀ t : ℝ, 0 < t → t < ε → b = t / 2 := by
    intro t ht htε
    have hd1 : dist (fun _ : Fin 1 => t) (fun _ : Fin 1 => (0 : ℝ)) < ε := by
      rw [dist_const_fin1, abs_of_pos ht]; exact htε
    have hd2 : dist (fun _ : Fin 1 => -t) (fun _ : Fin 1 => (0 : ℝ)) < ε := by
      rw [dist_const_fin1, abs_of_neg (show (-t : ℝ) < 0 by linarith)]; linarith
    have h1 : f (fun _ : Fin 1 => t) = a i (fun _ : Fin 1 => t) := hmatch _ hd1
    have h2 : f (fun _ : Fin 1 => -t) = a i (fun _ : Fin 1 => -t) := hmatch _ hd2
    simp only [hfdef, hai] at h1 h2
    have hm1 : max (0 : ℝ) t = t := max_eq_right_iff.mpr ht.le
    have hm2 : max (0 : ℝ) (-t) = 0 := max_eq_left_iff.mpr (by linarith)
    rw [hm1] at h1
    rw [hm2, mul_neg] at h2
    linarith
  have hb1 := key (ε / 2) (by linarith) (by linarith)
  have hb2 := key (ε / 3) (by linarith) (by linarith)
  linarith

/-! ### `relun` : proved -/

/-- Translate a matrix-based `AffineMap` (Agent037) evaluation into a function-based `Affine`
(Agent038) evaluation; these are the same data, `Matrix (Fin b) (Fin a) ℝ` being definitionally
`Fin b → Fin a → ℝ`. -/
private lemma eval_eq {a b : ℕ} (W : Fin b → Fin a → ℝ) (c : Fin b → ℝ) (x : Fin a → ℝ) :
    Agent037.AffineMap.eval (⟨W, c⟩ : Agent037.AffineMap a b) x
      = Agent038.Affine.apply (⟨W, c⟩ : Agent038.Affine a b) x := by
  funext i
  simp [Agent037.AffineMap.eval, Agent038.Affine.apply, Matrix.mulVec, Matrix.dotProduct,
    Pi.add_apply]

private lemma equiv037_038 : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent037.computesReLU k n f ↔ Agent038.ComputesHidden k n f := by
  intro k
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨T, hT⟩
      refine ⟨⟨T.A, T.c⟩, ?_⟩
      funext x
      have h := hT x
      rw [h]
      exact congrFun (eval_eq T.A T.c x) 0
    · rintro ⟨T, hT⟩
      refine ⟨⟨T.W, T.c⟩, ?_⟩
      intro x
      have h : f x = T.apply x 0 := congrFun hT x
      rw [h]
      exact (congrFun (eval_eq T.W T.c x) 0).symm
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, T, g, hg, hfeq⟩
      refine ⟨m, ⟨T.A, T.c⟩, g, (ih m g).mp hg, ?_⟩
      funext x
      have h := hfeq x
      rw [h]
      congr 1
      funext j
      have e := congrFun (eval_eq T.A T.c x) j
      simp only [Agent037.reluVec, Agent038.reluVec, Agent037.relu, Agent038.reluScalar]
      rw [e]
    · rintro ⟨m, T, g, hg, hfeq⟩
      refine ⟨m, ⟨T.W, T.c⟩, g, (ih m g).mpr hg, ?_⟩
      intro x
      have h : f x = g (Agent038.reluVec (Agent038.Affine.apply T x)) := congrFun hfeq x
      rw [h]
      congr 1
      funext j
      have e := congrFun (eval_eq T.W T.c x) j
      simp only [Agent037.reluVec, Agent038.reluVec, Agent037.relu, Agent038.reluScalar]
      rw [e]

/-- The identity on `ℝ` can be realized by two ReLUs: `v = max 0 v - max 0 (-v)`. -/
private lemma relu_diff (v : ℝ) : max (0 : ℝ) v - max (0 : ℝ) (-v) = v := by
  rcases le_total (0 : ℝ) v with h | h
  · rw [max_eq_right_iff.mpr h, max_eq_left_iff.mpr (by linarith : -v ≤ 0)]
    ring
  · rw [max_eq_left_iff.mpr h, max_eq_right_iff.mpr (by linarith : (0 : ℝ) ≤ -v)]
    ring

/-- Prepend an "identity-simulating" layer (via `relu_diff`) in front of a depth-`1` affine
map, doubling the hidden width. -/
private def padAffine {n : ℕ} (T : Agent038.Affine n 1) : Agent038.Affine n 2 where
  W := ![T.W 0, fun j => -(T.W 0 j)]
  c := ![T.c 0, -(T.c 0)]

/-- Combine the two padded coordinates back via subtraction. -/
private def padCombine : Agent038.Affine 2 1 where
  W := fun _ => ![(1 : ℝ), -1]
  c := fun _ => 0

private def padG (y : Fin 2 → ℝ) : ℝ := y 0 - y 1

private lemma padAffine_apply_zero {n : ℕ} (T : Agent038.Affine n 1) (x : Fin n → ℝ) :
    (padAffine T).apply x 0 = T.apply x 0 := by
  simp only [padAffine, Agent038.Affine.apply, Matrix.cons_val_zero]

private lemma padAffine_apply_one {n : ℕ} (T : Agent038.Affine n 1) (x : Fin n → ℝ) :
    (padAffine T).apply x 1 = -(T.apply x 0) := by
  have step1 : (Finset.univ.sum fun j => -(T.W 0 j) * x j)
      = Finset.univ.sum fun j => -(T.W 0 j * x j) :=
    Finset.sum_congr rfl (fun j _ => by ring)
  have hsum : (Finset.univ.sum fun j => -(T.W 0 j) * x j)
      = -(Finset.univ.sum fun j => T.W 0 j * x j) := by
    rw [step1, Finset.sum_neg_distrib]
  simp only [padAffine, Agent038.Affine.apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  rw [hsum]
  ring

private lemma padCombine_apply (y : Fin 2 → ℝ) : padCombine.apply y 0 = y 0 - y 1 := by
  simp only [padCombine, Agent038.Affine.apply, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]
  ring

private lemma padG_computesHidden : Agent038.ComputesHidden 0 2 padG := by
  refine ⟨padCombine, ?_⟩
  funext y
  show y 0 - y 1 = padCombine.apply y 0
  rw [padCombine_apply]

/-- Any function computable with exactly `k` hidden layers is also computable with exactly
`k + 1` hidden layers (pad with an identity-simulating layer). -/
private lemma pad_succ : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent038.ComputesHidden k n f → Agent038.ComputesHidden (k + 1) n f := by
  intro k
  induction k with
  | zero =>
    intro n f hf
    obtain ⟨T, hT⟩ := hf
    refine ⟨2, padAffine T, padG, padG_computesHidden, ?_⟩
    funext x
    have hfx : f x = T.apply x 0 := congrFun hT x
    have e0 := padAffine_apply_zero T x
    have e1 := padAffine_apply_one T x
    rw [hfx]
    show T.apply x 0 = padG (Agent038.reluVec ((padAffine T).apply x))
    simp only [padG, Agent038.reluVec, Agent038.reluScalar]
    rw [e0, e1]
    exact (relu_diff (T.apply x 0)).symm
  | succ k ih =>
    intro n f hf
    obtain ⟨m, T, g, hg, hfeq⟩ := hf
    exact ⟨m, T, g, ih m g hg, hfeq⟩

private lemma pad_add : ∀ (d k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent038.ComputesHidden k n f → Agent038.ComputesHidden (k + d) n f := by
  intro d
  induction d with
  | zero => intro k n f h; simpa using h
  | succ d ih =>
    intro k n f h
    have h1 := ih k n f h
    have h2 := pad_succ (k + d) n f h1
    have heq : k + (d + 1) = (k + d) + 1 := by omega
    rw [heq]
    exact h2

private lemma pad_le (k' k n : ℕ) (f : (Fin n → ℝ) → ℝ) (hk : k' ≤ k) :
    Agent038.ComputesHidden k' n f → Agent038.ComputesHidden k n f := by
  obtain ⟨d, hd⟩ := Nat.le.dest hk
  intro h
  have h2 := pad_add d k' n f h
  rwa [hd] at h2

theorem relun (n k : ℕ) : Agent037.ReLUn n k = Agent038.ReLUn n k := by
  ext f
  simp only [Agent037.ReLUn, Agent038.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k', hk', hf⟩
    exact pad_le k' k n f hk' ((equiv037_038 k' n f).mp hf)
  · intro hf
    exact ⟨k, le_refl k, (equiv037_038 k n f).mpr hf⟩

/-! ### `statement` -/

-- `cpwl_ne` shows Agent037.CPWL and Agent038.CPWL are genuinely different sets (the
-- counterexample `x ↦ max 0 (x 0)` only needs one coordinate, so it works for every n ≥ 3
-- too, not just n = 1). Consequently the two rendering-equivalences
-- `CPWL_n = ReLUn_n(depthBound n)` for Agent037 and Agent038 are propositions about
-- genuinely different `CPWL` predicates, and there is no formal shortcut (via `relun`/`depth`
-- alone) that identifies their truth values: resolving the iff one way or the other amounts
-- to deciding the truth of Theorem 2 itself (or its negation) for at least one of the two
-- specific encodings, i.e. redoing the paper's real mathematical content. That is out of
-- scope for this bridge, so this obligation is left as `sorry`.
theorem statement :
    (∀ n, 3 ≤ n → Agent037.CPWL n = Agent037.ReLUn n (Agent037.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent038.CPWL n = Agent038.ReLUn n (Agent038.depthBound n)) := by
  sorry

end Bridge_037_038

namespace Bridge_038_039

/-!
## Summary

Agent038 and Agent039 make essentially the same modelling choices:

* `Affine`/`AffineMap` are the same data (a "matrix" of weights and a bias vector,
  applied by the same `∑ + c` formula) — Agent038 stores the weights as a bare function
  `Fin b → Fin a → ℝ`, Agent039 stores them as a `Matrix (Fin b) (Fin a) ℝ` (which is
  definitionally the same type). `reluVec`/`reluScalar` vs. `reluVec`/`relu` are the same
  `max 0 ·` applied componentwise.
* `ComputesHidden`/`NetProp` are recursive predicates with the *same* shape, peeling off
  the first affine layer at each step. The only real difference: `Agent038.ReLUn n k`
  requires *exactly* `k` hidden layers, while `Agent039.ReLUn n k` requires *at most* `k`.
  These sets coincide via the padding trick `x = ReLU x - ReLU (-x)` flagged in the spec;
  we prove that trick below (`netProp_succ`/`netProp_mono`) and combine it with a
  translation lemma between the two recursive encodings (`computesHidden_iff_netProp`) to
  get full equality of `ReLUn`, not just an inclusion.
* `CPWL` is the same "continuous, and every point has a neighborhood on which `f` agrees
  with one of finitely many affine functionals" condition (family (b) in the spec) in both
  files, just packaged differently (Agent038 uses `Fin r`-indexed families and `ε`-balls,
  Agent039 uses arbitrary `Fintype`-indexed families and open sets); these repackage into
  each other directly.
* `depthBound` is the literal same term in both files.

All four obligations are **PROVED**.
-/

/-! ### Translating between `Agent038.Affine`/`Agent039.AffineMap` -/

/-- Convert an `Agent038.Affine` to an `Agent039.AffineMap` with the same action. -/
def toAffineMap {a b : ℕ} (T : Agent038.Affine a b) : Agent039.AffineMap a b :=
  ⟨Matrix.of T.W, T.c⟩

theorem toAffineMap_eval {a b : ℕ} (T : Agent038.Affine a b) (x : Fin a → ℝ) :
    (toAffineMap T).eval x = T.apply x := by
  funext i
  simp [Agent039.AffineMap.eval, toAffineMap, Agent038.Affine.apply, Matrix.mulVec,
    Matrix.dotProduct, Matrix.of_apply, Pi.add_apply]

/-- Convert an `Agent039.AffineMap` to an `Agent038.Affine` with the same action. -/
def ofAffineMap {a b : ℕ} (T : Agent039.AffineMap a b) : Agent038.Affine a b :=
  ⟨fun i j => T.A i j, T.c⟩

theorem ofAffineMap_eval {a b : ℕ} (T : Agent039.AffineMap a b) (x : Fin a → ℝ) :
    (ofAffineMap T).apply x = T.eval x := by
  funext i
  simp [Agent038.Affine.apply, ofAffineMap, Agent039.AffineMap.eval, Matrix.mulVec,
    Matrix.dotProduct, Pi.add_apply]

theorem reluVec_eq {m : ℕ} (v : Fin m → ℝ) : Agent038.reluVec v = Agent039.reluVec v := by
  funext i
  simp [Agent038.reluVec, Agent038.reluScalar, Agent039.reluVec, Agent039.relu]

/-- `Agent038.ComputesHidden` and `Agent039.NetProp` are the same "exactly `k` hidden
layers" predicate, just transported across the (field-for-field identical)
`Affine`/`AffineMap` structures. -/
theorem computesHidden_iff_netProp :
    ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
      Agent038.ComputesHidden k n f ↔ Agent039.NetProp n k f := by
  intro k
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨T, hT⟩
      refine ⟨toAffineMap T, fun x => ?_⟩
      simp only [hT, toAffineMap_eval]
    · rintro ⟨w, hw⟩
      refine ⟨ofAffineMap w, funext fun x => ?_⟩
      simp only [hw, ofAffineMap_eval]
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, T, g, hg, hf⟩
      refine ⟨m, toAffineMap T, g, (ih m g).mp hg, fun x => ?_⟩
      simp only [hf, toAffineMap_eval, reluVec_eq]
    · rintro ⟨m, T, g, hg, hf⟩
      refine ⟨m, ofAffineMap T, g, (ih m g).mpr hg, funext fun x => ?_⟩
      simp only [hf, ofAffineMap_eval, ← reluVec_eq]

/-! ### The padding lemma

`Agent038.ReLUn n k` means "exactly `k` hidden layers"; `Agent039.ReLUn n k` means "at
most `k` hidden layers". These coincide because a network with fewer hidden layers can
always be padded up: add one more hidden layer that duplicates its input as
`(x, -x)`, applies `ReLU` (giving `(ReLU x, ReLU(-x))`), and then recombines via the
identity `x = ReLU x - ReLU (-x)`. -/

/-- Precompose an `Agent039.AffineMap`. -/
def composeAffine {n' n b : ℕ} (w : Agent039.AffineMap n b) (B : Agent039.AffineMap n' n) :
    Agent039.AffineMap n' b :=
  ⟨w.A * B.A, w.A.mulVec B.c + w.c⟩

theorem composeAffine_eval {n' n b : ℕ} (w : Agent039.AffineMap n b) (B : Agent039.AffineMap n' n)
    (x : Fin n' → ℝ) :
    (composeAffine w B).eval x = w.eval (B.eval x) := by
  simp only [composeAffine, Agent039.AffineMap.eval, Matrix.mulVec_add, Matrix.mulVec_mulVec]
  abel

/-- Precomposing a `k`-hidden-layer network with an affine map yields a `k`-hidden-layer
network on the new domain: only the first affine layer needs to change. -/
theorem netProp_comp_affine {n n' : ℕ} (B : Agent039.AffineMap n' n) :
    ∀ (k : ℕ) (f : (Fin n → ℝ) → ℝ), Agent039.NetProp n k f →
      Agent039.NetProp n' k (fun x => f (B.eval x)) := by
  intro k
  cases k with
  | zero =>
    rintro f ⟨w, hw⟩
    exact ⟨composeAffine w B, fun x => by
      simp only [composeAffine_eval]; exact hw (B.eval x)⟩
  | succ k =>
    rintro f ⟨m, T, h, hh, hf⟩
    exact ⟨m, composeAffine T B, h, hh, fun x => by
      simp only [composeAffine_eval]; exact hf (B.eval x)⟩

/-- The key scalar identity behind the padding trick. -/
theorem relu_sub_relu_neg (x : ℝ) : max 0 x - max 0 (-x) = x := by
  rcases le_total 0 x with h | h
  · rw [max_eq_right_iff.mpr h, max_eq_left_iff.mpr (by linarith : (-x) ≤ 0)]
    ring
  · rw [max_eq_left_iff.mpr h, max_eq_right_iff.mpr (by linarith : (0:ℝ) ≤ -x)]
    ring

/-- The "duplicate and negate" affine map `x ↦ (x, -x) : ℝ^n → ℝ^{n+n}`. -/
def dupNeg (n : ℕ) : Agent039.AffineMap n (n + n) :=
  ⟨Matrix.of (Fin.append (fun i j : Fin n => if i = j then (1:ℝ) else 0)
                          (fun i j : Fin n => if i = j then (-1:ℝ) else 0)), 0⟩

theorem dupNeg_eval (n : ℕ) (x : Fin n → ℝ) :
    (dupNeg n).eval x = Fin.append x (-x) := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;>
    simp only [Agent039.AffineMap.eval, dupNeg, Pi.add_apply, Pi.zero_apply, add_zero,
      Matrix.mulVec, Matrix.dotProduct, Matrix.of_apply, Fin.append_left, Fin.append_right,
      ite_mul, one_mul, zero_mul, neg_one_mul, Fintype.sum_ite_eq, Pi.neg_apply]

/-- The "recombine" affine map `(u, v) ↦ u - v : ℝ^{n+n} → ℝ^n`. -/
def combine (n : ℕ) : Agent039.AffineMap (n + n) n :=
  ⟨Matrix.of (fun i => Fin.append (fun j : Fin n => if i = j then (1:ℝ) else 0)
                                   (fun j : Fin n => if i = j then (-1:ℝ) else 0)), 0⟩

theorem combine_eval (n : ℕ) (u v : Fin n → ℝ) (i : Fin n) :
    (combine n).eval (Fin.append u v) i = u i - v i := by
  simp only [Agent039.AffineMap.eval, combine, Pi.add_apply, Pi.zero_apply, add_zero,
    Matrix.mulVec, Matrix.dotProduct, Matrix.of_apply, Fin.sum_univ_add, Fin.append_left,
    Fin.append_right, ite_mul, one_mul, zero_mul, neg_one_mul, Fintype.sum_ite_eq,
    sub_eq_add_neg]

theorem reluVec_append {n : ℕ} (u v : Fin n → ℝ) :
    Agent039.reluVec (Fin.append u v) = Fin.append (Agent039.reluVec u) (Agent039.reluVec v) := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;>
    simp only [Agent039.reluVec, Agent039.relu, Fin.append_left, Fin.append_right]

/-- Recombining after a duplicate-negate-then-`ReLU` layer recovers the identity. -/
theorem combine_reluVec_dupNeg (n : ℕ) (x : Fin n → ℝ) :
    (combine n).eval (Agent039.reluVec ((dupNeg n).eval x)) = x := by
  rw [dupNeg_eval, reluVec_append]
  funext i
  rw [combine_eval]
  simp [Agent039.reluVec, Agent039.relu, Pi.neg_apply, relu_sub_relu_neg]

/-- Padding: any `k`-hidden-layer network can be re-expressed with one more hidden
layer. -/
theorem netProp_succ {n : ℕ} (k : ℕ) (f : (Fin n → ℝ) → ℝ) (hf : Agent039.NetProp n k f) :
    Agent039.NetProp n (k + 1) f :=
  ⟨n + n, dupNeg n, fun y => f ((combine n).eval y), netProp_comp_affine (combine n) k f hf,
    fun x => by simp only [combine_reluVec_dupNeg]⟩

/-- Padding, iterated: any `k`-hidden-layer network can be re-expressed with any
`k' ≥ k` hidden layers. -/
theorem netProp_mono {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    ∀ (k k' : ℕ), k ≤ k' → Agent039.NetProp n k f → Agent039.NetProp n k' f := by
  intro k k' hk
  induction k', hk using Nat.le_induction with
  | base => intro hf; exact hf
  | succ k' hk' ih => intro hf; exact netProp_succ k' f (ih hf)

/-! ### The four bridge obligations -/

theorem cpwl (n : ℕ) : Agent038.CPWL n = Agent039.CPWL n := by
  ext f
  constructor
  · rintro ⟨hf, r, a, ha, hloc⟩
    refine ⟨hf, Fin r, inferInstance, fun i => (ha i).choose, fun i => (ha i).choose_spec.choose,
      fun x => ?_⟩
    obtain ⟨i, ε, hε, hi⟩ := hloc x
    refine ⟨i, Metric.ball x ε, Metric.isOpen_ball, Metric.mem_ball_self hε, fun y hy => ?_⟩
    have hspec := (ha i).choose_spec.choose_spec
    rw [hi y (Metric.mem_ball.mp hy), hspec y]
  · rintro ⟨hf, ι, hι, w, b, hloc⟩
    refine ⟨hf, Fintype.card ι,
      fun k => fun x => (∑ j, w ((Fintype.equivFin ι).symm k) j * x j)
        + b ((Fintype.equivFin ι).symm k),
      fun k => ⟨w ((Fintype.equivFin ι).symm k), b ((Fintype.equivFin ι).symm k),
        fun x => rfl⟩,
      fun x => ?_⟩
    obtain ⟨i, U, hU, hxU, hi⟩ := hloc x
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hU x hxU
    refine ⟨Fintype.equivFin ι i, ε, hε, fun y hy => ?_⟩
    rw [hi y (hsub (Metric.mem_ball.mpr hy))]
    simp

theorem relun (n k : ℕ) : Agent038.ReLUn n k = Agent039.ReLUn n k := by
  ext f
  constructor
  · intro hf
    exact ⟨k, le_refl k, (computesHidden_iff_netProp k n f).mp hf⟩
  · rintro ⟨j, hj, hf⟩
    exact (computesHidden_iff_netProp k n f).mpr (netProp_mono f j k hj hf)

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent038.depthBound n = Agent039.depthBound n := rfl

theorem statement :
    (∀ n, 3 ≤ n → Agent038.CPWL n = Agent038.ReLUn n (Agent038.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent039.CPWL n = Agent039.ReLUn n (Agent039.depthBound n)) := by
  constructor
  · intro h n hn
    rw [← cpwl n, ← depth n hn, ← relun n (Agent038.depthBound n)]
    exact h n hn
  · intro h n hn
    rw [cpwl n, depth n hn, relun n (Agent039.depthBound n)]
    exact h n hn

end Bridge_038_039

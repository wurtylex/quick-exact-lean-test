namespace Bridge_044_045

/-!
Agent044 and Agent045 use essentially the same modelling choices for Theorem 2:

* `AffineMap`/`AffineTransform` are the same structure (a matrix `A` and bias `c`),
  with the same evaluation formula, just phrased once via `Matrix.mulVec` (044) and
  once via an explicit `∑` (045).
* `NetComputes`/`ComputesWithHidden` are the same recursive "exactly `k` hidden
  layers" predicate, except Agent044 additionally requires the hidden-layer width
  `m` to be positive (`0 < m`) at each step, while Agent045 places no such
  constraint. A `0`-width hidden layer forces the represented function to be a
  constant (its input has the unique type `Fin 0 → ℝ`), and constants are always
  representable with `0` hidden layers, so the two "at most `k` hidden layers"
  classes `ReLUn` still coincide; we prove this via a padding/collapsing lemma.
* `CPWL` is the same "continuous and locally equal to a member of a finite affine
  family" condition in both files, just packaged differently (044 stores the
  family as arrays `A`,`b`; 045 stores it as a family of functions each satisfying
  `IsAffineFun`).
* `depthBound` is the literal same term in both files.
-/

/-- Convert an `Agent044.AffineMap` to an `Agent045.AffineTransform` with the same data. -/
def toAT {a b : ℕ} (T : Agent044.AffineMap a b) : Agent045.AffineTransform a b :=
  ⟨T.A, T.c⟩

theorem toAT_eval {a b : ℕ} (T : Agent044.AffineMap a b) (x : Fin a → ℝ) :
    (toAT T).eval x = T.eval x := by
  funext i
  simp [toAT, Agent045.AffineTransform.eval, Agent044.AffineMap.eval, Matrix.mulVec,
    Matrix.dotProduct, Pi.add_apply]

/-- Convert an `Agent045.AffineTransform` to an `Agent044.AffineMap` with the same data. -/
def toAM {a b : ℕ} (T : Agent045.AffineTransform a b) : Agent044.AffineMap a b :=
  ⟨T.A, T.c⟩

theorem toAM_eval {a b : ℕ} (T : Agent045.AffineTransform a b) (x : Fin a → ℝ) :
    (toAM T).eval x = T.eval x := by
  funext i
  simp [toAM, Agent045.AffineTransform.eval, Agent044.AffineMap.eval, Matrix.mulVec,
    Matrix.dotProduct, Pi.add_apply]

theorem reluVec_eq {m : ℕ} (x : Fin m → ℝ) :
    Agent044.reluVec x = Agent045.reluVec x := by
  funext i
  simp [Agent044.reluVec, Agent044.relu, Agent045.reluVec, Agent045.relu]

/-- Every Agent044-style exact-`k`-hidden-layer network (positive widths only) is also
an Agent045-style exact-`k`-hidden-layer network (no positivity constraint on widths):
dropping a hypothesis only weakens the existential. -/
theorem netComputes_to_computesWithHidden :
    ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
      Agent044.NetComputes n k f → Agent045.ComputesWithHidden k n f := by
  intro k
  induction k with
  | zero =>
      intro n f hnc
      obtain ⟨T, hT⟩ := hnc
      exact ⟨toAT T, fun x => by rw [hT, toAT_eval]⟩
  | succ k ih =>
      intro n f hnc
      obtain ⟨m, _hm, T, g, hg, hf⟩ := hnc
      exact ⟨m, toAT T, g, ih m g hg, fun x => by rw [hf, toAT_eval, reluVec_eq]⟩

/-- Conversely, every Agent045-style exact-`k`-hidden-layer network is representable as
an Agent044-style network with *at most* `k` hidden layers: whenever Agent045 uses a
`0`-width hidden layer, the represented function collapses to a constant (its argument
at that point has the singleton type `Fin 0 → ℝ`), and a constant needs no hidden
layers at all in Agent044's sense. -/
theorem computesWithHidden_to_netComputes :
    ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
      Agent045.ComputesWithHidden k n f → ∃ k' ≤ k, Agent044.NetComputes n k' f := by
  intro k
  induction k with
  | zero =>
      intro n f hcw
      obtain ⟨T, hT⟩ := hcw
      exact ⟨0, le_refl 0, toAM T, fun x => by rw [hT, toAM_eval]⟩
  | succ k ih =>
      intro n f hcw
      obtain ⟨m, T0, g, hg, hfx⟩ := hcw
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0
        have hconst : ∀ x : Fin n → ℝ, f x = f (fun _ : Fin n => (0 : ℝ)) := by
          intro x
          have hE : Agent045.reluVec (T0.eval x) =
              Agent045.reluVec (T0.eval (fun _ : Fin n => (0 : ℝ))) := by
            funext i
            exact i.elim0
          rw [hfx, hE, ← hfx]
        refine ⟨0, Nat.zero_le _, ⟨(0 : Matrix (Fin 1) (Fin n) ℝ),
          fun _ => f (fun _ : Fin n => (0 : ℝ))⟩, ?_⟩
        intro x
        rw [hconst x]
        simp [Agent044.AffineMap.eval, Matrix.mulVec, Matrix.dotProduct, Pi.add_apply,
          Pi.zero_apply, Matrix.zero_apply]
      · obtain ⟨k', hk', hgc⟩ := ih m g hg
        refine ⟨k' + 1, Nat.succ_le_succ hk', m, hmpos, toAM T0, g, hgc, ?_⟩
        intro x
        rw [hfx, toAM_eval, reluVec_eq]

theorem cpwl (n : ℕ) : Agent044.CPWL n = Agent045.CPWL n := by
  ext f
  simp only [Agent044.CPWL, Agent045.CPWL, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hf, N, A, b, hloc⟩
    refine ⟨hf, N, (fun i y => (∑ j, A i j * y j) + b i), ?_, ?_⟩
    · intro i
      exact ⟨A i, b i, fun x => rfl⟩
    · intro x
      obtain ⟨i, hi⟩ := hloc x
      exact ⟨i, hi⟩
  · rintro ⟨hf, m, g, hag, hloc⟩
    choose a b hab using hag
    refine ⟨hf, m, a, b, ?_⟩
    intro x
    obtain ⟨i, hi⟩ := hloc x
    refine ⟨i, ?_⟩
    filter_upwards [hi] with y hy
    exact hy.trans (hab i y)

theorem relun (n k : ℕ) : Agent044.ReLUn n k = Agent045.ReLUn n k := by
  ext f
  simp only [Agent044.ReLUn, Agent045.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k', hk', hnc⟩
    exact ⟨k', hk', netComputes_to_computesWithHidden k' n f hnc⟩
  · rintro ⟨k', hk', hcw⟩
    obtain ⟨k'', hk'', hnc⟩ := computesWithHidden_to_netComputes k' n f hcw
    exact ⟨k'', hk''.trans hk', hnc⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent044.depthBound n = Agent045.depthBound n := rfl

theorem statement :
    (∀ n, 3 ≤ n → Agent044.CPWL n = Agent044.ReLUn n (Agent044.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent045.CPWL n = Agent045.ReLUn n (Agent045.depthBound n)) := by
  constructor
  · intro h n hn
    rw [← cpwl n, ← depth n hn, ← relun n (Agent044.depthBound n)]
    exact h n hn
  · intro h n hn
    rw [cpwl n, depth n hn, relun n (Agent045.depthBound n)]
    exact h n hn

end Bridge_044_045

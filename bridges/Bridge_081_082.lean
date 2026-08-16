namespace Bridge_081_082

/-- `depth`: both files spell the depth bound identically —
`⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1` — the `⌈·⌉₊` notation is just `Nat.ceil`, so the
two `depthBound`s are definitionally equal (noncomputability of `082`'s doesn't
affect kernel defeq). -/
theorem depth (n : ℕ) (hn : 3 ≤ n) :
    Agent081.depthBound n = Agent082.depthBound n := rfl

/-- `Agent081.Affine` and `Agent082.AffineMap'` are field-for-field identical
structures (`A : Matrix (Fin b) (Fin a) ℝ`, `c : Fin b → ℝ`), so they convert
back and forth with `eval` preserved definitionally. -/
def toB {a b : ℕ} (T : Agent081.Affine a b) : Agent082.AffineMap' a b := ⟨T.A, T.c⟩

def toA {a b : ℕ} (T : Agent082.AffineMap' a b) : Agent081.Affine a b := ⟨T.A, T.c⟩

theorem eval_toB {a b : ℕ} (T : Agent081.Affine a b) (x : Fin a → ℝ) :
    (toB T).eval x = T.eval x := rfl

theorem eval_toA {a b : ℕ} (T : Agent082.AffineMap' a b) (x : Fin a → ℝ) :
    (toA T).eval x = T.eval x := rfl

theorem reluVec_eq {m : ℕ} (v : Fin m → ℝ) :
    Agent081.reluVec v = Agent082.reluVec v := rfl

/-- The two recursive "network computes" predicates agree at every `n k f`: they
are literally the same recursion (peel an affine map, apply ReLU, recurse),
just phrased over the isomorphic affine-map structures above. -/
theorem net_iff : ∀ (n k : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent081.NetworkComputes n k f ↔ Agent082.NetComputes n k f
  | n, 0, f => by
      constructor
      · rintro ⟨T, hT⟩
        exact ⟨toB T, fun x => by rw [hT x, eval_toB]⟩
      · rintro ⟨T, hT⟩
        exact ⟨toA T, fun x => by rw [hT x, eval_toA]⟩
  | n, k + 1, f => by
      constructor
      · rintro ⟨m, T, g, hg, hf⟩
        refine ⟨m, toB T, g, (net_iff m k g).mp hg, fun x => ?_⟩
        rw [hf x, eval_toB, reluVec_eq]
      · rintro ⟨m, T, g, hg, hf⟩
        refine ⟨m, toA T, g, (net_iff m k g).mpr hg, fun x => ?_⟩
        rw [hf x, eval_toA, ← reluVec_eq]

theorem relun (n k : ℕ) : Agent081.ReLUn n k = Agent082.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨k', hk', hf⟩
    exact ⟨k', hk', (net_iff n k' f).mp hf⟩
  · rintro ⟨k', hk', hf⟩
    exact ⟨k', hk', (net_iff n k' f).mpr hf⟩

-- `cpwl`: `Agent081.CPWL` is a *polyhedral-subdivision* reading (a finite closed-
-- halfspace cover of ℝⁿ on which `f` is piecewise affine), while `Agent082.CPWL` is
-- a *local-agreement* reading (`∀ x, ∃ j`, `f` equals a fixed affine `g j` on a whole
-- neighbourhood of `x`). These are genuinely different: local-agreement fails at any
-- kink point (e.g. `x ↦ max 0 (x 0)` near `0`, a bona fide piecewise-linear function
-- under the polyhedral reading), so this is very likely a refutation. Proving the
-- non-membership rigorously needs neighbourhood-filter/metric-ball manipulation on
-- `Fin n → ℝ` that didn't fit the line budget for this link; left `sorry` rather than
-- risk an unreliable topology argument that can't be compile-checked here.
theorem cpwl (n : ℕ) : Agent081.CPWL n = Agent082.CPWL n := sorry

-- `statement`: would follow from `cpwl`/`relun`/`depth` all agreeing, but `cpwl` above
-- is unresolved (and is likely false per the discussion there), so there is no
-- established bridge between the two files' internal "theorem2 holds for all n"
-- claims; left `sorry`.
theorem statement :
    (∀ n, 3 ≤ n → Agent081.CPWL n = Agent081.ReLUn n (Agent081.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent082.CPWL n = Agent082.ReLUn n (Agent082.depthBound n)) := sorry

end Bridge_081_082

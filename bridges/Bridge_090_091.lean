namespace Bridge_090_091

/- `cpwl`: both `CPWL` defs are the same *kind* of thing (continuous + finite
polyhedral subdivision with affine agreement on each piece, family (a) from the
spec, not the dangerous "local agreement" family (b)), so the sets should be
equal. But Agent090 indexes pieces by `List (Halfspace n)` with a generic
`IsAffine` existential `(a, b)` pair, while Agent091 indexes by `Fin p` /
`Fin (m i)` with a concrete `AffineFun n 1` pair. Turning one indexing/affine
representation into the other needs real (bidirectional) reindexing plumbing
that does not fit the line budget, so this is left honest. -/
theorem cpwl (n : ℕ) : Agent090.CPWL n = Agent091.CPWL n := sorry

/- `relun`: both sides read "at most k hidden layers" (matching modelling
choices), and `Network`/`NetFunc` are the same recursive shape. The gap is
that Agent090's affine maps carry a `Matrix (Fin b) (Fin a) ℝ`
(`AffineMap`) while Agent091's carry a bare `Fin b → Fin a → ℝ`
(`AffineFun`); bridging them needs unfolding Mathlib's `Matrix.mulVec` /
`dotProduct` API precisely, which cannot be checked without compiling, so we
leave this honest rather than risk a bogus proof. -/
theorem relun (n k : ℕ) : Agent090.ReLUn n k = Agent091.ReLUn n k := sorry

/-- `depth`: for `n ≥ 3`, both formulas reduce to comparing
`⌈Real.logb 3 (m:ℝ)⌉₊` against `Nat.clog 3 m` for `m := n - 1 ≥ 2`, and these
agree by the defining `Nat.clog` bounds `Nat.le_pow_clog` /
`Nat.pow_pred_clog_lt_self` together with `Real.log` monotonicity. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) :
    Agent090.depthBound n = Agent091.depthBound n := by
  have hn1 : (1 : ℕ) ≤ n := by omega
  have hcast : (n : ℝ) - 1 = ((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hn1, Nat.cast_one]
  unfold Agent090.depthBound Agent091.depthBound
  rw [hcast]
  congr 1
  set m : ℕ := n - 1 with hm_def
  have hm2 : 2 ≤ m := by omega
  have hm1 : 1 < m := by omega
  have hb : (1 : ℕ) < 3 := by norm_num
  set k : ℕ := Nat.clog 3 m with hk_def
  have hkpos : 0 < k := Nat.clog_pos hb hm1
  have hub : m ≤ 3 ^ k := Nat.le_pow_clog hb m
  have hlb : (3 : ℕ) ^ (k - 1) < m := by
    have h := Nat.pow_pred_clog_lt_self hb hm1
    have hpe : (Nat.clog 3 m).pred = Nat.clog 3 m - 1 := by omega
    rwa [hpe] at h
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have h3pos : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hub' : Real.logb 3 (m : ℝ) ≤ (k : ℝ) := by
    rw [← Real.log_div_log, div_le_iff₀ h3pos]
    have hle : Real.log (m : ℝ) ≤ Real.log ((3 : ℝ) ^ k) :=
      Real.log_le_log hmR (by exact_mod_cast hub)
    rw [Real.log_pow] at hle
    nlinarith [hle, mul_comm (k : ℝ) (Real.log 3)]
  have hlb' : ((k - 1 : ℕ) : ℝ) < Real.logb 3 (m : ℝ) := by
    rw [← Real.log_div_log, lt_div_iff₀ h3pos]
    have hlt : Real.log ((3 : ℝ) ^ (k - 1)) < Real.log (m : ℝ) :=
      Real.log_lt_log (by positivity) (by exact_mod_cast hlb)
    rw [Real.log_pow] at hlt
    nlinarith [hlt, mul_comm ((k - 1 : ℕ) : ℝ) (Real.log 3)]
  exact (Nat.ceil_eq_iff hkpos.ne').mpr ⟨hlb', hub'⟩

/-- `statement`: a purely formal consequence of `cpwl`, `relun`, `depth` by
rewriting each side into the other; it does not use either agent's
`theorem2`. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent090.CPWL n = Agent090.ReLUn n (Agent090.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent091.CPWL n = Agent091.ReLUn n (Agent091.depthBound n)) := by
  constructor
  · intro h n hn
    rw [← cpwl n, h n hn, relun n (Agent090.depthBound n), depth n hn]
  · intro h n hn
    rw [cpwl n, h n hn, ← relun n (Agent091.depthBound n), ← depth n hn]

end Bridge_090_091

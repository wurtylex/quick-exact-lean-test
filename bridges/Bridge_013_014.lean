namespace Bridge_013_014

/-!
## Comparing `Agent013` and `Agent014`

Both files use the *same* encoding for `depthBound` (`Real.logb`/`Nat.ceil`), so `depth`
is immediate.

For `ReLUn`, `Agent013` reads it as "at most `k` hidden layers" (`∃ k' ≤ k, IsReLURep n k' f`)
while `Agent014` reads it as "exactly `k` hidden layers" (`IsReLUNetFun n k f`). These agree
because any network with `k' ≤ k` hidden layers can be padded to exactly `k` hidden layers
by prepending an extra layer that implements the identity via the standard ReLU trick
`x = relu x - relu (-x)`. We prove this padding lemma explicitly below (`pad`) and derive
`relun`.

For `CPWL`, `Agent013` uses a "local agreement" reading (type (b) from the task notes):
`f` agrees with *some* member of a fixed finite family of affine functions on a
neighbourhood of every point. `Agent014` uses a genuine finite polyhedral subdivision
(type (a)). These are *not* the same: the function `x ↦ max 0 (x 0)` is a genuine
(non-affine) CPWL function under the polyhedral reading, but it is *not* locally affine at
the origin (no single affine function can match it on a whole neighbourhood of `0`, since
its restriction to the `x 0`-axis is not affine near `0`). So `Agent013.CPWL` and
`Agent014.CPWL` disagree, and we prove `cpwl_ne`.

Since `Agent013.CPWL` is genuinely wrong (too restrictive) as a model of "continuous
piecewise linear", `Agent013`'s own version of Theorem 2 is false (the ReLU-representable
non-affine function above witnesses the failure at `n = 3`, since it needs only 1 hidden
layer). `Agent014`'s version of Theorem 2, on the other hand, is (modulo the "exactly k"
vs "at most k" issue we already resolve in `relun`) the actual hard theorem from the paper,
whose truth we cannot decide here. Hence `statement` genuinely requires resolving that open
direction and is left as `sorry` (see the comment there).
-/

/- ===================== `depth` ===================== -/

/-- Both files write the depth bound as `⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1`, using the same
`Nat.ceil` / `Real.logb`; the two definitions are syntactically identical modulo notation. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent013.depthBound n = Agent014.depthBound n := rfl

/- ===================== `cpwl_ne` ===================== -/

/-- The witness function: `x ↦ max 0 (x 0)` on `ℝ^1`, i.e. plain ReLU. -/
def witnessF : (Fin 1 → ℝ) → ℝ := fun x => max (0 : ℝ) (x 0)

theorem witnessF_continuous : Continuous witnessF :=
  continuous_const.max (continuous_apply 0)

/-! ### `witnessF` is a genuine (polyhedral) CPWL function for `Agent014` -/

/-- The "positive" piece: `f = x 0` on `{x 0 ≥ 0}`. -/
def piecePos : Agent014.PWLPiece 1 where
  aff := ⟨Matrix.of (fun _ _ => (1 : ℝ)), fun _ => 0⟩
  numConstraints := 1
  normal := fun _ _ => (-1 : ℝ)
  bound := fun _ => 0

/-- The "negative" piece: `f = 0` on `{x 0 ≤ 0}`. -/
def pieceNeg : Agent014.PWLPiece 1 where
  aff := ⟨Matrix.of (fun _ _ => (0 : ℝ)), fun _ => 0⟩
  numConstraints := 1
  normal := fun _ _ => (1 : ℝ)
  bound := fun _ => 0

def pieces14 : Bool → Agent014.PWLPiece 1
  | true => piecePos
  | false => pieceNeg

theorem pieces14_cover : (⋃ i, (pieces14 i).region) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  rcases le_total (0 : ℝ) (x 0) with h | h
  · refine Set.mem_iUnion.mpr ⟨true, ?_⟩
    show ∀ _ : Fin 1, ∑ i : Fin 1, (-1 : ℝ) * x i ≤ 0
    intro j
    rw [Fin.sum_univ_one]
    linarith
  · refine Set.mem_iUnion.mpr ⟨false, ?_⟩
    show ∀ _ : Fin 1, ∑ i : Fin 1, (1 : ℝ) * x i ≤ 0
    intro j
    rw [Fin.sum_univ_one]
    linarith

theorem pieces14_eq :
    ∀ i : Bool, ∀ x ∈ (pieces14 i).region, witnessF x = (pieces14 i).aff.eval x 0 := by
  intro i x hx
  cases i with
  | true =>
    have hx0 : (0 : ℝ) ≤ x 0 := by
      have h : (∑ j : Fin 1, (-1 : ℝ) * x j) ≤ 0 := hx 0
      rw [Fin.sum_univ_one] at h
      linarith
    show max (0 : ℝ) (x 0) = (∑ j : Fin 1, (1 : ℝ) * x j) + 0
    rw [Fin.sum_univ_one, one_mul, add_zero]
    exact max_eq_right_iff.mpr hx0
  | false =>
    have hx0 : x 0 ≤ (0 : ℝ) := by
      have h : (∑ j : Fin 1, (1 : ℝ) * x j) ≤ 0 := hx 0
      rw [Fin.sum_univ_one, one_mul] at h
      exact h
    show max (0 : ℝ) (x 0) = (∑ j : Fin 1, (0 : ℝ) * x j) + 0
    rw [Fin.sum_univ_one, zero_mul, add_zero]
    exact max_eq_left_iff.mpr hx0

theorem witnessF_mem_14 : witnessF ∈ Agent014.CPWL 1 :=
  ⟨witnessF_continuous, Bool, inferInstance, pieces14, pieces14_cover, pieces14_eq⟩

/-! ### `witnessF` is *not* a CPWL function for `Agent013` -/

/-- Basic algebraic fact: `witnessF` is not locally affine at `0`, checked directly via
three sample points (`0`, `ε/2`, `-ε/2`). -/
theorem witnessF_not_mem_013 : witnessF ∉ Agent013.CPWL 1 := by
  rintro ⟨-, r, g, hg⟩
  obtain ⟨i, ε, hε, hy⟩ := hg (0 : Fin 1 → ℝ)
  have heval : ∀ y : Fin 1 → ℝ,
      (g i).eval y 0 = (g i).A 0 0 * y 0 + (g i).c 0 := by
    intro y
    have step1 : (g i).eval y 0 = (g i).A.mulVec y 0 + (g i).c 0 := rfl
    have step2 : (g i).A.mulVec y 0 = ∑ j : Fin 1, (g i).A 0 j * y j := rfl
    rw [step1, step2, Fin.sum_univ_one]
  set y1 : Fin 1 → ℝ := fun _ => ε / 2 with hy1def
  set y2 : Fin 1 → ℝ := fun _ => -(ε / 2) with hy2def
  have hd0 : dist (0 : Fin 1 → ℝ) (0 : Fin 1 → ℝ) < ε := by rw [dist_self]; exact hε
  have hd1 : dist y1 (0 : Fin 1 → ℝ) < ε := by
    rw [dist_pi_lt_iff hε]
    intro b
    show dist (ε / 2 : ℝ) (0 : ℝ) < ε
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith : (0 : ℝ) < ε / 2)]
    linarith
  have hd2 : dist y2 (0 : Fin 1 → ℝ) < ε := by
    rw [dist_pi_lt_iff hε]
    intro b
    show dist (-(ε / 2) : ℝ) (0 : ℝ) < ε
    rw [Real.dist_eq, sub_zero, abs_of_neg (by linarith : (-(ε / 2) : ℝ) < 0)]
    linarith
  have e0 : (0 : ℝ) = (g i).A 0 0 * 0 + (g i).c 0 := by
    have h := hy 0 hd0
    rw [heval] at h
    have hw : witnessF (0 : Fin 1 → ℝ) = 0 := max_eq_right_iff.mpr (le_refl (0:ℝ))
    rw [hw] at h
    exact h
  have e1 : ε / 2 = (g i).A 0 0 * (ε / 2) + (g i).c 0 := by
    have h := hy y1 hd1
    rw [heval] at h
    have hw : witnessF y1 = ε / 2 := by
      show max (0 : ℝ) (ε / 2 : ℝ) = ε / 2
      exact max_eq_right_iff.mpr (by linarith)
    rw [hw] at h
    exact h
  have e2 : (0 : ℝ) = (g i).A 0 0 * (-(ε / 2)) + (g i).c 0 := by
    have h := hy y2 hd2
    rw [heval] at h
    have hw : witnessF y2 = 0 := by
      show max (0 : ℝ) (-(ε / 2) : ℝ) = 0
      exact max_eq_left_iff.mpr (by linarith)
    rw [hw] at h
    exact h
  rw [mul_zero, zero_add] at e0
  rw [← e0, add_zero] at e1
  rw [← e0, add_zero] at e2
  rw [mul_neg] at e2
  have hA0 : (g i).A 0 0 * (ε / 2) = 0 := by linarith
  rw [hA0] at e1
  linarith

theorem cpwl_ne : ∃ n, Agent013.CPWL n ≠ Agent014.CPWL n := by
  refine ⟨1, ?_⟩
  intro hEq
  have h14 : witnessF ∈ Agent014.CPWL 1 := witnessF_mem_14
  rw [← hEq] at h14
  exact witnessF_not_mem_013 h14

/- ===================== `relun` ===================== -/

/-! ### General helper: splitting a `dotProduct` along `Fin.append` -/

theorem dotProduct_append {p q : ℕ} (a : Fin p → ℝ) (b : Fin q → ℝ) (z : Fin (p + q) → ℝ) :
    (Fin.append a b) ⬝ᵥ z
      = a ⬝ᵥ (fun i => z (Fin.castAdd q i))
      + b ⬝ᵥ (fun i => z (Fin.natAdd p i)) := by
  show (∑ k : Fin (p + q), Fin.append a b k * z k)
      = (∑ i : Fin p, a i * z (Fin.castAdd q i)) + ∑ i : Fin q, b i * z (Fin.natAdd p i)
  rw [Fin.sum_univ_add]
  congr 1
  · exact Finset.sum_congr rfl (fun i _ => by rw [Fin.append_left])
  · exact Finset.sum_congr rfl (fun i _ => by rw [Fin.append_right])

/-! ### The "identity via ReLU" front layer: `x ↦ (x, -x)` -/

def padMat (n : ℕ) : Matrix (Fin (n + n)) (Fin n) ℝ :=
  Matrix.of (Fin.append (1 : Matrix (Fin n) (Fin n) ℝ) (-(1 : Matrix (Fin n) (Fin n) ℝ)))

theorem padMat_mulVec_castAdd (n : ℕ) (x : Fin n → ℝ) (i : Fin n) :
    (padMat n).mulVec x (Fin.castAdd n i) = x i := by
  have hrow : (padMat n) (Fin.castAdd n i) = (1 : Matrix (Fin n) (Fin n) ℝ) i := by
    show Fin.append (1 : Matrix (Fin n) (Fin n) ℝ) (-(1 : Matrix (Fin n) (Fin n) ℝ))
        (Fin.castAdd n i) = (1 : Matrix (Fin n) (Fin n) ℝ) i
    rw [Fin.append_left]
  calc (padMat n).mulVec x (Fin.castAdd n i)
      = (padMat n) (Fin.castAdd n i) ⬝ᵥ x := rfl
    _ = (1 : Matrix (Fin n) (Fin n) ℝ) i ⬝ᵥ x := by rw [hrow]
    _ = (1 : Matrix (Fin n) (Fin n) ℝ).mulVec x i := rfl
    _ = x i := congrFun (Matrix.one_mulVec x) i

theorem padMat_mulVec_natAdd (n : ℕ) (x : Fin n → ℝ) (i : Fin n) :
    (padMat n).mulVec x (Fin.natAdd n i) = -x i := by
  have hrow : (padMat n) (Fin.natAdd n i) = (-(1 : Matrix (Fin n) (Fin n) ℝ)) i := by
    show Fin.append (1 : Matrix (Fin n) (Fin n) ℝ) (-(1 : Matrix (Fin n) (Fin n) ℝ))
        (Fin.natAdd n i) = (-(1 : Matrix (Fin n) (Fin n) ℝ)) i
    rw [Fin.append_right]
  calc (padMat n).mulVec x (Fin.natAdd n i)
      = (padMat n) (Fin.natAdd n i) ⬝ᵥ x := rfl
    _ = (-(1 : Matrix (Fin n) (Fin n) ℝ)) i ⬝ᵥ x := by rw [hrow]
    _ = (-(1 : Matrix (Fin n) (Fin n) ℝ)).mulVec x i := rfl
    _ = (-((1 : Matrix (Fin n) (Fin n) ℝ).mulVec x)) i := by rw [Matrix.neg_mulVec]
    _ = -x i := by rw [Matrix.one_mulVec]

def padFront (n : ℕ) : Agent014.AffineT n (n + n) := ⟨padMat n, 0⟩

/-! ### The "recover x from (relu x, relu (-x))" back layer -/

def combineMat (n : ℕ) : Matrix (Fin n) (Fin (n + n)) ℝ :=
  Matrix.of (fun i =>
    Fin.append ((1 : Matrix (Fin n) (Fin n) ℝ) i) ((-(1 : Matrix (Fin n) (Fin n) ℝ)) i))

def combine (n : ℕ) : Agent014.AffineT (n + n) n := ⟨combineMat n, 0⟩

theorem combineMat_dotProduct (n : ℕ) (i : Fin n) (z : Fin (n + n) → ℝ) :
    (combineMat n) i ⬝ᵥ z = z (Fin.castAdd n i) - z (Fin.natAdd n i) := by
  have hrow : (combineMat n) i
      = Fin.append ((1 : Matrix (Fin n) (Fin n) ℝ) i) ((-(1 : Matrix (Fin n) (Fin n) ℝ)) i) :=
    rfl
  rw [hrow, dotProduct_append]
  have h1 : (1 : Matrix (Fin n) (Fin n) ℝ) i ⬝ᵥ (fun j => z (Fin.castAdd n j))
      = z (Fin.castAdd n i) :=
    congrFun (Matrix.one_mulVec (fun j => z (Fin.castAdd n j))) i
  have h2 : (-(1 : Matrix (Fin n) (Fin n) ℝ)) i ⬝ᵥ (fun j => z (Fin.natAdd n j))
      = -z (Fin.natAdd n i) := by
    have h2' := congrFun
      (Matrix.neg_mulVec (fun j => z (Fin.natAdd n j)) (1 : Matrix (Fin n) (Fin n) ℝ)) i
    simpa using h2'
  rw [h1, h2]
  ring

/-- The key real-number identity behind the padding trick. -/
theorem max_zero_sub_max_zero_neg (t : ℝ) : max (0 : ℝ) t - max (0 : ℝ) (-t) = t := by
  rcases le_or_lt (0 : ℝ) t with h | h
  · rw [max_eq_right_iff.mpr h, max_eq_left_iff.mpr (by linarith : -t ≤ (0 : ℝ))]
    ring
  · rw [max_eq_left_iff.mpr h.le, max_eq_right_iff.mpr (by linarith : (0 : ℝ) ≤ -t)]
    ring

theorem combine_padFront_eval (n : ℕ) (x : Fin n → ℝ) :
    (combine n).eval (Agent014.reluVec ((padFront n).eval x)) = x := by
  funext i
  have hpc : ((padFront n).eval x) (Fin.castAdd n i) = x i := by
    show (padMat n).mulVec x (Fin.castAdd n i) + (0 : Fin (n + n) → ℝ) (Fin.castAdd n i) = x i
    rw [Pi.zero_apply, add_zero, padMat_mulVec_castAdd]
  have hpn : ((padFront n).eval x) (Fin.natAdd n i) = -x i := by
    show (padMat n).mulVec x (Fin.natAdd n i) + (0 : Fin (n + n) → ℝ) (Fin.natAdd n i) = -x i
    rw [Pi.zero_apply, add_zero, padMat_mulVec_natAdd]
  have e1 : (Agent014.reluVec ((padFront n).eval x)) (Fin.castAdd n i) = max (0 : ℝ) (x i) := by
    show Agent014.relu (((padFront n).eval x) (Fin.castAdd n i)) = max (0 : ℝ) (x i)
    rw [hpc]
  have e2 : (Agent014.reluVec ((padFront n).eval x)) (Fin.natAdd n i)
      = max (0 : ℝ) (-x i) := by
    show Agent014.relu (((padFront n).eval x) (Fin.natAdd n i)) = max (0 : ℝ) (-x i)
    rw [hpn]
  show (combineMat n).mulVec (Agent014.reluVec ((padFront n).eval x)) i
      + (0 : Fin n → ℝ) i = x i
  rw [Pi.zero_apply, add_zero]
  show (combineMat n) i ⬝ᵥ (Agent014.reluVec ((padFront n).eval x)) = x i
  rw [combineMat_dotProduct, e1, e2]
  exact max_zero_sub_max_zero_neg (x i)

/-! ### Composing an `AffineT` network with an affine map on its input -/

def affineTComp {n' n b : ℕ} (T : Agent014.AffineT n b) (L : Agent014.AffineT n' n) :
    Agent014.AffineT n' b := ⟨T.A * L.A, T.A.mulVec L.c + T.c⟩

theorem affineTComp_eval {n' n b : ℕ} (T : Agent014.AffineT n b) (L : Agent014.AffineT n' n)
    (y : Fin n' → ℝ) : (affineTComp T L).eval y = T.eval (L.eval y) := by
  show (T.A * L.A).mulVec y + (T.A.mulVec L.c + T.c) = T.A.mulVec (L.A.mulVec y + L.c) + T.c
  rw [Matrix.mulVec_add, ← Matrix.mulVec_mulVec]
  abel

theorem precompose (n k : ℕ) (f : (Fin n → ℝ) → ℝ) (h : Agent014.IsReLUNetFun n k f)
    (n' : ℕ) (L : Agent014.AffineT n' n) :
    Agent014.IsReLUNetFun n' k (fun y => f (L.eval y)) := by
  cases k with
  | zero =>
    obtain ⟨T, hT⟩ := h
    exact ⟨affineTComp T L, fun y => by rw [hT (L.eval y), affineTComp_eval]⟩
  | succ k =>
    obtain ⟨m, T, g, hg, hf⟩ := h
    exact ⟨m, affineTComp T L, g, hg, fun y => by rw [hf (L.eval y), affineTComp_eval]⟩

/-! ### The padding lemma: `k` hidden layers can always be padded to `k + 1` -/

theorem pad (n k : ℕ) (f : (Fin n → ℝ) → ℝ) (h : Agent014.IsReLUNetFun n k f) :
    Agent014.IsReLUNetFun n (k + 1) f := by
  refine ⟨n + n, padFront n, fun z => f ((combine n).eval z),
    precompose n k f h (n + n) (combine n), fun x => ?_⟩
  show f x = f ((combine n).eval (Agent014.reluVec ((padFront n).eval x)))
  rw [combine_padFront_eval]

theorem pad_le (n k' : ℕ) (f : (Fin n → ℝ) → ℝ) (h : Agent014.IsReLUNetFun n k' f) :
    ∀ k, k' ≤ k → Agent014.IsReLUNetFun n k f := by
  intro k hk
  induction hk with
  | refl => exact h
  | step _ ih => exact pad n _ f ih

/-! ### `IsReLURep` and `IsReLUNetFun` describe the same "exactly `k` layers" class -/

def toAffineT {a b : ℕ} (T : Agent013.AffineMap a b) : Agent014.AffineT a b := ⟨T.A, T.c⟩
def toAffineMap {a b : ℕ} (T : Agent014.AffineT a b) : Agent013.AffineMap a b := ⟨T.A, T.c⟩

theorem toAffineT_eval {a b : ℕ} (T : Agent013.AffineMap a b) (x : Fin a → ℝ) :
    (toAffineT T).eval x = T.eval x := rfl

theorem toAffineMap_eval {a b : ℕ} (T : Agent014.AffineT a b) (x : Fin a → ℝ) :
    (toAffineMap T).eval x = T.eval x := rfl

theorem reluVec_eq {m : ℕ} (z : Fin m → ℝ) : Agent013.reluVec z = Agent014.reluVec z := rfl

theorem isReLURep_iff_isReLUNetFun (n k : ℕ) (f : (Fin n → ℝ) → ℝ) :
    Agent013.IsReLURep n k f ↔ Agent014.IsReLUNetFun n k f := by
  induction k generalizing n f with
  | zero =>
    constructor
    · rintro ⟨T, hT⟩
      refine ⟨toAffineT T, fun x => ?_⟩
      have hTx : f x = T.eval x 0 := congrFun hT x
      rw [hTx, toAffineT_eval]
    · rintro ⟨T, hT⟩
      refine ⟨toAffineMap T, funext fun x => ?_⟩
      show f x = (toAffineMap T).eval x 0
      rw [hT x, toAffineMap_eval]
  | succ k ih =>
    constructor
    · rintro ⟨m, T, g, hg, hf⟩
      refine ⟨m, toAffineT T, g, (ih m g).mp hg, fun x => ?_⟩
      show f x = g (Agent014.reluVec ((toAffineT T).eval x))
      have hfx : f x = g (Agent013.reluVec (T.eval x)) := congrFun hf x
      rw [hfx, toAffineT_eval, reluVec_eq]
    · rintro ⟨m, T, g, hg, hf⟩
      refine ⟨m, toAffineMap T, g, (ih m g).mpr hg, funext fun x => ?_⟩
      show f x = g (Agent013.reluVec ((toAffineMap T).eval x))
      rw [hf x, toAffineMap_eval, ← reluVec_eq]

theorem relun (n k : ℕ) : Agent013.ReLUn n k = Agent014.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨k', hk', hf⟩
    exact pad_le n k' f ((isReLURep_iff_isReLUNetFun n k' f).mp hf) k hk'
  · intro hf
    exact ⟨k, le_refl k, (isReLURep_iff_isReLUNetFun n k f).mpr hf⟩

/- ===================== `statement` ===================== -/

/-
We can show directly (by the same argument as `cpwl_ne`, run at `n = 3` where
`depthBound_013 3 = 2 ≥ 1`) that `Agent013.CPWL 3 ≠ Agent013.ReLUn 3 (Agent013.depthBound 3)`,
since `witnessF`-at-3-coordinates is representable with 1 hidden ReLU layer but is not in
`Agent013.CPWL 3`; so `Agent013`'s own reading of Theorem 2 is *false*. That alone does not
settle the stated `Iff`, because `Agent014`'s reading of Theorem 2 (with the genuine
polyhedral `CPWL` and the "exactly k hidden layers" `ReLUn`, which `relun` shows coincides
with the "at most k" reading) is exactly the actual, hard direction of Theorem 2 from the
paper (existence of a depth-`⌈log_3(n-1)⌉+1` ReLU network computing every CPWL function).
Proving or refuting *that* is a research-level undertaking well beyond the scope of a
bridge file, so we cannot determine whether `Agent014`'s statement is true or false, and
hence cannot determine the truth value of the stated `Iff` (`False ↔ True` vs `False ↔
False`). We leave this as `sorry`.
-/
theorem statement :
    (∀ n, 3 ≤ n → Agent013.CPWL n = Agent013.ReLUn n (Agent013.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent014.CPWL n = Agent014.ReLUn n (Agent014.depthBound n)) := by
  sorry

end Bridge_013_014

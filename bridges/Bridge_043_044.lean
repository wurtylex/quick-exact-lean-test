namespace Bridge_043_044

/-!
Comparison of `Agent043` and `Agent044`'s formalizations of Theorem 2.

Both agents:
* define `relu`/`reluVec` identically (`max 0 x`, applied componentwise);
* define an affine map `AffineT`/`AffineMap` as a `(matrix, bias)` pair evaluated the same way;
* define `depthBound n` by the *syntactically identical* term
  `Nat.ceil (Real.logb 3 ((n : ℝ) - 1)) + 1`;
* define `CPWL n` via the same "local agreement with a finite family of affine functions"
  condition (b) from the spec, one phrased with an explicit metric ball, the other with the
  `nhds` filter — these are equivalent via `Metric.eventually_nhds_iff`;
* define `ReLUn n k` as "at most `k` hidden layers" (`∃ k' ≤ k, …`), built by the same
  recursion-on-`k` peeling off the innermost affine map. The only structural difference is that
  `Agent043.NetworkComputes` carries a generic output dimension `m` (instantiated to `1` by
  `ReLUn`) and does not require hidden layers to have positive width, while
  `Agent044.NetComputes` is specialized to scalar output and requires each hidden layer to have
  positive width (`0 < m`). We show below that this does not change the represented function
  class: a zero-width layer can only ever compute a constant, and constants are already
  representable with `0` hidden layers.

All four obligations are proved below.
-/

/-- Convert an `Agent043` affine map to the `Agent044` encoding (same fields). -/
private def toAgent044 {a b : ℕ} (T : Agent043.AffineT a b) : Agent044.AffineMap a b :=
  ⟨T.A, T.c⟩

/-- Convert an `Agent044` affine map to the `Agent043` encoding (same fields). -/
private def toAgent043 {a b : ℕ} (T : Agent044.AffineMap a b) : Agent043.AffineT a b :=
  ⟨T.A, T.c⟩

private lemma toAgent044_eval {a b : ℕ} (T : Agent043.AffineT a b) (x : Fin a → ℝ) :
    (toAgent044 T).eval x = T.eval x := rfl

private lemma toAgent043_eval {a b : ℕ} (T : Agent044.AffineMap a b) (x : Fin a → ℝ) :
    (toAgent043 T).eval x = T.eval x := rfl

/-- `relu`/`reluVec` are literally the same function (`max 0 ·`) under both names. -/
private lemma reluVec_eq {m : ℕ} (x : Fin m → ℝ) :
    Agent043.reluVec x = Agent044.reluVec x := rfl

/-- Any two functions out of the empty type `Fin 0` are equal. -/
private lemma fin0_eq (u v : Fin 0 → ℝ) : u = v :=
  funext fun i => absurd i.isLt (Nat.not_lt_zero _)

/-- The unique element of `Fin 1` is `0`. -/
private lemma fin1_eq_zero (i : Fin 1) : i = 0 := by
  first
  | omega
  | (apply Fin.ext; simp)
  | exact Subsingleton.elim i 0

/-- Every `Agent043`-network (output wrapped into `Fin 1`) with `k` hidden layers can be
re-expressed as an `Agent044`-network with at most `k` hidden layers. The only place the bound
can drop is when `Agent043` uses a degenerate zero-width hidden layer, in which case the
resulting function is constant and is realized with `0` hidden layers instead. -/
private lemma net_to044 : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent043.NetworkComputes 1 k n (fun x _ => f x) →
    ∃ k' ≤ k, Agent044.NetComputes n k' f := by
  intro k
  induction k with
  | zero =>
    intro n f hf
    obtain ⟨T, hT⟩ := hf
    refine ⟨0, le_refl 0, toAgent044 T, fun x => ?_⟩
    have h1 : (fun (_ : Fin 1) => f x) = T.eval x := congrFun hT x
    have h2 : f x = T.eval x 0 := congrFun h1 0
    show f x = (toAgent044 T).eval x 0
    rw [toAgent044_eval T x]
    exact h2
  | succ k ih =>
    intro n f hf
    obtain ⟨p, T, g, hg, hfg⟩ := hf
    have hg' : g = fun z (_ : Fin 1) => g z 0 := by
      funext z i
      show g z i = g z 0
      rw [fin1_eq_zero i]
    rw [hg'] at hg
    obtain ⟨k', hk'le, hk'⟩ := ih p (fun z => g z 0) hg
    have hx : ∀ x : Fin n → ℝ, f x = g (Agent043.reluVec (T.eval x)) 0 :=
      fun x => congrFun (congrFun hfg x) 0
    rcases Nat.eq_zero_or_pos p with hp0 | hppos
    · subst hp0
      set z0 : Fin 0 → ℝ := fun i => absurd i.isLt (Nat.not_lt_zero _) with hz0def
      refine ⟨0, Nat.zero_le _, ⟨0, fun _ => g z0 0⟩, fun x => ?_⟩
      have hveqx : Agent043.reluVec (T.eval x) = z0 := fin0_eq _ _
      have hxc : f x = g z0 0 := by rw [hx x, hveqx]
      show f x = (0 : Matrix (Fin 1) (Fin n) ℝ).mulVec x 0 + g z0 0
      rw [Matrix.zero_mulVec, Pi.zero_apply, zero_add]
      exact hxc
    · refine ⟨k' + 1, Nat.succ_le_succ hk'le, p, hppos, toAgent044 T, (fun z => g z 0), hk',
        fun x => ?_⟩
      show f x = g (Agent044.reluVec ((toAgent044 T).eval x)) 0
      rw [toAgent044_eval T x, ← reluVec_eq (T.eval x)]
      exact hx x

/-- Conversely every `Agent044`-network with `k` hidden layers directly gives an
`Agent043`-network (output wrapped into `Fin 1`) with exactly `k` hidden layers: `Agent044`'s
extra positivity constraint on hidden widths is never needed in this direction. -/
private lemma net_to043 : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent044.NetComputes n k f →
    Agent043.NetworkComputes 1 k n (fun x _ => f x) := by
  intro k
  induction k with
  | zero =>
    intro n f hf
    obtain ⟨T, hT⟩ := hf
    refine ⟨toAgent043 T, ?_⟩
    funext x i
    rw [fin1_eq_zero i]
    show f x = (toAgent043 T).eval x 0
    rw [toAgent043_eval T x]
    exact hT x
  | succ k ih =>
    intro n f hf
    obtain ⟨m, hm, T, g, hg, hfg⟩ := hf
    have hg' := ih m g hg
    refine ⟨m, toAgent043 T, (fun z _ => g z), hg', ?_⟩
    funext x i
    show f x = g (Agent043.reluVec ((toAgent043 T).eval x))
    rw [toAgent043_eval T x, reluVec_eq (T.eval x)]
    exact hfg x

theorem cpwl (n : ℕ) : Agent043.CPWL n = Agent044.CPWL n := by
  ext f
  simp only [Agent043.CPWL, Agent044.CPWL, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hf, N, A, c, hloc⟩
    refine ⟨hf, N, A, c, fun x => ?_⟩
    obtain ⟨r, hr, i, hri⟩ := hloc x
    refine ⟨i, ?_⟩
    rw [Metric.eventually_nhds_iff]
    exact ⟨r, hr, fun y hy => hri y hy⟩
  · rintro ⟨hf, N, A, c, hloc⟩
    refine ⟨hf, N, A, c, fun x => ?_⟩
    obtain ⟨i, hi⟩ := hloc x
    rw [Metric.eventually_nhds_iff] at hi
    obtain ⟨r, hr, hri⟩ := hi
    exact ⟨r, hr, i, fun y hy => hri hy⟩

theorem relun (n k : ℕ) : Agent043.ReLUn n k = Agent044.ReLUn n k := by
  ext f
  simp only [Agent043.ReLUn, Agent044.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k', hk'le, hk'⟩
    obtain ⟨k'', hk''le, hk''⟩ := net_to044 k' n f hk'
    exact ⟨k'', hk''le.trans hk'le, hk''⟩
  · rintro ⟨k', hk'le, hk'⟩
    exact ⟨k', hk'le, net_to043 k' n f hk'⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent043.depthBound n = Agent044.depthBound n := rfl

theorem statement :
    (∀ n, 3 ≤ n → Agent043.CPWL n = Agent043.ReLUn n (Agent043.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent044.CPWL n = Agent044.ReLUn n (Agent044.depthBound n)) := by
  constructor
  · intro h n hn
    rw [← cpwl n, ← depth n hn, ← relun n (Agent043.depthBound n)]
    exact h n hn
  · intro h n hn
    rw [cpwl n, depth n hn, relun n (Agent044.depthBound n)]
    exact h n hn

end Bridge_043_044

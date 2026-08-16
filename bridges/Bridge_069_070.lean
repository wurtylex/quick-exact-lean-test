namespace Bridge_069_070

/-!
Agent069 and Agent070 formalize Theorem 2 almost identically: same `relu`/`reluVec`,
the same concrete `A * x + c` affine maps (069's `AffineMap'` vs 070's `AffineMap`,
identical fields), the same "at most k hidden layers" reading of `ReLUn` (justified by
the same padding-argument comment in both files), the same `CPWL` (continuous +
local agreement with a finite affine family), and the literally identical formula
`⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1` for `depthBound`.

The only real difference is *how* a ReLU network is encoded: 069 uses a `Type`-valued
inductive `ReLUNet` with an explicit `eval` function, while 070 uses a `Prop`-valued
inductive relation `NetworkComputes`. We bridge these by a pair of mutually inverse
structural conversions, `to070`/`to069` on affine maps and `toNC`/`toEx` on networks.
-/

/-- Convert a 069 affine map to the (identically-shaped) 070 affine map. -/
def to070 {a b : ℕ} (T : Agent069.AffineMap' a b) : Agent070.AffineMap a b := ⟨T.A, T.c⟩

/-- Convert a 070 affine map to the (identically-shaped) 069 affine map. -/
def to069 {a b : ℕ} (T : Agent070.AffineMap a b) : Agent069.AffineMap' a b := ⟨T.A, T.c⟩

lemma to070_eval {a b : ℕ} (T : Agent069.AffineMap' a b) (x : Fin a → ℝ) (i : Fin b) :
    (to070 T).eval x i = T.apply x i := by
  simp [to070, Agent070.AffineMap.eval, Agent069.AffineMap'.apply, Pi.add_apply]

lemma to069_apply {a b : ℕ} (T : Agent070.AffineMap a b) (x : Fin a → ℝ) (i : Fin b) :
    (to069 T).apply x i = T.eval x i := by
  simp [to069, Agent070.AffineMap.eval, Agent069.AffineMap'.apply, Pi.add_apply]

lemma to070_eval' {a b : ℕ} (T : Agent069.AffineMap' a b) (x : Fin a → ℝ) :
    (to070 T).eval x = T.apply x := funext (to070_eval T x)

lemma to069_apply' {a b : ℕ} (T : Agent070.AffineMap a b) (x : Fin a → ℝ) :
    (to069 T).apply x = T.eval x := funext (to069_apply T x)

/-- Both `reluVec`s are `fun i => max 0 (x i)`. -/
lemma reluVec_eq {m : ℕ} (y : Fin m → ℝ) : Agent069.reluVec y = Agent070.reluVec y := by
  funext i
  simp [Agent069.reluVec, Agent070.reluVec, Agent069.relu, Agent070.relu]

/-- Every 069 `ReLUNet` (with output dimension `1`) yields a 070 `NetworkComputes`
witness for the same function. Structural recursion on the network. -/
theorem toNC : ∀ {a k : ℕ} (net : Agent069.ReLUNet a 1 k),
    Agent070.NetworkComputes a k (fun x => net.eval x 0)
  | _, _, .last T => by
      have hf : (fun x => (Agent069.ReLUNet.last T).eval x 0)
              = (fun x => (to070 T).eval x 0) := by
        funext x; exact (to070_eval T x 0).symm
      rw [hf]
      exact Agent070.NetworkComputes.base _ (to070 T)
  | _, _, .cons T rest => by
      have hf : (fun x => (Agent069.ReLUNet.cons T rest).eval x 0)
              = (fun x => rest.eval (Agent070.reluVec ((to070 T).eval x)) 0) := by
        funext x
        show rest.eval (Agent069.reluVec (T.apply x)) 0
            = rest.eval (Agent070.reluVec ((to070 T).eval x)) 0
        rw [to070_eval', reluVec_eq]
      rw [hf]
      exact Agent070.NetworkComputes.step _ _ _ (to070 T) _ (toNC rest)

/-- Conversely, every 070 `NetworkComputes` witness comes from some 069 `ReLUNet`. -/
theorem toEx : ∀ {a k : ℕ} {f : (Fin a → ℝ) → ℝ}, Agent070.NetworkComputes a k f →
    ∃ net : Agent069.ReLUNet a 1 k, ∀ x, f x = net.eval x 0
  | _, _, _, .base n T =>
      ⟨Agent069.ReLUNet.last (to069 T), fun x => by
        show T.eval x 0 = (Agent069.ReLUNet.last (to069 T)).eval x 0
        exact (to069_apply T x 0).symm⟩
  | _, _, _, .step n m j T g hg =>
      let ⟨net', hnet'⟩ := toEx hg
      ⟨Agent069.ReLUNet.cons (to069 T) net', fun x => by
        show g (Agent070.reluVec (T.eval x))
            = net'.eval (Agent069.reluVec ((to069 T).apply x)) 0
        rw [to069_apply', reluVec_eq]
        exact hnet' _⟩

theorem cpwl (n : ℕ) : Agent069.CPWL n = Agent070.CPWL n := by
  ext f
  constructor
  · rintro ⟨hc, m, g, hg, hloc⟩
    exact ⟨hc, m, g, hg, hloc⟩
  · rintro ⟨hc, m, g, hg, hloc⟩
    exact ⟨hc, m, g, hg, hloc⟩

theorem relun (n k : ℕ) : Agent069.ReLUn n k = Agent070.ReLUn n k := by
  ext f
  simp only [Agent069.ReLUn, Agent070.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k', hk', net, hnet⟩
    refine ⟨k', hk', ?_⟩
    have hf : f = fun x => net.eval x 0 := funext hnet
    rw [hf]
    exact toNC net
  · rintro ⟨k', hk', hNC⟩
    obtain ⟨net, hnet⟩ := toEx hNC
    exact ⟨k', hk', net, hnet⟩

/-- Both files use the literally identical formula `⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1`. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent069.depthBound n = Agent070.depthBound n := rfl

theorem statement :
    (∀ n, 3 ≤ n → Agent069.CPWL n = Agent069.ReLUn n (Agent069.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent070.CPWL n = Agent070.ReLUn n (Agent070.depthBound n)) := by
  constructor
  · intro h n hn
    calc Agent070.CPWL n = Agent069.CPWL n := (cpwl n).symm
      _ = Agent069.ReLUn n (Agent069.depthBound n) := h n hn
      _ = Agent070.ReLUn n (Agent069.depthBound n) := relun n (Agent069.depthBound n)
      _ = Agent070.ReLUn n (Agent070.depthBound n) := by rw [depth n hn]
  · intro h n hn
    calc Agent069.CPWL n = Agent070.CPWL n := cpwl n
      _ = Agent070.ReLUn n (Agent070.depthBound n) := h n hn
      _ = Agent070.ReLUn n (Agent069.depthBound n) := by rw [depth n hn]
      _ = Agent069.ReLUn n (Agent069.depthBound n) := (relun n (Agent069.depthBound n)).symm

end Bridge_069_070

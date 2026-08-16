namespace Bridge_055_056

/- ## Auxiliary lemmas -/

/-- The two agents' scalar `relu` (hence componentwise `reluVec`) are the same function
`max 0 ·`, so they agree pointwise on every vector. -/
private theorem reluVec_eq {m : ℕ} :
    (Agent055.reluVec : (Fin m → ℝ) → Fin m → ℝ) = Agent056.reluVec := by
  funext x i
  rfl

/-- Both agents' `AffMap.eval` compute `x ↦ A x + c` from the same matrix `A` and bias `c`;
Agent055 states this directly as a sum, Agent056 goes through `Matrix.mulVec`, and the two
agree by unfolding `mulVec`/`dotProduct` to the same sum. -/
private theorem aff_eval_eq {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ)
    (x : Fin n → ℝ) :
    Agent055.AffMap.eval (⟨A, c⟩ : Agent055.AffMap n m) x
      = Agent056.AffMap.eval (⟨A, c⟩ : Agent056.AffMap n m) x := by
  funext i
  show (∑ j, A i j * x j) + c i = (A.mulVec x + c) i
  simp only [Matrix.mulVec, Matrix.dotProduct, Pi.add_apply]

/-- Agent055's recursive-`Prop` network family and Agent056's inductive-`Type` network
family compute exactly the same set of functions at every depth `k`, by induction on `k`
using `aff_eval_eq` and `reluVec_eq` to match layers one at a time. -/
theorem computedByReLUNet_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent055.ComputedByReLUNet n k f ↔
      ∃ net : Agent056.ReLUNet n k, ∀ x, f x = net.compute x := by
  intro k
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨a, b, hab⟩
      refine ⟨Agent056.ReLUNet.output (⟨fun _ j => a j, fun _ => b⟩ : Agent056.AffMap n 1),
        fun x => ?_⟩
      show f x = Agent056.AffMap.eval
        (⟨fun (_ : Fin 1) j => a j, fun _ => b⟩ : Agent056.AffMap n 1) x 0
      rw [hab x]
      show (∑ j, a j * x j) + b
          = ((fun (_ : Fin 1) j => a j : Matrix (Fin 1) (Fin n) ℝ).mulVec x + fun _ => b) 0
      simp only [Matrix.mulVec, Matrix.dotProduct, Pi.add_apply]
    · rintro ⟨net, hnet⟩
      cases net with
      | output T =>
        obtain ⟨A, bias⟩ := T
        refine ⟨fun j => A 0 j, bias 0, fun x => ?_⟩
        have h1 : f x = Agent056.AffMap.eval (⟨A, bias⟩ : Agent056.AffMap n 1) x 0 := hnet x
        rw [h1]
        show (A.mulVec x + bias) 0 = (∑ j, A 0 j * x j) + bias 0
        simp only [Matrix.mulVec, Matrix.dotProduct, Pi.add_apply]
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, T, g, hg, hfx⟩
      obtain ⟨A, c⟩ := T
      obtain ⟨net, hnet⟩ := (ih m g).1 hg
      refine ⟨Agent056.ReLUNet.layer (⟨A, c⟩ : Agent056.AffMap n m) net, fun x => ?_⟩
      have h2 : Agent055.reluVec (Agent055.AffMap.eval (⟨A, c⟩ : Agent055.AffMap n m) x)
              = Agent056.reluVec (Agent056.AffMap.eval (⟨A, c⟩ : Agent056.AffMap n m) x) := by
        rw [reluVec_eq, aff_eval_eq]
      rw [hfx x, h2]
      exact hnet _
    · rintro ⟨net, hnet⟩
      cases net with
      | layer T rest =>
        rename_i m
        obtain ⟨A, c⟩ := T
        have hg : Agent055.ComputedByReLUNet m k (fun y => rest.compute y) :=
          (ih m (fun y => rest.compute y)).2 ⟨rest, fun _ => rfl⟩
        refine ⟨m, (⟨A, c⟩ : Agent055.AffMap n m), (fun y => rest.compute y), hg, fun x => ?_⟩
        show f x = rest.compute
          (Agent055.reluVec (Agent055.AffMap.eval (⟨A, c⟩ : Agent055.AffMap n m) x))
        have h2 : Agent055.reluVec (Agent055.AffMap.eval (⟨A, c⟩ : Agent055.AffMap n m) x)
                = Agent056.reluVec (Agent056.AffMap.eval (⟨A, c⟩ : Agent056.AffMap n m) x) := by
          rw [reluVec_eq, aff_eval_eq]
        rw [h2]
        exact hnet x

/- ## The four obligations -/

theorem cpwl (n : ℕ) : Agent055.CPWL n = Agent056.CPWL n := by
  ext f
  constructor
  · rintro ⟨hf, m, g, hg, hloc⟩
    choose a b hab using hg
    refine ⟨hf, m, fun i => (⟨a i, b i⟩ : Agent056.AffineFunctional n), fun x => ?_⟩
    obtain ⟨i, U, hU, heq⟩ := hloc x
    refine ⟨i, Filter.eventually_iff_exists_mem.2 ⟨U, hU, fun y hy => ?_⟩⟩
    show f y = (Finset.univ.sum fun j => a i j * y j) + b i
    rw [heq hy, hab i y]
  · rintro ⟨hf, m, g, hloc⟩
    refine ⟨hf, m, fun i => (g i).eval,
      fun i => ⟨(g i).coeff, (g i).const, fun x => rfl⟩, fun x => ?_⟩
    obtain ⟨i, hev⟩ := hloc x
    obtain ⟨U, hU, hU'⟩ := Filter.eventually_iff_exists_mem.1 hev
    exact ⟨i, U, hU, fun y hy => hU' y hy⟩

theorem relun (n k : ℕ) : Agent055.ReLUn n k = Agent056.ReLUn n k := by
  ext f
  unfold Agent055.ReLUn Agent056.ReLUn
  constructor
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (computedByReLUNet_iff j n f).1 hf⟩
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (computedByReLUNet_iff j n f).2 hf⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent055.depthBound n = Agent056.depthBound n := by
  have h1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have h1n : (1 : ℕ) ≤ n := by omega
    rw [Nat.cast_sub h1n, Nat.cast_one]
  show ⌈Real.logb 3 ((n - 1 : ℕ) : ℝ)⌉₊ + 1 = ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1
  rw [h1]

theorem statement :
    (∀ n, 3 ≤ n → Agent055.CPWL n = Agent055.ReLUn n (Agent055.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent056.CPWL n = Agent056.ReLUn n (Agent056.depthBound n)) := by
  constructor
  · intro h n hn
    have e1 := cpwl n
    have e2 := relun n (Agent055.depthBound n)
    have e3 := depth n hn
    rw [← e1, h n hn, e2, e3]
  · intro h n hn
    have e1 := cpwl n
    have e2 := relun n (Agent056.depthBound n)
    have e3 := depth n hn
    rw [e1, h n hn, ← e2, ← e3]

end Bridge_055_056

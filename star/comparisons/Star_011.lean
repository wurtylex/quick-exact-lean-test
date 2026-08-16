namespace Star_011

/-! ### The refutation of `CPWL`

`Agent011.CPWL` asks that `f` agree with one of finitely many affine functionals
on a *neighbourhood* of every point.  On connected `ℝⁿ` that forces `f` to be
globally affine, so it is strictly stronger than the reference's polyhedral-cover
condition.  Witness: `fun x => max 0 (x i)`. -/

/-- The line `t ↦ t • eᵢ` in `ℝⁿ`. -/
private def line {n : ℕ} (i : Fin n) (t : ℝ) : Fin n → ℝ := fun k => if k = i then t else 0

private theorem line_self {n : ℕ} (i : Fin n) (t : ℝ) : line i t i = t := by simp [line]

private theorem line_zero {n : ℕ} (i : Fin n) : line i 0 = (0 : Fin n → ℝ) := by
  funext k; simp [line]

private theorem continuous_line {n : ℕ} (i : Fin n) : Continuous (line i) := by
  refine continuous_pi fun k => ?_
  by_cases h : k = i
  · simp only [line, if_pos h]; exact continuous_id
  · simp only [line, if_neg h]; exact continuous_const

/-- The kink argument: `max 0 (x i)` is not locally affine at the origin. -/
private theorem notCPWL {n : ℕ} (i : Fin n) :
    (fun x : Fin n → ℝ => max 0 (x i)) ∉ Agent011.CPWL n := by
  rintro ⟨-, m, g, hg, hcov⟩
  obtain ⟨j, U, hU, hEq⟩ := hcov 0
  obtain ⟨a, b, hab⟩ := hg j
  have hsum : ∀ t : ℝ, (∑ k, a k * line i t k) = a i * t := by
    intro t
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [line, hk]) (by simp)]
    simp [line]
  have hpre : line i ⁻¹' U ∈ nhds (0 : ℝ) := by
    have hU0 : U ∈ nhds (line i 0) := by rw [line_zero]; exact hU
    exact (continuous_line i).continuousAt.preimage_mem_nhds hU0
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hpre
  have key : ∀ t : ℝ, |t| < ε → max 0 t = a i * t + b := by
    intro t ht
    have htb : t ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero]; exact ht
    have h2 : max 0 (line i t i) = g j (line i t) := hEq (hball htb)
    rw [line_self, hab (line i t), hsum t] at h2
    exact h2
  have hb : b = 0 := by
    have h0 := key 0 (by rw [abs_zero]; exact hε)
    simpa using h0.symm
  have hp := key (ε / 2) (by rw [abs_of_pos (by linarith)]; linarith)
  have hn := key (-(ε / 2)) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ ε / 2)] at hp
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0 : ℝ))] at hn
  rw [hb] at hp hn
  linarith

private theorem halfspace_isPolyhedron {n : ℕ} {S : Set (Fin n → ℝ)} (h : Ref.IsHalfspace n S) :
    Ref.IsPolyhedron n S := ⟨1, fun _ => S, fun _ => h, by ext x; simp⟩

/-- `max 0 (x 0)` *is* CPWL in the reference sense: two halfspaces cover `ℝ¹`. -/
private theorem f_isCPWL : Ref.IsCPWL 1 (fun x : Fin 1 → ℝ => max 0 (x 0)) := by
  refine ⟨continuous_const.max (continuous_apply 0), 2,
    ![{x : Fin 1 → ℝ | (∑ i, (1 : ℝ) * x i) ≤ 0}, {x : Fin 1 → ℝ | (∑ i, (-1 : ℝ) * x i) ≤ 0}],
    ![fun _ => 0, fun x => x 0], ?_, ?_, ?_, ?_⟩
  · rw [Fin.forall_fin_two]
    exact ⟨halfspace_isPolyhedron ⟨fun _ => 1, 0, rfl⟩,
      halfspace_isPolyhedron ⟨fun _ => -1, 0, rfl⟩⟩
  · rw [Fin.forall_fin_two]
    exact ⟨⟨fun _ => 0, 0, by intro x; simp⟩, ⟨fun _ => 1, 0, by intro x; simp⟩⟩
  · rw [Set.eq_univ_iff_forall]
    intro x
    rw [Set.mem_iUnion]
    rcases le_total (x 0) 0 with h | h
    · refine ⟨0, ?_⟩
      show (∑ i, (1 : ℝ) * x i) ≤ 0
      rw [Fin.sum_univ_one]; linarith
    · refine ⟨1, ?_⟩
      show (∑ i, (-1 : ℝ) * x i) ≤ 0
      rw [Fin.sum_univ_one]; linarith
  · rw [Fin.forall_fin_two]
    constructor
    · intro x hx
      replace hx : (∑ i, (1 : ℝ) * x i) ≤ 0 := hx
      rw [Fin.sum_univ_one] at hx
      show max 0 (x 0) = 0
      exact max_eq_left (by linarith)
    · intro x hx
      replace hx : (∑ i, (-1 : ℝ) * x i) ≤ 0 := hx
      rw [Fin.sum_univ_one] at hx
      show max 0 (x 0) = x 0
      exact max_eq_right (by linarith)

theorem cpwl_ne : ∃ n, Agent011.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => notCPWL (0 : Fin 1) ?_⟩
  rw [h]; exact f_isCPWL

/-! ### The agent's Theorem 2 is outright false -/

private def wLayer : Agent011.Layer 3 1 :=
  { A := Matrix.of fun _ j => if j = 0 then (1 : ℝ) else 0, c := 0 }

private def idLayer : Agent011.Layer 1 1 := { A := 1, c := 0 }

private def net3 : Agent011.NetLayers 3 1 :=
  Agent011.NetLayers.cons wLayer (Agent011.NetLayers.last idLayer)

private theorem idLayer_apply (v : Fin 1 → ℝ) : idLayer.apply v = v := by
  simp [idLayer, Agent011.Layer.apply, Matrix.one_mulVec]

private theorem net3_eval (x : Fin 3 → ℝ) : net3.eval x = max 0 (x 0) := by
  have hw : (wLayer.apply x) 0 = x 0 := by
    have h : (wLayer.apply x) 0 = (∑ j, (if j = 0 then (1 : ℝ) else 0) * x j) + 0 := rfl
    rw [h, Finset.sum_eq_single (0 : Fin 3) (fun k _ hk => by simp [hk]) (by simp)]
    simp
  have h1 : net3.eval x = Agent011.relu ((wLayer.apply x) 0) := by
    show idLayer.apply (Agent011.reluVec (wLayer.apply x)) 0 = _
    rw [idLayer_apply]; rfl
  rw [h1, hw]; rfl

/-- `fun x => max 0 (x 0)` is a one-hidden-layer network on `ℝ³`, hence lies in
`ReLUn 3 (depthBound 3)`, but the neighbourhood-agreement `CPWL` rejects it. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent011.CPWL n = Agent011.ReLUn n (Agent011.depthBound n)) := by
  intro h
  refine notCPWL (0 : Fin 3) ?_
  rw [h 3 le_rfl]
  exact ⟨1, Nat.le_add_left 1 _, net3, funext fun x => (net3_eval x).symm⟩

/-! ### `ReLUn` and `depthBound` agree -/

/-- The agent's `NetLayers` data is exactly the reference's `ComputedBy` predicate. -/
private theorem computedBy_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Ref.ComputedBy n k f ↔ ∃ net : Agent011.NetLayers n k, f = net.eval := by
  intro k
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨T, hT⟩
      exact ⟨Agent011.NetLayers.last ⟨T.M, T.c⟩, funext fun x => hT x⟩
    · rintro ⟨net, rfl⟩
      cases net with
      | last L => exact ⟨⟨L.A, L.c⟩, fun x => rfl⟩
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, T, g, hg, hf⟩
      obtain ⟨net, rfl⟩ := (ih m g).1 hg
      exact ⟨Agent011.NetLayers.cons ⟨T.M, T.c⟩ net, funext fun x => hf x⟩
    · rintro ⟨net, rfl⟩
      cases net with
      | cons L rest => exact ⟨_, ⟨L.A, L.c⟩, rest.eval, (ih _ _).2 ⟨rest, rfl⟩, fun x => rfl⟩

theorem relun (n k : ℕ) : Agent011.ReLUn n k = Ref.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨j, hj, net, rfl⟩
    exact ⟨j, hj, (computedBy_iff j n _).2 ⟨net, rfl⟩⟩
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (computedBy_iff j n f).1 hf⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent011.depthBound n = Ref.depthBound n := rfl

/-- The two sides are *not* equivalent: the left side is false (`agent_side_false`)
while the right side is the true Theorem 2, so the honest obligation here is
`statement_ne` — and proving it requires proving `Ref.theorem2` itself, which is
`sorry`-ed in the reference.  Left as an honest `sorry`. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent011.CPWL n = Agent011.ReLUn n (Agent011.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_011

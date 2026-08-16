namespace Bridge_056_057

/-! `depthBound` is the literally identical expression in both files. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent056.depthBound n = Agent057.depthBound n := rfl

/-! ## `relun`

`Agent056.ReLUNet n k'` / `.compute` builds a network as *data* and evaluates it;
`Agent057.ComputesReLU n 1 k' F` is an inductive *predicate* on the alternating
composition `T^{(k'+1)} ∘ ReLU ∘ ⋯ ∘ ReLU ∘ T^{(1)}`. Both encode the same
composition and both use the "at most k" reading, so the represented classes
coincide; we convert one network representation into the other, layer by layer. -/

/-- For `F : (Fin n → ℝ) → (Fin 1 → ℝ)`, being computed (as data) by an
`Agent056.ReLUNet` with `k` hidden layers is the same as satisfying
`Agent057.ComputesReLU` with `k` hidden layers. Induction on `k`, generalized over
`n` since the recursive call happens at the hidden-layer width, not at `n`. -/
private theorem key : ∀ (k n : ℕ) (F : (Fin n → ℝ) → Fin 1 → ℝ),
    (∃ net : Agent056.ReLUNet n k, ∀ x, F x = fun _ => net.compute x) ↔
      Agent057.ComputesReLU n 1 k F := by
  intro k
  induction k with
  | zero =>
      intro n F
      constructor
      · rintro ⟨net, hnet⟩
        cases net with
        | output T =>
            have hF : F = (⟨T.A, T.bias⟩ : Agent057.AffMap n 1).eval := by
              funext x i
              have hi : i = 0 := Subsingleton.elim i 0
              subst hi
              have hx := congrFun (hnet x) 0
              simpa [Agent056.ReLUNet.compute, Agent056.AffMap.eval,
                Agent057.AffMap.eval] using hx
            rw [hF]
            exact Agent057.ComputesReLU.base _
      · intro h
        cases h with
        | base T =>
            refine ⟨Agent056.ReLUNet.output ⟨T.A, T.c⟩, fun x => ?_⟩
            funext i
            have hi : i = 0 := Subsingleton.elim i 0
            subst hi
            simp [Agent056.ReLUNet.compute, Agent056.AffMap.eval, Agent057.AffMap.eval]
  | succ k ih =>
      intro n F
      constructor
      · rintro ⟨net, hnet⟩
        cases net with
        | layer T rest =>
            have hg : Agent057.ComputesReLU _ 1 k (fun y _ => rest.compute y) :=
              (ih _ (fun y _ => rest.compute y)).1 ⟨rest, fun _ => rfl⟩
            have hF : F = (fun y (_ : Fin 1) => rest.compute y) ∘ Agent057.reluVec ∘
                (⟨T.A, T.bias⟩ : Agent057.AffMap _ _).eval := by
              funext x i
              have hi : i = 0 := Subsingleton.elim i 0
              subst hi
              have hx := congrFun (hnet x) 0
              simp only [Agent056.ReLUNet.compute, Function.comp_apply] at hx ⊢
              rw [hx]
              congr 1
              funext j
              simp [Agent057.reluVec, Agent056.reluVec, Agent057.relu, Agent056.relu,
                Agent057.AffMap.eval, Agent056.AffMap.eval]
            rw [hF]
            exact Agent057.ComputesReLU.step _ _ hg
      · intro h
        cases h with
        | step T g hg =>
            obtain ⟨rest, hrest⟩ := (ih _ g).2 hg
            refine ⟨Agent056.ReLUNet.layer ⟨T.A, T.c⟩ rest, fun x => ?_⟩
            funext i
            have hi : i = 0 := Subsingleton.elim i 0
            subst hi
            show (g ∘ Agent057.reluVec ∘ T.eval) x 0 =
                (Agent056.ReLUNet.layer (⟨T.A, T.c⟩ : Agent056.AffMap _ _) rest).compute x
            simp only [Agent056.ReLUNet.compute, Function.comp_apply]
            have hy : Agent056.reluVec ((⟨T.A, T.c⟩ : Agent056.AffMap _ _).eval x) =
                Agent057.reluVec (T.eval x) := by
              funext j
              simp [Agent057.reluVec, Agent056.reluVec, Agent057.relu, Agent056.relu,
                Agent057.AffMap.eval, Agent056.AffMap.eval]
            rw [hy]
            exact congrFun (hrest (Agent057.reluVec (T.eval x))) 0

theorem relun (n k : ℕ) : Agent056.ReLUn n k = Agent057.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨k', hk', net, hnet⟩
    exact ⟨k', hk', (key k' n (fun x _ => f x)).1
      ⟨net, fun x => by funext i; exact hnet x⟩⟩
  · rintro ⟨k', hk', h⟩
    obtain ⟨net, hnet⟩ := (key k' n (fun x _ => f x)).2 h
    exact ⟨k', hk', net, fun x => congrFun (hnet x) 0⟩

/-! ## `cpwl_ne`

`Agent056.CPWL` uses *local agreement*: `f` is CPWL iff `Continuous f` and every
point has a full two-sided `nhds` neighbourhood on which `f` coincides with ONE
affine functional from a finite family. `Agent057.CPWL` uses a genuine finite
*polyhedral subdivision*: `f` is CPWL iff `Continuous f` and finitely many
polyhedra cover `ℝⁿ`, on each of which `f` agrees with an affine map. These
disagree: `f x = max 0 (x 0)` on `ℝ¹` is CPWL under the 057 reading (two
half-spaces) but not under the 056 reading, since no single affine `a*t+b` can
equal `max 0 t` on a full two-sided neighbourhood of `t = 0` (it forces `b = 0`
from `t = 0`, `a = 1` from the right, and then `0 = -a·(ε/2) = -ε/2` from the
left, i.e. `ε = 0`, contradicting `ε > 0`). -/

private def posProj : (Fin 1 → ℝ) →ₗ[ℝ] ℝ where
  toFun x := x 0
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

private def negProj : (Fin 1 → ℝ) →ₗ[ℝ] ℝ where
  toFun x := -(x 0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

private theorem posProj_apply (x : Fin 1 → ℝ) : posProj x = x 0 := rfl
private theorem negProj_apply (x : Fin 1 → ℝ) : negProj x = -(x 0) := rfl

private def idAff : (Fin 1 → ℝ) →ᵃ[ℝ] ℝ where
  toFun x := x 0
  linear := posProj
  map_vadd' _ _ := by first | rfl | simp [vadd_eq_add, posProj_apply]

private theorem idAff_apply (x : Fin 1 → ℝ) : idAff x = x 0 := rfl

private theorem hpoly_le0 : Agent057.IsPolyhedron 1 {x : Fin 1 → ℝ | x 0 ≤ 0} := by
  refine ⟨PUnit, inferInstance, fun _ => posProj, fun _ => (0 : ℝ), ?_⟩
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iInter, posProj_apply]
  exact ⟨fun h _ => h, fun h => h PUnit.unit⟩

private theorem hpoly_ge0 : Agent057.IsPolyhedron 1 {x : Fin 1 → ℝ | 0 ≤ x 0} := by
  refine ⟨PUnit, inferInstance, fun _ => negProj, fun _ => (0 : ℝ), ?_⟩
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iInter, negProj_apply]
  constructor
  · intro h _; linarith [h]
  · intro h; linarith [h PUnit.unit]

private theorem f_mem_057 : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Agent057.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), Bool, inferInstance,
    fun b => if b then {x : Fin 1 → ℝ | 0 ≤ x 0} else {x : Fin 1 → ℝ | x 0 ≤ 0},
    fun b => if b then idAff else AffineMap.const ℝ (Fin 1 → ℝ) (0 : ℝ),
    ?_, ?_, ?_⟩
  · intro b; cases b with
    | false => exact hpoly_le0
    | true => exact hpoly_ge0
  · refine Set.eq_univ_iff_forall.mpr fun x => ?_
    rcases le_total (x 0) 0 with h | h
    · exact Set.mem_iUnion.mpr ⟨false, h⟩
    · exact Set.mem_iUnion.mpr ⟨true, h⟩
  · intro b; cases b with
    | false =>
        intro x hx
        show max 0 (x 0) = AffineMap.const ℝ (Fin 1 → ℝ) (0 : ℝ) x
        rw [AffineMap.const_apply]
        exact max_eq_left hx
    | true =>
        intro x hx
        show max 0 (x 0) = idAff x
        rw [idAff_apply]
        exact max_eq_right hx

private theorem cpwl056_not_mem :
    (fun x : Fin 1 → ℝ => max 0 (x 0)) ∉ Agent056.CPWL 1 := by
  rintro ⟨-, m, g, hg⟩
  obtain ⟨i, hi⟩ := hg (fun _ => 0)
  have htendsto : Filter.Tendsto (fun t : ℝ => (fun _ : Fin 1 => t))
      (nhds (0 : ℝ)) (nhds (fun _ : Fin 1 => (0 : ℝ))) :=
    (continuous_pi (fun _ => continuous_id)).tendsto 0
  have hev : ∀ᶠ t in nhds (0 : ℝ), max 0 t = (g i).eval (fun _ : Fin 1 => t) :=
    htendsto.eventually hi
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  have h0 : max (0 : ℝ) 0 = (g i).eval (fun _ : Fin 1 => (0 : ℝ)) :=
    @hball 0 (by rw [dist_self]; exact hε)
  have h1 : max (0 : ℝ) (ε / 2) = (g i).eval (fun _ : Fin 1 => (ε / 2 : ℝ)) :=
    @hball (ε / 2) (by
      rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith : (0 : ℝ) < ε / 2)]; linarith)
  have h2 : max (0 : ℝ) (-(ε / 2)) = (g i).eval (fun _ : Fin 1 => (-(ε / 2) : ℝ)) :=
    @hball (-(ε / 2)) (by
      rw [Real.dist_eq, sub_zero, abs_of_neg (by linarith : -(ε / 2) < (0 : ℝ))]; linarith)
  simp only [max_self, Agent056.AffineFunctional.eval, Fin.sum_univ_one, mul_zero,
    zero_add] at h0
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ ε / 2)] at h1
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0 : ℝ))] at h2
  simp only [Agent056.AffineFunctional.eval, Fin.sum_univ_one] at h1 h2
  rw [← h0, mul_neg] at h2
  linarith [h1, h2]

theorem cpwl_ne : ∃ n, Agent056.CPWL n ≠ Agent057.CPWL n :=
  ⟨1, fun h => cpwl056_not_mem (h ▸ f_mem_057)⟩

/-! ## `statement`

`relun` shows the two `ReLUn` families are identical, and `cpwl_ne` shows the two
`CPWL` families genuinely differ (already at `n = 1`, and the same construction
should generalize to any `n ≥ 3`). This makes `Agent056`'s rendering of Theorem 2
very likely *false* as a Prop: `max 0 (x 0)` (suitably padded) lies in
`Agent056.ReLUn n (Agent056.depthBound n)` for `n ≥ 3` via a single hidden layer,
but plausibly not in `Agent056.CPWL n` by the same local-agreement argument.
Deciding the `↔` in `statement` then hinges entirely on whether `Agent057`'s
rendering is *true* for all `n ≥ 3` — i.e. on the actual content of the paper's
Theorem 2, whose proof is far beyond a single bridge file. We leave this `sorry`. -/

theorem statement :
    (∀ n, 3 ≤ n → Agent056.CPWL n = Agent056.ReLUn n (Agent056.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent057.CPWL n = Agent057.ReLUn n (Agent057.depthBound n)) := by
  sorry

end Bridge_056_057

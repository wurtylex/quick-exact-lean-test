namespace Bridge_065_066

/-! Bridge between `Agent065` and `Agent066`'s formalizations of Theorem 2.

Both agents use the *same* "local agreement with a finite affine family" reading of
`CPWL` (family (b) in `BRIDGE_SPEC.md`) and the *same* literal `depthBound` formula, so
those two obligations are provable. They differ on `ReLUn`: `Agent065` requires
*exactly* `k` hidden layers, `Agent066` allows *at most* `k`; reconciling these needs
the identity-padding lemma `x = ReLU x - ReLU (-x)`, which nobody has formalized (see
spec) and which is out of scope to build here. -/

/-- `Agent065`'s coordinate-sum affine functions are exactly the coercions of bundled
Mathlib `AffineMap`s (`Agent066`'s representation), on `Fin n → ℝ`. -/
private lemma isAffineFun_iff (n : ℕ) (f : (Fin n → ℝ) → ℝ) :
    Agent065.IsAffineFun f ↔ ∃ h : (Fin n → ℝ) →ᵃ[ℝ] ℝ, (h : (Fin n → ℝ) → ℝ) = f := by
  constructor
  · rintro ⟨a, b, hf⟩
    refine ⟨AffineMap.mk' f (∑ i, a i • LinearMap.proj i) 0 ?_, rfl⟩
    intro p'
    have h0 : f 0 = b := by simpa using hf 0
    have hlin : (∑ i, a i • LinearMap.proj i) (p' -ᵥ (0 : Fin n → ℝ)) = ∑ i, a i * p' i := by
      simp [vsub_eq_sub, sub_zero, LinearMap.sum_apply, LinearMap.smul_apply,
        LinearMap.proj_apply, smul_eq_mul]
    rw [hlin, h0, vadd_eq_add]
    exact hf p'
  · rintro ⟨h, rfl⟩
    refine ⟨fun i => h.linear (Pi.single i 1), h 0, fun x => ?_⟩
    have key : h.linear x = h x - h 0 := by
      have := h.linearMap_vsub x 0
      simpa [vsub_eq_sub] using this
    have hx : x = ∑ i, Pi.single i (x i) := (LinearMap.sum_single_apply x).symm
    have hexp : h.linear x = ∑ i, h.linear (Pi.single i (1 : ℝ)) * x i := by
      calc h.linear x = h.linear (∑ i, Pi.single i (x i)) := by rw [← hx]
        _ = ∑ i, h.linear (Pi.single i (x i)) := map_sum h.linear _ _
        _ = ∑ i, h.linear (x i • Pi.single i (1 : ℝ)) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              congr 1
              funext j
              by_cases hji : j = i
              · simp [hji, Pi.single_apply, Pi.smul_apply, smul_eq_mul]
              · simp [hji, Pi.single_apply, Pi.smul_apply, smul_eq_mul]
        _ = ∑ i, x i • h.linear (Pi.single i (1 : ℝ)) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              exact map_smul h.linear (x i) _
        _ = ∑ i, h.linear (Pi.single i (1 : ℝ)) * x i := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [smul_eq_mul, mul_comm]
    have hxeq : h x = h.linear x + h 0 := by linarith [key]
    rw [hxeq, hexp]

theorem cpwl (n : ℕ) : Agent065.CPWL n = Agent066.CPWL n := by
  ext f
  constructor
  · rintro ⟨hf, m, g, hg, hloc⟩
    refine ⟨hf, m, fun i => ((isAffineFun_iff n (g i)).1 (hg i)).choose, fun x => ?_⟩
    obtain ⟨i, hi⟩ := hloc x
    refine ⟨i, ?_⟩
    have hcoe := ((isAffineFun_iff n (g i)).1 (hg i)).choose_spec
    exact hi.mono (fun y hy => hy.trans (congrFun hcoe.symm y))
  · rintro ⟨hf, m, g, hloc⟩
    refine ⟨hf, m, fun i => (g i : (Fin n → ℝ) → ℝ), fun i => (isAffineFun_iff n _).2 ⟨g i, rfl⟩,
      fun x => ?_⟩
    obtain ⟨i, hi⟩ := hloc x
    exact ⟨i, hi⟩

/- `Agent065.ReLUn n k` requires *exactly* `k` hidden layers (the `ReLUNetwork`
structure pins `dims_last : dims (k+1) = 1`), while `Agent066.ReLUn n k` allows *at
most* `k` (`∃ k' ≤ k, ReLUComputable n k' f`). These only coincide via the
identity-padding trick noted in the spec (`x = ReLU x - ReLU (-x)` lets an extra
hidden layer act as the identity, so exact-depth classes are monotone in `k` and their
union over `k' ≤ k` collapses back to exact depth `k`). That padding construction —
threading fresh block-diagonal matrices through both agents' distinct recursive network
encodings — is a genuine but currently unproved lemma (per the spec, nobody has proved
it), so we leave this as `sorry` rather than fake it. -/
theorem relun (n k : ℕ) : Agent065.ReLUn n k = Agent066.ReLUn n k := by
  sorry

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent065.depthBound n = Agent066.depthBound n := rfl

theorem statement :
    (∀ n, 3 ≤ n → Agent065.CPWL n = Agent065.ReLUn n (Agent065.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent066.CPWL n = Agent066.ReLUn n (Agent066.depthBound n)) := by
  constructor
  · intro h n hn
    rw [← cpwl n, h n hn, relun n (Agent065.depthBound n), depth n hn]
  · intro h n hn
    rw [cpwl n, h n hn, ← depth n hn, ← relun n (Agent065.depthBound n)]

end Bridge_065_066

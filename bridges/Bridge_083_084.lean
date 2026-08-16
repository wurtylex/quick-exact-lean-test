namespace Bridge_083_084

/- ## `depth`

Both agents define `depthBound n` with the literally identical term
`⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1` (083 as `def`, 084 as `noncomputable def`; the
`noncomputable` annotation does not affect definitional equality). -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent083.depthBound n = Agent084.depthBound n := rfl

/- ## `relun` — REFUTED

Both encode `ReLUNet`/`IsReLUNetworkOutput` as the same alternating affine/ReLU
recursion, but 084's `ReLUn` places the network witness *inside* the `∀ x`:
`ReLUn n k := {f | ∃ k' ≤ k, ∀ x, IsReLUNetworkOutput n k' x (f x)}`.
At `k' = 0`, `IsReLUNetworkOutput n 0 x y := ∃ T : AffineLayer n 1, T.eval x 0 = y`
is true for *every* `x, y` (take the zero matrix and bias `y`), so this per-point
existential is vacuous and `Agent084.ReLUn n k = Set.univ` for every `n k`.
083's `ReLUn` instead requires *one fixed* net for all `x`
(`∃ j ≤ k, ∃ net, ∀ x, f x = net.eval x`), so at `k = 0` it is exactly the affine
functions. The non-affine function `x ↦ (x 0)^2` on `Fin 1 → ℝ` separates them. -/
theorem relun_ne : ∃ n k, Agent083.ReLUn n k ≠ Agent084.ReLUn n k := by
  refine ⟨1, 0, ?_⟩
  intro hEq
  set f : (Fin 1 → ℝ) → ℝ := fun x => x 0 * x 0 with hf
  have hmem84 : f ∈ Agent084.ReLUn 1 0 := by
    refine ⟨0, le_refl 0, ?_⟩
    intro x
    show ∃ T : Agent084.AffineLayer 1 1, T.eval x 0 = f x
    refine ⟨⟨0, fun _ => f x⟩, ?_⟩
    simp [Agent084.AffineLayer.eval, Matrix.mulVec, Matrix.dotProduct, Matrix.zero_apply]
  have hmem83 : f ∈ Agent083.ReLUn 1 0 := by rw [hEq]; exact hmem84
  obtain ⟨j, hj0, net, hx⟩ := hmem83
  have hj : j = 0 := Nat.le_zero.mp hj0
  subst hj
  cases net with
  | output T =>
    have h0 := hx (fun _ => (0 : ℝ))
    have h1 := hx (fun _ => (1 : ℝ))
    have h2 := hx (fun _ => (2 : ℝ))
    simp only [hf, Agent083.ReLUNet.eval, Agent083.AffineTransform.apply, Pi.add_apply,
      Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_one] at h0 h1 h2
    nlinarith [h0, h1, h2]

/- ## `cpwl` — SORRY

`Agent084.CPWL` is built on `Polyhedron.mem`, whose body `∀ H ∈ P, H.mem x` needs a
`Membership (Halfspace n) (Polyhedron n)` instance; since `Polyhedron n` is a plain
`def` (semireducible) for `List (Halfspace n)` rather than an `abbrev`, Lean's
instance-transparency typeclass search cannot unfold it to find `List`'s `Membership`
instance, so this is exactly the elaboration failure noted in the task: `Polyhedron.mem`
(and hence `Agent084.CPWL`, which calls `(P i).mem x`) does not honestly elaborate, and
whatever term ends up registered for `Agent084.CPWL` after error recovery has no
reliable mathematical content to reason about. Separately, even if that bug were fixed,
083 allows *arbitrary* convex closed pieces while 084 restricts to finite-halfspace
polyhedra, a real (if plausibly bridgeable via a triangulation/polyhedral-refinement
argument) difference that nobody has proved. Both obstructions make an honest proof or
refutation infeasible here. -/
theorem cpwl (n : ℕ) : Agent083.CPWL n = Agent084.CPWL n := by
  sorry

/- ## `statement` — SORRY

Both directions of this iff quantify over `Agent084.CPWL`, which inherits the same
`Polyhedron`/`Membership` elaboration failure documented above; there is no reliable
term to reason about, so this obligation is left open rather than faked. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent083.CPWL n = Agent083.ReLUn n (Agent083.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent084.CPWL n = Agent084.ReLUn n (Agent084.depthBound n)) := by
  sorry

end Bridge_083_084

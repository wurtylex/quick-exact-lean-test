namespace Star_093

/-- Package a coefficient vector and a constant as one of the agent's affine functionals. -/
private def mkAff {n : ℕ} (a : Fin n → ℝ) (b : ℝ) : Agent093.AffFun n :=
  show (Fin 1 → Fin n → ℝ) × (Fin 1 → ℝ) from (fun _ => a, fun _ => b)

private lemma mkAff_eval {n : ℕ} (a : Fin n → ℝ) (b : ℝ) (x : Fin n → ℝ) :
    (mkAff a b).eval x = (∑ j, a j * x j) + b := rfl

/-! ## Polyhedra

`Agent093.IsPolyhedron` cuts out `{x | ∀ i, (H i).eval x ≤ 0}` with affine functionals,
`Ref.IsPolyhedron` intersects halfspaces `{x | ∑ a i * x i ≤ b}`.  Moving the constant
across the inequality identifies the two. -/

private lemma poly_agent_to_ref {n : ℕ} {S : Set (Fin n → ℝ)}
    (h : Agent093.IsPolyhedron n S) : Ref.IsPolyhedron n S := by
  obtain ⟨m, H, rfl⟩ := h
  refine ⟨m, fun i => {x | (∑ j, (H i).1 0 j * x j) ≤ -((H i).2 0)},
    fun i => ⟨fun j => (H i).1 0 j, -((H i).2 0), rfl⟩, ?_⟩
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iInter]
  constructor
  · intro hx i
    have h2 : (∑ j, (H i).1 0 j * x j) + (H i).2 0 ≤ 0 := hx i
    linarith
  · intro hx i
    have h2 : (∑ j, (H i).1 0 j * x j) ≤ -((H i).2 0) := hx i
    show (∑ j, (H i).1 0 j * x j) + (H i).2 0 ≤ 0
    linarith

private lemma poly_ref_to_agent {n : ℕ} {S : Set (Fin n → ℝ)}
    (h : Ref.IsPolyhedron n S) : Agent093.IsPolyhedron n S := by
  obtain ⟨m, H, hH, rfl⟩ := h
  choose a b hab using hH
  refine ⟨m, fun i => mkAff (a i) (-(b i)), ?_⟩
  ext x
  simp only [Set.mem_iInter, hab, Set.mem_setOf_eq]
  constructor
  · intro hx i
    rw [mkAff_eval]
    linarith [hx i]
  · intro hx i
    have h2 := hx i
    rw [mkAff_eval] at h2
    linarith

/-! ## CPWL

The two `CPWL` definitions differ only in bookkeeping: the agent stores the affine pieces
as data (`AffFun n`) and the reference as functions satisfying `IsAffine`. -/

/-- The agent's `CPWL` agrees with the reference's. -/
theorem cpwl (n : ℕ) : Agent093.CPWL n = Ref.CPWL n := by
  ext f
  constructor
  · rintro ⟨hc, m, S, L, hcov, hpoly, hagree⟩
    refine ⟨hc, m, S, fun i => (L i).eval, ?_, ?_, ?_, ?_⟩
    · exact fun i => poly_agent_to_ref (hpoly i)
    · exact fun i => ⟨fun j => (L i).1 0 j, (L i).2 0, fun _ => rfl⟩
    · exact hcov
    · exact hagree
  · rintro ⟨hc, m, P, g, hpoly, haff, hcov, hagree⟩
    choose a b hab using haff
    refine ⟨hc, m, P, fun i => mkAff (a i) (b i), ?_, ?_, ?_⟩
    · exact hcov
    · exact fun i => poly_ref_to_agent (hpoly i)
    · intro i x hx
      show f x = (mkAff (a i) (b i)).eval x
      rw [mkAff_eval, hagree i x hx, hab i x]

/-! ## ReLU networks

The agent's `Layers a ws b` is an inductive chain of affine maps with hidden widths `ws`;
the reference's `ComputedBy n k f` is the same alternating composition, recursively on the
number `k` of hidden layers.  Both classes then take *at most* `k` hidden layers, so the
two translations below suffice — no padding identity is needed. -/

/-- Every coordinate of a layer chain is computed by a reference network with `ws.length`
hidden layers. -/
private lemma net_to_ref : ∀ {a : ℕ} {ws : List ℕ} {b : ℕ} (L : Agent093.Layers a ws b)
    (i : Fin b), Ref.ComputedBy a ws.length (fun x => L.apply x i) := by
  intro a ws b L
  induction L with
  | last a' b' T =>
      intro i
      exact show ∃ T' : Ref.Aff a' 1, ∀ x, T.apply x i = T'.eval x 0 from
        ⟨⟨fun _ => T.1 i, fun _ => T.2 i⟩, fun _ => rfl⟩
  | cons a' b' ws' m T rest ih =>
      intro i
      exact show ∃ (p : ℕ) (T' : Ref.Aff a' p) (g : (Fin p → ℝ) → ℝ),
          Ref.ComputedBy p ws'.length g ∧
            ∀ x, rest.apply (Agent093.reluVec (T.apply x)) i = g (Ref.reluVec (T'.eval x)) from
        ⟨m, ⟨T.1, T.2⟩, fun y => rest.apply y i, ih i, fun _ => rfl⟩

/-- Conversely, a reference network with `j` hidden layers is a layer chain whose width
list has length `j`. -/
private lemma net_of_ref : ∀ (j : ℕ) {n : ℕ} {f : (Fin n → ℝ) → ℝ}, Ref.ComputedBy n j f →
    ∃ ws : List ℕ, ws.length = j ∧ ∃ L : Agent093.Layers n ws 1, f = fun x => L.apply x 0 := by
  intro j
  induction j with
  | zero =>
      intro n f hf
      obtain ⟨T, hT⟩ : ∃ T : Ref.Aff n 1, ∀ x, f x = T.eval x 0 := hf
      exact ⟨[], rfl, Agent093.Layers.last (T.M, T.c), funext fun x => hT x⟩
  | succ j ih =>
      intro n f hf
      obtain ⟨m, T, g, hg, hfg⟩ : ∃ (m : ℕ) (T : Ref.Aff n m) (g : (Fin m → ℝ) → ℝ),
          Ref.ComputedBy m j g ∧ ∀ x, f x = g (Ref.reluVec (T.eval x)) := hf
      obtain ⟨ws, hlen, L, hL⟩ := ih hg
      subst hL
      exact ⟨m :: ws, by simp [hlen], Agent093.Layers.cons m (T.M, T.c) L, funext fun x => hfg x⟩

/-- The agent's `ReLUn` agrees with the reference's. -/
theorem relun (n k : ℕ) : Agent093.ReLUn n k = Ref.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨ws, hlen, L, rfl⟩
    exact show ∃ j ≤ k, Ref.ComputedBy n j (fun x => L.apply x 0) from
      ⟨ws.length, hlen, net_to_ref L 0⟩
  · rintro ⟨j, hj, hcb⟩
    obtain ⟨ws, hlen, L, hL⟩ := net_of_ref j hcb
    exact ⟨ws, by omega, L, hL⟩

/-! ## Depth bound and the statement -/

/-- The two depth bounds are the same expression. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent093.depthBound n = Ref.depthBound n := rfl

theorem statement :
    (∀ n, 3 ≤ n → Agent093.CPWL n = Agent093.ReLUn n (Agent093.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
  constructor
  · intro h n hn
    rw [← cpwl, ← relun, ← depth n hn]
    exact h n hn
  · intro h n hn
    rw [cpwl, relun, depth n hn]
    exact h n hn

end Star_093

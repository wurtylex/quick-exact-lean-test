namespace Star_071

/-! ## Comparison of `Agent071` with `Ref`

`Agent071.CPWL` is the *local agreement* (neighbourhood) variant: `f` must agree,
near every point, with one member of a fixed finite family of affine maps.  On
connected `ℝⁿ` that forces `f` to be globally affine, so it is strictly stronger
than the reference notion.  Hence `cpwl` is **false** (see `cpwl_ne`), and in fact
the agent's own Theorem 2 is false (see `agent_side_false`). -/

/-- The kink obstruction: `max 0 ·` is not affine on any neighbourhood of `0`. -/
private lemma kink (ε : ℝ) (hε : 0 < ε) (A b : ℝ)
    (h : ∀ t : ℝ, |t| < ε → max 0 t = A * t + b) : False := by
  have h0 := h 0 (by rwa [abs_zero])
  rw [max_self, mul_zero, zero_add] at h0
  have hp := h (ε / 2) (by rw [abs_of_pos (by linarith)]; linarith)
  rw [max_eq_right (by linarith : (0:ℝ) ≤ ε / 2)] at hp
  have hn := h (-(ε / 2)) (by rw [abs_of_neg (by linarith)]; linarith)
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0:ℝ)), mul_neg] at hn
  linarith

/-- `fun x => max 0 (x 0)` is never in the agent's neighbourhood-`CPWL`. -/
private lemma not_mem_cpwl (n : ℕ) (hn : 0 < n) :
    (fun x : Fin n → ℝ => max 0 (x ⟨0, hn⟩)) ∉ Agent071.CPWL n := by
  rintro ⟨-, m, g, hg, hall⟩
  obtain ⟨j, U, hU, hEq⟩ := hall 0
  obtain ⟨a, b, hab⟩ := hg j
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  refine kink ε hε (∑ i, a i) b ?_
  intro t ht
  have hmem : (fun _ : Fin n => t) ∈ U := by
    refine hball ?_
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro i
    simpa [Real.dist_eq] using ht
  have key := hEq hmem
  rw [hab] at key
  rw [Finset.sum_mul]
  exact key

/-- A two-halfspace cover of `ℝ¹`. -/
private def P2 : Fin 2 → Set (Fin 1 → ℝ) := fun i =>
  if (i : ℕ) = 0 then {x | (∑ j, (1:ℝ) * x j) ≤ 0} else {x | (∑ j, (-1:ℝ) * x j) ≤ 0}

private def g2 : Fin 2 → ((Fin 1 → ℝ) → ℝ) := fun i =>
  if (i : ℕ) = 0 then (fun _ => 0) else (fun x => x 0)

private lemma P2_poly (i : Fin 2) : Ref.IsPolyhedron 1 (P2 i) := by
  unfold P2; split
  · exact ⟨1, fun _ => {x : Fin 1 → ℝ | (∑ j, (1:ℝ) * x j) ≤ 0},
      fun _ => ⟨fun _ => 1, 0, rfl⟩, (Set.iInter_const _).symm⟩
  · exact ⟨1, fun _ => {x : Fin 1 → ℝ | (∑ j, (-1:ℝ) * x j) ≤ 0},
      fun _ => ⟨fun _ => -1, 0, rfl⟩, (Set.iInter_const _).symm⟩

private lemma g2_affine (i : Fin 2) : Ref.IsAffine (g2 i) := by
  unfold g2; split
  · exact ⟨fun _ => 0, 0, by intro x; simp⟩
  · exact ⟨fun _ => 1, 0, by intro x; simp [Fin.sum_univ_one]⟩

/-- `fun x => max 0 (x 0)` *is* in the reference `CPWL 1`. -/
private lemma witness_mem_ref : (fun x : Fin 1 → ℝ => max 0 (x 0)) ∈ Ref.CPWL 1 := by
  refine ⟨continuous_const.max (continuous_apply 0), 2, P2, g2, P2_poly, g2_affine, ?_, ?_⟩
  · refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
    rcases le_or_gt (x 0) 0 with h | h
    · refine ⟨0, ?_⟩
      show (∑ j, (1:ℝ) * x j) ≤ 0
      rw [Fin.sum_univ_one, one_mul]; exact h
    · refine ⟨1, ?_⟩
      show (∑ j, (-1:ℝ) * x j) ≤ 0
      rw [Fin.sum_univ_one]; linarith
  · intro i x hx
    fin_cases i
    · have h2 : (∑ j, (1:ℝ) * x j) ≤ 0 := hx
      rw [Fin.sum_univ_one, one_mul] at h2
      show max 0 (x 0) = 0
      exact max_eq_left h2
    · have h2 : (∑ j, (-1:ℝ) * x j) ≤ 0 := hx
      rw [Fin.sum_univ_one] at h2
      show max 0 (x 0) = x 0
      exact max_eq_right (by linarith)

/-- The two notions of `CPWL` differ: the agent's is strictly stronger. -/
theorem cpwl_ne : ∃ n, Agent071.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => not_mem_cpwl 1 Nat.one_pos ?_⟩
  rw [h]; exact witness_mem_ref

/-! ### The agent's Theorem 2 is outright false -/

private def wid : Fin 3 → ℕ := fun i => if (i : ℕ) = 0 then 3 else 1

private lemma wid_pos (i : Fin 3) : 0 < wid i := by unfold wid; split <;> norm_num

private lemma wid_le (i : Fin 3) : wid i ≤ 3 := by unfold wid; split <;> norm_num

/-- Each layer copies the first coordinate. -/
private def lay (i : Fin 2) : Agent071.AffineMap (wid i.castSucc) (wid i.succ) where
  A := fun p q => if (p : ℕ) = 0 ∧ (q : ℕ) = 0 then 1 else 0
  c := fun _ => 0

private lemma sum_pick {m : ℕ} (hm : 0 < m) (v : Fin m → ℝ) (c : ℕ) (hc : c = 0) :
    (∑ j : Fin m, (if c = 0 ∧ (j : ℕ) = 0 then (1:ℝ) else 0) * v j) = v ⟨0, hm⟩ := by
  subst hc
  rw [Finset.sum_eq_single (⟨0, hm⟩ : Fin m)]
  · simp
  · intro d _ hne
    have hd : (d : ℕ) ≠ 0 := by simpa [Fin.ext_iff] using hne
    simp [hd]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma lay_eval (i : Fin 2) (v : Fin (wid i.castSucc) → ℝ) (p : Fin (wid i.succ)) :
    (lay i).eval v p = v ⟨0, wid_pos i.castSucc⟩ := by
  have hne : ((i.succ : Fin 3) : ℕ) ≠ 0 := by simp [Fin.val_succ]
  have hw : wid i.succ = 1 := by unfold wid; exact if_neg hne
  have hp : (p : ℕ) = 0 := by
    have h2 : (p : ℕ) < 1 := lt_of_lt_of_le p.isLt hw.le
    omega
  show (∑ j, (if (p : ℕ) = 0 ∧ (j : ℕ) = 0 then (1:ℝ) else 0) * v j) + 0
      = v ⟨0, wid_pos i.castSucc⟩
  rw [add_zero]
  exact sum_pick (wid_pos i.castSucc) v (p : ℕ) hp

private def netz (x : Fin 3 → ℝ) : (i : Fin 3) → Fin (wid i) → ℝ := fun i j =>
  if (i : ℕ) = 0 then x ⟨(j : ℕ), lt_of_lt_of_le j.isLt (wid_le i)⟩ else max 0 (x 0)

private lemma relu_coord_mem :
    (fun x : Fin 3 → ℝ => max 0 (x 0)) ∈ Agent071.ReLUn 3 (Agent071.depthBound 3) := by
  refine ⟨1, by unfold Agent071.depthBound; exact Nat.le_add_left 1 _,
    wid, rfl, rfl, lay, fun x => ⟨netz x, ?_, ?_, ?_, ?_⟩⟩
  · funext j; rfl
  · intro i hi
    fin_cases i
    · funext p
      show max 0 (x 0) = Agent071.relu ((lay 0).eval (netz x (Fin.castSucc 0)) p)
      rw [lay_eval]; rfl
    · exact absurd hi (by decide)
  · intro i hi
    fin_cases i
    · exact absurd hi (by decide)
    · funext p
      rw [lay_eval]; rfl
  · rfl

/-- The agent's own Theorem 2 is false: `relu ∘ (· 0)` is a one-hidden-layer
network, hence in `ReLUn 3 (depthBound 3)`, but its kink at the origin keeps it
out of the neighbourhood-`CPWL`. -/
theorem agent_side_false :
    ¬ (∀ n, 3 ≤ n → Agent071.CPWL n = Agent071.ReLUn n (Agent071.depthBound n)) := by
  intro h
  have hmem := relu_coord_mem
  rw [← h 3 le_rfl] at hmem
  exact not_mem_cpwl 3 (by norm_num) hmem

/-- Both files write `⌈Real.logb 3 (n-1)⌉₊ + 1` verbatim. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent071.depthBound n = Ref.depthBound n := rfl

-- `sorry`: both sides mean "at most `k` hidden layers", but `Agent071` encodes a
-- network as a width sequence `w : Fin (k+2) → ℕ` with dependently typed layers,
-- while `Ref` uses a recursive composition.  Identifying the two sets needs an
-- induction on `k` translating one representation into the other.
theorem relun (n k : ℕ) : Agent071.ReLUn n k = Ref.ReLUn n k := sorry

-- `sorry`: by `agent_side_false` the left-hand side is `False`, so this iff is
-- equivalent to the *negation* of the reference Theorem 2 — i.e. the statement is
-- in fact false, but refuting it requires proving Ref's Theorem 2, the whole
-- content of the paper, which is `sorry`-ed in the reference file.
theorem statement :
    (∀ n, 3 ≤ n → Agent071.CPWL n = Agent071.ReLUn n (Agent071.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_071

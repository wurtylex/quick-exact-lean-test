namespace Star_069

/-! ## `ReLUn` : the two encodings agree

`Agent069` builds networks as an indexed inductive type `ReLUNet n 1 k`, while
`Ref` uses the recursive predicate `Ref.ComputedBy n k`.  Both take "at most `k`
hidden layers" in `ReLUn`, so no padding lemma is needed: the two are literally
the same alternating composition, and the translation is a plain induction. -/

/-- A `Ref`-style network with exactly `k` hidden layers is the same thing as an
`Agent069.ReLUNet n 1 k`. -/
private lemma computedBy_iff (k : ℕ) : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Ref.ComputedBy n k f ↔ ∃ net : Agent069.ReLUNet n 1 k, ∀ x, f x = net.eval x 0 := by
  induction k with
  | zero =>
      intro n f
      constructor
      · rintro ⟨T, hT⟩
        exact ⟨Agent069.ReLUNet.last ⟨T.M, T.c⟩, hT⟩
      · rintro ⟨net, hnet⟩
        cases net with
        | last T => exact ⟨⟨T.A, T.c⟩, hnet⟩
  | succ k ih =>
      intro n f
      constructor
      · rintro ⟨m, T, g, hg, hf⟩
        obtain ⟨net, hnet⟩ := (ih m g).1 hg
        refine ⟨Agent069.ReLUNet.cons ⟨T.M, T.c⟩ net, fun x => ?_⟩
        rw [hf x]
        exact hnet _
      · rintro ⟨net, hnet⟩
        cases net with
        | cons T rest =>
            exact ⟨_, ⟨T.A, T.c⟩, fun y => rest.eval y 0,
              (ih _ _).2 ⟨rest, fun _ => rfl⟩, fun x => hnet x⟩

theorem relun (n k : ℕ) : Agent069.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent069.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, hnet⟩
    exact ⟨j, hj, (computedBy_iff j n f).2 hnet⟩
  · rintro ⟨j, hj, hc⟩
    exact ⟨j, hj, (computedBy_iff j n f).1 hc⟩

/-! ## `depthBound` : syntactically identical -/

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent069.depthBound n = Ref.depthBound n := rfl

/-! ## `CPWL` : `Agent069` is strictly stronger, so the claim is false

`Agent069.CPWL` asks for agreement with one affine piece on a *neighbourhood* of
every point.  On connected `ℝⁿ` that forces global affineness, so it misses the
genuine piecewise-linear function `x ↦ max 0 (x 0)`. -/

/-- The separating witness `x ↦ max 0 (x 0)` on `ℝ¹`. -/
private noncomputable def wit : (Fin 1 → ℝ) → ℝ := fun x => Ref.relu (x 0)

private lemma wit_cont : Continuous wit := by
  have h : Continuous fun x : Fin 1 → ℝ => max 0 (x 0) :=
    continuous_const.max (continuous_apply 0)
  exact h

private lemma halfspace_poly {n : ℕ} {S : Set (Fin n → ℝ)} (h : Ref.IsHalfspace n S) :
    Ref.IsPolyhedron n S :=
  ⟨1, fun _ => S, fun _ => h, by ext x; simp⟩

/-- `wit` is continuous piecewise-linear in the reference (polyhedral-cover) sense. -/
private lemma wit_mem_ref : wit ∈ Ref.CPWL 1 := by
  refine ⟨wit_cont, 2,
    ![{x : Fin 1 → ℝ | (∑ i, (1:ℝ) * x i) ≤ 0}, {x : Fin 1 → ℝ | (∑ i, (-1:ℝ) * x i) ≤ 0}],
    ![fun _ => (0:ℝ), fun x => x 0], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact halfspace_poly ⟨fun _ => (1:ℝ), 0, rfl⟩
    · exact halfspace_poly ⟨fun _ => (-1:ℝ), 0, rfl⟩
  · intro i
    fin_cases i
    · exact ⟨0, 0, fun x => by
        show (0:ℝ) = (∑ i, (0 : Fin 1 → ℝ) i * x i) + 0
        simp⟩
    · exact ⟨fun _ => (1:ℝ), 0, fun x => by
        show x 0 = (∑ i, (1:ℝ) * x i) + 0
        simp⟩
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    rcases le_total (x 0) 0 with h | h
    · refine ⟨0, ?_⟩
      show (∑ i, (1:ℝ) * x i) ≤ 0
      simpa [Fin.sum_univ_one] using h
    · refine ⟨1, ?_⟩
      show (∑ i, (-1:ℝ) * x i) ≤ 0
      simp only [Fin.sum_univ_one, neg_mul, one_mul]
      linarith
  · intro i
    fin_cases i
    · show ∀ x ∈ {x : Fin 1 → ℝ | (∑ i, (1:ℝ) * x i) ≤ 0}, wit x = (0:ℝ)
      intro x hx
      simp only [Set.mem_setOf_eq, Fin.sum_univ_one, one_mul] at hx
      show max 0 (x 0) = 0
      exact max_eq_left hx
    · show ∀ x ∈ {x : Fin 1 → ℝ | (∑ i, (-1:ℝ) * x i) ≤ 0}, wit x = x 0
      intro x hx
      simp only [Set.mem_setOf_eq, Fin.sum_univ_one, neg_mul, one_mul] at hx
      show max 0 (x 0) = x 0
      exact max_eq_right (by linarith)

/-- `wit` fails the neighbourhood-agreement condition at the origin: local
agreement with a single affine map on a ball around `0` forces `b = 0`, `a = 1`
and simultaneously `a * (-ε/2) = 0`, which is absurd. -/
private lemma wit_not_mem_agent : wit ∉ Agent069.CPWL 1 := by
  rintro ⟨-, m, g, hg, hloc⟩
  obtain ⟨i, hi⟩ := hloc 0
  obtain ⟨a, b, hab⟩ := hg i
  have hcont : Continuous (fun t : ℝ => (fun _ => t : Fin 1 → ℝ)) :=
    continuous_pi fun _ => continuous_id
  have ht : Filter.Tendsto (fun t : ℝ => (fun _ => t : Fin 1 → ℝ)) (nhds 0) (nhds 0) :=
    hcont.tendsto 0
  have hev : ∀ᶠ t : ℝ in nhds 0, max 0 t = a 0 * t + b := by
    filter_upwards [ht.eventually hi] with t ht'
    simpa [wit, Ref.relu, hab, Fin.sum_univ_one] using ht'
  obtain ⟨ε, hε, hmain⟩ := Metric.eventually_nhds_iff.1 hev
  have hd : ∀ t : ℝ, |t| < ε → dist t 0 < ε := by
    intro t h
    rwa [Real.dist_eq, sub_zero]
  have hb : b = 0 := by
    simpa using (hmain (hd 0 (by simpa using hε))).symm
  subst hb
  have hp := hmain (hd (ε / 2) (by rw [abs_of_pos (by linarith)]; linarith))
  have hn := hmain (hd (-(ε / 2)) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith))
  rw [max_eq_right (by linarith : (0:ℝ) ≤ ε / 2)] at hp
  rw [max_eq_left (by linarith : -(ε / 2) ≤ (0:ℝ))] at hn
  linarith

/-- `Agent069.CPWL` is **not** the reference `CPWL`: at `n = 1` the function
`x ↦ max 0 (x 0)` lies in `Ref.CPWL 1` but not in `Agent069.CPWL 1`. -/
theorem cpwl_ne : ∃ n, Agent069.CPWL n ≠ Ref.CPWL n := by
  refine ⟨1, fun h => wit_not_mem_agent ?_⟩
  rw [h]
  exact wit_mem_ref

/-! ## The statement-level comparison -/

/-- Honest `sorry`.  `cpwl_ne` shows the two `CPWL`s differ, and the left-hand
side is in fact false (`Agent069.CPWL n` contains only globally affine maps,
while `ReLUn n (depthBound n)` contains `max 0 (x 0)`).  But deciding the `↔`
also requires knowing the truth value of the right-hand side, which is exactly
`Ref.theorem2` — the unproved paper theorem.  Neither `statement` nor
`statement_ne` is available without it, so this is left open rather than routed
through a `sorry`-ed `theorem2`. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent069.CPWL n = Agent069.ReLUn n (Agent069.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := sorry

end Star_069

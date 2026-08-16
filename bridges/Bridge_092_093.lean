namespace Bridge_092_093

/-! `depthBound`: both agents write `⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1` (`⌈·⌉₊` is notation
for `Nat.ceil`), so the definitions are syntactically identical. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent092.depthBound n = Agent093.depthBound n := by
  unfold Agent092.depthBound Agent093.depthBound
  rfl

/-- `Agent092` requires *exactly* `k` hidden layers, `Agent093` allows *at most* `k`.
Relating the two needs a padding lemma (an extra hidden layer can be made to act as the
identity, e.g. `x = ReLU x - ReLU (-x)`) which neither agent proved; not attempted here
within budget. -/
theorem relun (n k : ℕ) : Agent092.ReLUn n k = Agent093.ReLUn n k := by
  sorry

/-- Helper: the affine functional `x ↦ a * x 0 + b` on `ℝ^1`, in `Agent093`'s encoding. -/
def mkAff093 (a b : ℝ) : Agent093.AffFun 1 := (fun _ _ => a, fun _ => b)

theorem mkAff093_eval (a b : ℝ) (x : Fin 1 → ℝ) :
    Agent093.AffFun.eval (mkAff093 a b) x = a * x 0 + b := by
  simp [Agent093.AffFun.eval, Agent093.AffineMap'.apply, mkAff093, Fin.sum_univ_one]

/-- The coordinate ReLU on `ℝ^1`: witnesses that `Agent092.CPWL` and `Agent093.CPWL`
disagree. -/
def reluFun : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

theorem reluFun_continuous : Continuous reluFun :=
  continuous_const.max (continuous_apply 0)

def Sset : Fin 2 → Set (Fin 1 → ℝ) := ![{x | (0 : ℝ) ≤ x 0}, {x | x 0 ≤ 0}]
def Laff : Fin 2 → Agent093.AffFun 1 := ![mkAff093 1 0, mkAff093 0 0]

/-- `reluFun` sits in `Agent093.CPWL 1`: `{x 0 ≥ 0}` and `{x 0 ≤ 0}` form a polyhedral
subdivision on which `reluFun` is respectively `x 0` and `0`. -/
theorem reluFun_mem_093 : reluFun ∈ Agent093.CPWL 1 := by
  refine ⟨reluFun_continuous, 2, Sset, Laff, ?_, ?_, ?_⟩
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    rcases le_total (0 : ℝ) (x 0) with h | h
    · exact ⟨0, by simpa [Sset] using h⟩
    · exact ⟨1, by simpa [Sset] using h⟩
  · intro i
    fin_cases i
    · exact ⟨1, fun _ => mkAff093 (-1) 0, by
        ext x; simp [Sset, mkAff093_eval, neg_nonpos, Fin.forall_fin_one]⟩
    · exact ⟨1, fun _ => mkAff093 1 0, by
        ext x; simp [Sset, mkAff093_eval, Fin.forall_fin_one]⟩
  · intro i
    fin_cases i
    · intro x hx
      simp only [Sset, Matrix.cons_val_zero, Set.mem_setOf_eq] at hx
      simp [reluFun, Laff, mkAff093_eval, max_eq_right hx]
    · intro x hx
      simp only [Sset, Matrix.cons_val_one, Matrix.head_cons, Set.mem_setOf_eq] at hx
      simp [reluFun, Laff, mkAff093_eval, max_eq_left hx]

/-- `reluFun` is *not* in `Agent092.CPWL 1`: at `x = 0` no single affine function can
agree with `reluFun` on a whole neighbourhood, since `reluFun` genuinely kinks there.
This is the "local agreement forces global affine-ness" phenomenon flagged in the spec. -/
theorem reluFun_not_mem_092 : reluFun ∉ Agent092.CPWL 1 := by
  rintro ⟨-, m, g, hloc⟩
  obtain ⟨i, hi⟩ := hloc (0 : Fin 1 → ℝ)
  have hcont : Continuous (fun t : ℝ => (fun _ : Fin 1 => t)) :=
    continuous_pi (fun _ => continuous_id)
  have hc0 : (fun _ : Fin 1 => (0 : ℝ)) = (0 : Fin 1 → ℝ) := by ext j; simp
  have htendsto :
      Filter.Tendsto (fun t : ℝ => (fun _ : Fin 1 => t)) (nhds (0 : ℝ)) (nhds (0 : Fin 1 → ℝ)) := by
    have := hcont.tendsto 0
    rwa [hc0] at this
  have hev : ∀ᶠ t in nhds (0 : ℝ),
      reluFun (fun _ : Fin 1 => t) = (g i).eval (fun _ : Fin 1 => t) := htendsto.eventually hi
  obtain ⟨δ, hδ, hδp⟩ := Metric.eventually_nhds_iff.1 hev
  have evalform : ∀ t : ℝ,
      (g i).eval (fun _ : Fin 1 => t) = (g i).1 0 0 * t + (g i).2 0 := by
    intro t
    simp [Agent092.AffineFunc.eval, Agent092.affineEval, Matrix.mulVec, Matrix.dotProduct,
      Fin.sum_univ_one]
  have e0 := hδp (show dist (0 : ℝ) 0 < δ by simpa using hδ)
  have epos := hδp
    (show dist (δ / 2 : ℝ) 0 < δ by rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]; linarith)
  have eneg := hδp (show dist (-δ / 2 : ℝ) 0 < δ by
    rw [Real.dist_eq, sub_zero, abs_of_neg (by linarith : (-δ / 2 : ℝ) < 0)]; linarith)
  simp only [reluFun, evalform] at e0 epos eneg
  have hB0 : (g i).2 0 = 0 := by simpa using e0
  rw [hB0] at epos eneg
  have hApos : max (0 : ℝ) (δ / 2) = δ / 2 := max_eq_right (le_of_lt (half_pos hδ))
  rw [hApos] at epos
  have hd : (δ / 2 : ℝ) ≠ 0 := ne_of_gt (half_pos hδ)
  have h2 : (δ / 2 : ℝ) = (g i).1 0 0 * (δ / 2) := by linarith [epos]
  have h3 : (g i).1 0 0 * (δ / 2) = 1 * (δ / 2) := by rw [one_mul]; linarith [h2]
  have hA1 : (g i).1 0 0 = 1 := mul_right_cancel₀ hd h3
  rw [hA1] at eneg
  have hAneg : max (0 : ℝ) (-δ / 2) = 0 := max_eq_left (by linarith)
  rw [hAneg] at eneg
  simp only [one_mul, add_zero] at eneg
  linarith

theorem cpwl_ne : ∃ n, Agent092.CPWL n ≠ Agent093.CPWL n := by
  refine ⟨1, fun h => ?_⟩
  apply reluFun_not_mem_092
  rw [h]
  exact reluFun_mem_093

/-- Both agents' `theorem2` is `sorry`, and `cpwl_ne` shows their `CPWL` already
disagree, so independently resolving this biconditional is out of scope within budget. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent092.CPWL n = Agent092.ReLUn n (Agent092.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent093.CPWL n = Agent093.ReLUn n (Agent093.depthBound n)) := by
  sorry

end Bridge_092_093

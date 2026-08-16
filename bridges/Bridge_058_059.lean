namespace Bridge_058_059

/-!
Bridge between `Agent058` and `Agent059`'s formalizations of Theorem 2.

`depthBound` is *literally* the same definition in both files (`⌈Real.logb 3
((n:ℝ)-1)⌉₊ + 1`, `⌈x⌉₊` being notation for `Nat.ceil x`), so `depth` is `rfl`.

`CPWL` differs genuinely: Agent058 requires `f` to agree with *some single* affine
function on a full neighbourhood of every point (`∀ x, ∃ i, ∀ᶠ y in nhds x, ...`),
while Agent059 requires a finite polyhedral subdivision on each closed piece of
which `f` is affine. The kink function `x ↦ max 0 (x 0)` on `ℝ^1` separates them:
it is a textbook polyhedral-subdivision PWL function (059), but at `x = 0` no
single affine function agrees with it on a whole neighbourhood (058), since it is
genuinely kinked there. We prove `cpwl_ne` using this witness at `n = 1`.

`relun` and `statement` are left `sorry` (see comments at each).
-/

/-- The witness separating the two `CPWL` notions: `x ↦ max 0 (x 0)` on `ℝ^1`. -/
noncomputable def kink : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0)

theorem kink_continuous : Continuous kink :=
  continuous_const.max (continuous_apply (0 : Fin 1))

theorem max_zero_eq_of_nonneg {t : ℝ} (h : 0 ≤ t) : max (0 : ℝ) t = t :=
  le_antisymm (max_le h le_rfl) (le_max_right 0 t)

theorem max_zero_eq_of_nonpos {t : ℝ} (h : t ≤ 0) : max (0 : ℝ) t = 0 :=
  le_antisymm (max_le le_rfl h) (le_max_left 0 t)

/-- A single scalar inequality `a * x 0 ≤ b` on `ℝ^1` is a polyhedron. -/
theorem isPolyhedron_le (a b : ℝ) :
    Agent059.IsPolyhedron {x : Fin 1 → ℝ | a * x 0 ≤ b} := by
  refine ⟨1, fun _ _ => a, fun _ => b, Set.ext fun x => ?_⟩
  simp only [Set.mem_setOf_eq, Fin.sum_univ_one]
  exact ⟨fun h _ => h, fun h => h 0⟩

def S0 : Set (Fin 1 → ℝ) := {x | (-1 : ℝ) * x 0 ≤ 0}
def S1 : Set (Fin 1 → ℝ) := {x | (1 : ℝ) * x 0 ≤ 0}
def g0 : (Fin 1 → ℝ) → ℝ := fun x => x 0
def g1 : (Fin 1 → ℝ) → ℝ := fun _ => 0

/-- `kink` lies in Agent059's `CPWL 1`: the half-spaces `x 0 ≤ 0`/`x 0 ≥ 0` cover
`ℝ^1`, and `kink` is affine (`x 0`, resp. `0`) on each closed half-space. -/
theorem kink_mem_059 : kink ∈ Agent059.CPWL 1 := by
  refine ⟨kink_continuous, 2, ![S0, S1], ![g0, g1], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact isPolyhedron_le (-1) 0
    · exact isPolyhedron_le 1 0
  · intro i
    fin_cases i
    · exact ⟨fun _ => 1, 0, fun x => by
        show g0 x = (∑ j, (1 : ℝ) * x j) + 0
        unfold g0
        simp [Fin.sum_univ_one]⟩
    · exact ⟨fun _ => 0, 0, fun x => by
        show g1 x = (∑ j, (0 : ℝ) * x j) + 0
        unfold g1
        simp⟩
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    rcases le_total (x 0) 0 with h | h
    · exact ⟨1, show (1 : ℝ) * x 0 ≤ 0 by linarith⟩
    · exact ⟨0, show (-1 : ℝ) * x 0 ≤ 0 by linarith⟩
  · intro i
    fin_cases i
    · intro x hx
      have hx' : (-1 : ℝ) * x 0 ≤ 0 := hx
      exact max_zero_eq_of_nonneg (by linarith)
    · intro x hx
      have hx' : (1 : ℝ) * x 0 ≤ 0 := hx
      exact max_zero_eq_of_nonpos (by linarith)

/-- `kink` does *not* lie in Agent058's `CPWL 1`: no single affine function agrees
with `max 0 ·` throughout any neighbourhood of `0`, since it is the identity for
`t > 0` and constantly `0` for `t < 0`. -/
theorem kink_not_mem_058 : kink ∉ Agent058.CPWL 1 := by
  rintro ⟨-, m, g, H⟩
  obtain ⟨i, hi⟩ := H (fun _ => (0 : ℝ))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hi
  have heval : ∀ t : ℝ, (g i).eval (fun _ : Fin 1 => t) 0
      = (g i).A 0 0 * t + (g i).c 0 := by
    intro t
    simp [Agent058.AffineMapRn.eval, Matrix.mulVec, dotProduct, Fin.sum_univ_one,
      Pi.add_apply]
  have hmem : ∀ t : ℝ, |t| < ε →
      max (0 : ℝ) t = (g i).A 0 0 * t + (g i).c 0 := by
    intro t ht
    have hle : dist (fun _ : Fin 1 => t) (fun _ : Fin 1 => (0 : ℝ)) ≤ dist t (0 : ℝ) :=
      dist_pi_const_le t 0
    rw [Real.dist_eq, sub_zero] at hle
    have hballmem : (fun _ : Fin 1 => t) ∈ Metric.ball (fun _ : Fin 1 => (0 : ℝ)) ε :=
      show dist (fun _ : Fin 1 => t) (fun _ : Fin 1 => (0 : ℝ)) < ε by linarith
    have hfin := hball hballmem
    rw [← heval t]
    exact hfin
  have e1 : max (0 : ℝ) (ε / 2) = (g i).A 0 0 * (ε / 2) + (g i).c 0 :=
    hmem (ε / 2) (by rw [abs_of_pos (show (0 : ℝ) < ε / 2 by linarith)]; linarith)
  have e2 : max (0 : ℝ) (ε / 4) = (g i).A 0 0 * (ε / 4) + (g i).c 0 :=
    hmem (ε / 4) (by rw [abs_of_pos (show (0 : ℝ) < ε / 4 by linarith)]; linarith)
  have e3 : max (0 : ℝ) (-(ε / 2)) = (g i).A 0 0 * (-(ε / 2)) + (g i).c 0 :=
    hmem (-(ε / 2)) (by rw [abs_of_neg (show -(ε / 2) < (0 : ℝ) by linarith)]; linarith)
  have m1 : max (0 : ℝ) (ε / 2) = ε / 2 := max_zero_eq_of_nonneg (by linarith)
  have m2 : max (0 : ℝ) (ε / 4) = ε / 4 := max_zero_eq_of_nonneg (by linarith)
  have m3 : max (0 : ℝ) (-(ε / 2)) = 0 := max_zero_eq_of_nonpos (by linarith)
  rw [m1] at e1
  rw [m2] at e2
  rw [m3] at e3
  have g4 : (g i).A 0 0 * (ε / 4) = (g i).A 0 0 * (ε / 2) / 2 := by ring
  have g5 : (g i).A 0 0 * (-(ε / 2)) = -((g i).A 0 0 * (ε / 2)) := by ring
  linarith [e1, e2, e3, g4, g5, hε]

theorem cpwl_ne : ∃ n, Agent058.CPWL n ≠ Agent059.CPWL n := by
  refine ⟨1, fun h => kink_not_mem_058 ?_⟩
  rw [h]
  exact kink_mem_059

/-- `ReLUn`: both sides mean "at most `k` hidden layers, matrix/bias affine layers
with ReLU between them", but Agent058 encodes a network via a `widths`/`netApply`
composition while Agent059 encodes it via the recursive predicate
`ReLURepresentable`. These are the same class of functions, but proving it needs an
induction on `k` converting between the two concrete encodings term-by-term, which
is not attempted here. -/
theorem relun (n k : ℕ) : Agent058.ReLUn n k = Agent059.ReLUn n k := by
  sorry

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent058.depthBound n = Agent059.depthBound n :=
  rfl

/-- `statement`: this asks whether Agent058's Theorem 2 claim and Agent059's
Theorem 2 claim are equivalent, i.e. whether their (each individually `sorry`'d,
unproved) formalizations of the paper's actual theorem are simultaneously true or
false. Since `cpwl_ne` shows the two `CPWL` predicates genuinely differ, this is
not a formal consequence of `cpwl`/`relun`/`depth`; deciding it outright requires
the real mathematical content of the paper (Theorem 2 itself), which is out of
scope for this bridge. -/
theorem statement :
    (∀ n, 3 ≤ n → Agent058.CPWL n = Agent058.ReLUn n (Agent058.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent059.CPWL n = Agent059.ReLUn n (Agent059.depthBound n)) := by
  sorry

end Bridge_058_059

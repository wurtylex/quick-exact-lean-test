import QuickTest.Formalizations.Thm2_063
import QuickTest.Reference

namespace Star_063

/-!
`Agent063` and `Ref` make the same three modelling choices: `CPWL` is the honest
finite polyhedral subdivision, `ReLUn` is "**at most** `k` hidden layers", and the
depth bound is `⌈log₃ (n-1)⌉ + 1` written with `Nat.ceil`.  The only differences
are presentational (matrices as bare functions vs. `Matrix`, polyhedra as one
`∀ j`-set vs. an intersection of halfspaces), so all four obligations are proved.
-/

/-- `Ref.Aff.eval` is, componentwise, the same explicit sum as `Agent063.affineApply`. -/
private lemma aff_eval_apply {a b : ℕ} (T : Ref.Aff a b) (x : Fin a → ℝ) (i : Fin b) :
    T.eval x i = (∑ j, T.M i j * x j) + T.c i := rfl

/-- The two componentwise ReLUs are the same function. -/
private lemma reluVec_eq {m : ℕ} (v : Fin m → ℝ) : Agent063.reluVec v = Ref.reluVec v := rfl

/-- The two notions of scalar affine function are literally the same predicate. -/
private lemma affine_iff {n : ℕ} (g : (Fin n → ℝ) → ℝ) :
    Agent063.IsAffine n g ↔ Ref.IsAffine g := Iff.rfl

/-- A set is cut out by finitely many inequalities `aⱼ ⬝ x + bⱼ ≤ 0` iff it is a finite
intersection of closed halfspaces. -/
private lemma poly_iff (n : ℕ) (P : Set (Fin n → ℝ)) :
    Agent063.IsPolyhedron n P ↔ Ref.IsPolyhedron n P := by
  constructor
  · rintro ⟨m, a, b, rfl⟩
    refine ⟨m, fun j => {x | (∑ i, a j i * x i) ≤ -b j}, fun j => ⟨a j, -b j, rfl⟩, ?_⟩
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor <;> intro h j <;> have := h j <;> linarith
  · rintro ⟨m, H, hH, rfl⟩
    choose a b hab using hH
    refine ⟨m, a, fun j => -b j, ?_⟩
    ext x
    simp only [Set.mem_iInter, hab, Set.mem_setOf_eq]
    constructor <;> intro h j <;> have := h j <;> linarith

/-- Representability by a network with *exactly* `k` hidden layers agrees on the nose:
`Agent063.affineApply A c` is `Ref.Aff.eval ⟨A, c⟩`. -/
private lemma repr_iff : ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Agent063.Represents n k f ↔ Ref.ComputedBy n k f := by
  intro k
  induction k with
  | zero =>
    intro n f
    constructor
    · rintro ⟨c, b, hf⟩
      exact ⟨⟨Matrix.of fun _ j => c j, fun _ => b⟩, fun x => hf x⟩
    · rintro ⟨T, hf⟩
      exact ⟨fun j => T.M 0 j, T.c 0, fun x => hf x⟩
  | succ k ih =>
    intro n f
    constructor
    · rintro ⟨m, A, bvec, g, hg, hf⟩
      exact ⟨m, ⟨Matrix.of A, bvec⟩, g, (ih m g).mp hg, fun x => hf x⟩
    · rintro ⟨m, T, g, hg, hf⟩
      exact ⟨m, fun i j => T.M i j, T.c, g, (ih m g).mpr hg, fun x => hf x⟩

/-- Both files define `CPWL` as: continuous, plus a finite polyhedral cover on each piece
of which `f` is affine.  Only the encoding of "polyhedron" differs. -/
theorem cpwl (n : ℕ) : Agent063.CPWL n = Ref.CPWL n := by
  ext f
  simp only [Agent063.CPWL, Ref.CPWL, Set.mem_setOf_eq, Agent063.IsCPWL, Ref.IsCPWL]
  constructor
  · rintro ⟨hc, m, P, g, hP, hg, hcov, hagree⟩
    exact ⟨hc, m, P, g, fun j => (poly_iff n (P j)).mp (hP j),
      fun j => (affine_iff (g j)).mp (hg j), hcov, hagree⟩
  · rintro ⟨hc, m, P, g, hP, hg, hcov, hagree⟩
    exact ⟨hc, m, P, g, fun j => (poly_iff n (P j)).mpr (hP j),
      fun j => (affine_iff (g j)).mpr (hg j), hcov, hagree⟩

/-- Both files read `ReLU_{n,k}` as "at most `k` hidden layers", so this reduces to
`repr_iff` layer by layer — no padding argument is needed. -/
theorem relun (n k : ℕ) : Agent063.ReLUn n k = Ref.ReLUn n k := by
  ext f
  simp only [Agent063.ReLUn, Ref.ReLUn, Set.mem_setOf_eq]
  exact exists_congr fun j => and_congr_right fun _ => repr_iff j n f

/-- `⌈·⌉₊` is notation for `Nat.ceil`, so the two depth bounds are the same term. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent063.depthBound n = Ref.depthBound n := rfl

theorem statement :
    (∀ n, 3 ≤ n → Agent063.CPWL n = Agent063.ReLUn n (Agent063.depthBound n)) ↔
    (∀ n, 3 ≤ n → Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
  have key : ∀ n, 3 ≤ n →
      (Agent063.CPWL n = Agent063.ReLUn n (Agent063.depthBound n) ↔
        Ref.CPWL n = Ref.ReLUn n (Ref.depthBound n)) := by
    intro n hn
    rw [cpwl n, relun n (Agent063.depthBound n), depth n hn]
  exact ⟨fun h n hn => (key n hn).mp (h n hn), fun h n hn => (key n hn).mpr (h n hn)⟩

end Star_063

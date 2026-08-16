namespace Bridge_006_007

/-!
## Overview

`Agent006` and `Agent007` use essentially the same modelling choices (matrix/bias
affine transformations, "at most k hidden layers", continuity + finite local
affine agreement for `CPWL`), but differ in two purely presentational ways:

* `CPWL`: `Agent006` indexes its finite family of affine pieces by `Fin m` and
  states local agreement via `∀ᶠ y in nhds x, …`; `Agent007` indexes by a
  `Finset` and states local agreement via an explicit open set. These are
  interchangeable (`eventually_nhds_iff` for the quantifier, a `Fintype.equivFin`
  repackaging for `Fin m` vs. `Finset`), so `cpwl` is provable.
* `ReLUn`: both mean "representable by exactly `k'` hidden layers, for some
  `k' ≤ k`", but the recursive definition of "exactly `k'` hidden layers" peels
  off the *first* affine/ReLU layer in `Agent006.ComputesHidden` and the *last*
  one in `Agent007.RepresentableVec`. These describe the same class of
  functions; reconciling the two recursions is a genuine (if routine)
  associativity-of-composition induction, carried out below via a
  vector-valued generalization of `Agent006`'s recursion together with
  "prepend" / "append" lemmas.
-/

/-! ### `cpwl` -/

/-- Repackage an `Agent006` affine function as an `Agent007` one. -/
def toAffineFun {n : ℕ} (g : Agent006.AffineFunc n) : Agent007.AffineFun n :=
  (g.coeffs, g.const)

/-- Repackage an `Agent007` affine function as an `Agent006` one. -/
def toAffineFunc {n : ℕ} (a : Agent007.AffineFun n) : Agent006.AffineFunc n :=
  ⟨a.1, a.2⟩

theorem toAffineFun_eval {n : ℕ} (g : Agent006.AffineFunc n) (y : Fin n → ℝ) :
    (toAffineFun g).eval y = g.eval y := rfl

theorem toAffineFunc_eval {n : ℕ} (a : Agent007.AffineFun n) (y : Fin n → ℝ) :
    (toAffineFunc a).eval y = a.eval y := rfl

/-- The two `CPWL` definitions differ only in how the finite family of affine
pieces is indexed (`Fin m` vs. `Finset`) and how "locally agrees" is phrased
(`∀ᶠ y in nhds x, …` vs. an explicit open set); these are interchangeable. -/
theorem cpwl_inner_iff (n : ℕ) (f : (Fin n → ℝ) → ℝ) :
    (∃ (m : ℕ) (g : Fin m → Agent006.AffineFunc n),
        ∀ x : Fin n → ℝ, ∃ i, ∀ᶠ y in nhds x, f y = (g i).eval y) ↔
    (∃ S : Finset (Agent007.AffineFun n),
        ∀ x : Fin n → ℝ, ∃ a ∈ S, ∃ U : Set (Fin n → ℝ),
          IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, f y = a.eval y) := by
  classical
  constructor
  · rintro ⟨m, g, hg⟩
    refine ⟨Finset.univ.image (fun i => toAffineFun (g i)), fun x => ?_⟩
    obtain ⟨i, hi⟩ := hg x
    rw [eventually_nhds_iff] at hi
    obtain ⟨U, hU, hUopen, hxU⟩ := hi
    refine ⟨toAffineFun (g i), Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, U, hUopen, hxU,
      fun y hy => ?_⟩
    rw [toAffineFun_eval]
    exact hU y hy
  · rintro ⟨S, hS⟩
    let e : {a // a ∈ S} ≃ Fin (Fintype.card {a // a ∈ S}) := Fintype.equivFin {a // a ∈ S}
    refine ⟨Fintype.card {a // a ∈ S}, fun i => toAffineFunc (e.symm i).1, fun x => ?_⟩
    obtain ⟨a, haS, U, hUopen, hxU, hUeq⟩ := hS x
    refine ⟨e ⟨a, haS⟩, ?_⟩
    rw [eventually_nhds_iff]
    refine ⟨U, fun y hy => ?_, hUopen, hxU⟩
    have hsymm : (e.symm (e ⟨a, haS⟩)).1 = a := by rw [e.symm_apply_apply]
    rw [hsymm, toAffineFunc_eval]
    exact hUeq y hy

theorem cpwl (n : ℕ) : Agent006.CPWL n = Agent007.CPWL n := by
  ext f
  unfold Agent006.CPWL Agent007.CPWL
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hf, m, g, hg⟩
    exact ⟨hf, (cpwl_inner_iff n f).mp ⟨m, g, hg⟩⟩
  · rintro ⟨hf, S, hS⟩
    exact ⟨hf, (cpwl_inner_iff n f).mpr ⟨S, hS⟩⟩

/-! ### `relun` -/

/-- Vector-valued generalization of `Agent006.ComputesHidden`: the same
"front-peeling" recursion (peel off the *first* affine/ReLU layer, recurse on
what's left), but allowing an arbitrary output dimension `b` instead of the
fixed scalar output. `Agent006.ComputesHidden` is the special case `b = 1`
(see `computesHidden_iff_vec`). We need this general-`b` version to line it up
against `Agent007.RepresentableVec`, whose recursion peels off the *last*
affine layer instead. -/
def ComputesHiddenVec : (n k b : ℕ) → ((Fin n → ℝ) → (Fin b → ℝ)) → Prop
  | n, 0, b, f => ∃ T : Agent006.AffineTransform n b, f = Agent006.affineApply T
  | n, (k + 1), b, f =>
      ∃ (m : ℕ) (T : Agent006.AffineTransform n m) (g : (Fin m → ℝ) → (Fin b → ℝ)),
        ComputesHiddenVec m k b g ∧ f = fun x => g (Agent006.reluVec (Agent006.affineApply T x))

/-- `Agent006.ComputesHidden` is the `b = 1` case of `ComputesHiddenVec`, modulo
the trivial identification of scalars with `Fin 1 → ℝ`. -/
theorem computesHidden_iff_vec (n k : ℕ) (f : (Fin n → ℝ) → ℝ) :
    Agent006.ComputesHidden n k f ↔ ComputesHiddenVec n k 1 (fun x _ => f x) := by
  induction k generalizing n f with
  | zero =>
      constructor
      · rintro ⟨T, hT⟩
        refine ⟨T, ?_⟩
        funext x i
        fin_cases i
        exact hT x
      · rintro ⟨T, hT⟩
        exact ⟨T, fun x => congrFun (congrFun hT x) 0⟩
  | succ k ih =>
      constructor
      · rintro ⟨m, T, g, hg, hf⟩
        refine ⟨m, T, fun y _ => g y, (ih m g).mp hg, ?_⟩
        funext x i
        fin_cases i
        exact hf x
      · rintro ⟨m, T, g, hg, hf⟩
        have hg' : ComputesHiddenVec m k 1 (fun y _ => g y 0) := by
          have e : (fun y (_ : Fin 1) => g y 0) = g := by
            funext y i
            fin_cases i
            rfl
          rw [e]
          exact hg
        exact ⟨m, T, fun y => g y 0, (ih m (fun y => g y 0)).mpr hg',
          fun x => congrFun (congrFun hf x) 0⟩

/-- `Agent007.RepresentableVec` is closed under prepending an affine/ReLU layer
at the front (this is the "front-peel" content packed into `Agent006`'s
recursion, proved here for the "back-peel" definition by induction on the
layer count). -/
theorem representableVec_prepend :
    ∀ (k n m b : ℕ) (T : Agent006.AffineTransform n m) (g : (Fin m → ℝ) → (Fin b → ℝ)),
      Agent007.RepresentableVec m k b g →
      Agent007.RepresentableVec n (k + 1) b
        (fun x => g (Agent006.reluVec (Agent006.affineApply T x))) := by
  intro k
  induction k with
  | zero =>
      intro n m b T g hg
      obtain ⟨A, c, hA⟩ := hg
      refine ⟨m, Agent006.affineApply T, A, c, ⟨T.A, T.c, rfl⟩, ?_⟩
      funext x
      rw [hA]
  | succ k ih =>
      intro n m b T g hg
      obtain ⟨p, g₁, A, c, hg₁, hg⟩ := hg
      have step := ih n m p T g₁ hg₁
      refine ⟨p, fun x => g₁ (Agent006.reluVec (Agent006.affineApply T x)), A, c, step, ?_⟩
      funext x
      rw [hg]

/-- Dual to `representableVec_prepend`: `ComputesHiddenVec` is closed under
appending a final affine layer at the back. -/
theorem computesHiddenVec_append :
    ∀ (k n m b : ℕ) (A : Matrix (Fin b) (Fin m) ℝ) (c : Fin b → ℝ)
      (g : (Fin n → ℝ) → (Fin m → ℝ)),
      ComputesHiddenVec n k m g →
      ComputesHiddenVec n (k + 1) b
        (fun x => Agent007.affineEval A c (Agent006.reluVec (g x))) := by
  intro k
  induction k with
  | zero =>
      intro n m b A c g hg
      obtain ⟨T, hT⟩ := hg
      refine ⟨m, T, Agent007.affineEval A c, ⟨⟨A, c⟩, rfl⟩, ?_⟩
      funext x
      rw [hT]
  | succ k ih =>
      intro n m b A c g hg
      obtain ⟨p, T, g₁, hg₁, hg⟩ := hg
      have step := ih p m b A c g₁ hg₁
      refine ⟨p, T, fun y => Agent007.affineEval A c (Agent006.reluVec (g₁ y)), step, ?_⟩
      funext x
      rw [hg]

/-- The "front-peel" and "back-peel" recursive characterizations of "computed
by a ReLU network with exactly `k` hidden layers" agree. -/
theorem computesHiddenVec_iff_representableVec :
    ∀ (k n b : ℕ) (f : (Fin n → ℝ) → (Fin b → ℝ)),
      ComputesHiddenVec n k b f ↔ Agent007.RepresentableVec n k b f := by
  intro k
  induction k with
  | zero =>
      intro n b f
      constructor
      · rintro ⟨T, hT⟩; exact ⟨T.A, T.c, hT⟩
      · rintro ⟨A, c, hA⟩; exact ⟨⟨A, c⟩, hA⟩
  | succ k ih =>
      intro n b f
      constructor
      · rintro ⟨m, T, g, hg, hf⟩
        have hg' : Agent007.RepresentableVec m k b g := (ih m b g).mp hg
        have := representableVec_prepend k n m b T g hg'
        rwa [hf]
      · rintro ⟨m, g, A, c, hg, hf⟩
        have hg' : ComputesHiddenVec n k m g := (ih n m g).mpr hg
        have := computesHiddenVec_append k n m b A c g hg'
        rwa [hf]

theorem representable_iff (n k : ℕ) (f : (Fin n → ℝ) → ℝ) :
    Agent006.ComputesHidden n k f ↔ Agent007.Representable n k f := by
  have h := computesHiddenVec_iff_representableVec k n 1 (fun x _ => f x)
  rw [computesHidden_iff_vec]
  exact h

theorem relun (n k : ℕ) : Agent006.ReLUn n k = Agent007.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (representable_iff n j f).mp hf⟩
  · rintro ⟨j, hj, hf⟩
    exact ⟨j, hj, (representable_iff n j f).mpr hf⟩

/-! ### `depth` -/

/-- Both agents use the literally identical expression `⌈log₃(n-1)⌉₊ + 1`
(`⌈·⌉₊` is notation for `Nat.ceil`), so this holds unconditionally. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent006.depthBound n = Agent007.depthBound n := rfl

/-! ### `statement` -/

theorem statement :
    (∀ n, 3 ≤ n → Agent006.CPWL n = Agent006.ReLUn n (Agent006.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent007.CPWL n = Agent007.ReLUn n (Agent007.depthBound n)) := by
  constructor
  · intro h n hn
    rw [← cpwl n, h n hn, relun n (Agent006.depthBound n), depth n hn]
  · intro h n hn
    rw [cpwl n, h n hn, ← relun n (Agent007.depthBound n), ← depth n hn]

end Bridge_006_007

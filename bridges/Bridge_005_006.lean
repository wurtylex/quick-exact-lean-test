namespace Bridge_005_006

/-!
`Agent005` and `Agent006` use essentially the same encodings:

* `depthBound` is *literally* the same formula (`⌈log_3 (n-1)⌉₊ + 1`, with `⌈·⌉₊`
  notation for `Nat.ceil`) in both files.
* `ReLUn n k` is "representable by a network with **at most** `k` hidden layers"
  in both files, and the underlying "`k` hidden layers, exactly" predicates
  (`Agent005.computesReLU` / `Agent006.ComputesHidden`) are the same recursive
  alternating-composition definition, just packaged with a bare
  `Matrix × Vector` pair (005) vs. a `structure AffineTransform` bundling the
  same two fields (006).
* `CPWL n` is the *local-agreement* reading (family (b) from the spec) in
  *both* files: a finite family of affine scalar functions such that `f`
  agrees with one of them in a neighbourhood of every point. 005 packages the
  family as a `Finset` of functions (each separately shown affine); 006
  packages it as a `Fin m`-indexed family of `AffineFunc` structures. These
  are the same mathematical family, just enumerated differently.

Since both files sit on the same side of every axis mentioned in the spec, we
prove genuine equalities for all four obligations instead of refutations.
-/

/-- `Agent005.computesReLU k n f` and `Agent006.ComputesHidden n k f` are the same
predicate: both say "`f` is computed by an alternating composition of `k + 1`
affine maps `ℝ^n → ℝ^{m_i}` with componentwise ReLU in between", the only
difference being that 005 stores each affine map as a bare
`(Matrix, biasVector)` pair while 006 bundles the same two fields into the
`AffineTransform` structure. We prove the equivalence by induction on `k`,
matching bare pairs `(A, c)` with structures `⟨A, c⟩` at each layer; the
underlying formulas (`Matrix.mulVec`, `Pi.add`, `Finset.sum`) are literally
identical once unfolded, so each layer-matching step closes by `rfl` after
rewriting with the hypothesis. -/
theorem computesReLU_iff :
    ∀ (k n : ℕ) (f : (Fin n → ℝ) → ℝ),
      Agent005.computesReLU k n f ↔ Agent006.ComputesHidden n k f
  | 0, n, f => by
      constructor
      · rintro ⟨w, c, hf⟩
        exact ⟨⟨fun _ j => w j, fun _ => c⟩, fun x => by rw [congrFun hf x]⟩
      · rintro ⟨T, hT⟩
        exact ⟨fun j => T.A 0 j, T.c 0, funext fun x => by rw [hT x]⟩
  | (k + 1), n, f => by
      constructor
      · rintro ⟨m, A, c, g, hg, hf⟩
        exact ⟨m, ⟨A, c⟩, g, (computesReLU_iff k m g).mp hg, fun x => by rw [congrFun hf x]⟩
      · rintro ⟨m, T, g, hg, hf⟩
        exact ⟨m, T.A, T.c, g, (computesReLU_iff k m g).mpr hg, funext fun x => by rw [hf x]⟩

/-- Given a `Finset` of functions all satisfying `Agent005.IsAffine`, we can
build an `Agent006`-style `Fin m`-indexed family of `AffineFunc`s that
*covers* every member of the `Finset` (every `g ∈ F` equals `(h i).eval` for
some `i`). Proved by induction on the `Finset` using `Finset.induction_on`,
prepending one new layer with `Fin.cons` at each insertion step. This is the
one genuinely new lemma needed to bridge the `Finset`-of-functions
presentation (005) with the `Fin m`-indexed-family presentation (006) of the
finite affine family underlying `CPWL`. -/
theorem exists_cover {n : ℕ} :
    ∀ F : Finset ((Fin n → ℝ) → ℝ), (∀ g ∈ F, Agent005.IsAffine g) →
      ∃ (m : ℕ) (h : Fin m → Agent006.AffineFunc n), ∀ g ∈ F, ∃ i, (h i).eval = g := by
  classical
  intro F
  induction F using Finset.induction_on with
  | empty => intro _; exact ⟨0, Fin.elim0, by simp⟩
  | @insert a s ha IH =>
      intro hAff
      obtain ⟨w, c, hac⟩ := hAff a (Finset.mem_insert_self a s)
      obtain ⟨m', h', hcov'⟩ := IH (fun g hg => hAff g (Finset.mem_insert_of_mem hg))
      refine ⟨m' + 1, Fin.cons (⟨w, c⟩ : Agent006.AffineFunc n) h', ?_⟩
      intro g hg
      rcases Finset.mem_insert.mp hg with rfl | hg'
      · refine ⟨0, ?_⟩
        simp only [Fin.cons_zero]
        exact hac.symm
      · obtain ⟨i, hi⟩ := hcov' g hg'
        refine ⟨i.succ, ?_⟩
        simp only [Fin.cons_succ]
        exact hi

theorem cpwl (n : ℕ) : Agent005.CPWL n = Agent006.CPWL n := by
  ext f
  constructor
  · rintro ⟨hcont, F, hAff, hloc⟩
    obtain ⟨m, h, hcover⟩ := exists_cover F hAff
    refine ⟨hcont, m, h, fun x => ?_⟩
    obtain ⟨p, hpF, U, hU, hxU, hEq⟩ := hloc x
    obtain ⟨i, hi⟩ := hcover p hpF
    exact ⟨i, eventually_nhds_iff.mpr ⟨U, fun y hy => (hEq hy).trans (congrFun hi.symm y), hU, hxU⟩⟩
  · rintro ⟨hcont, m, g, hloc⟩
    classical
    refine ⟨hcont, Finset.image (fun i => (g i).eval) Finset.univ, ?_, fun x => ?_⟩
    · intro q hq
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hq
      exact ⟨(g i).coeffs, (g i).const, rfl⟩
    · obtain ⟨i, hi⟩ := hloc x
      obtain ⟨U, hUsub, hU, hxU⟩ := eventually_nhds_iff.mp hi
      exact ⟨(g i).eval, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, U, hU, hxU, hUsub⟩

theorem relun (n k : ℕ) : Agent005.ReLUn n k = Agent006.ReLUn n k := by
  ext f
  constructor
  · rintro ⟨k', hk', hc⟩
    exact ⟨k', hk', (computesReLU_iff k' n f).mp hc⟩
  · rintro ⟨k', hk', hc⟩
    exact ⟨k', hk', (computesReLU_iff k' n f).mpr hc⟩

/-- Both files define `depthBound n` as `⌈Real.logb 3 ((n:ℝ) - 1)⌉₊ + 1`
(the `⌈·⌉₊` notation on 005's side literally *is* `Nat.ceil` on 006's side),
so the two definitions are the same term up to notation and `rfl` closes it
without even needing `hn`. -/
theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent005.depthBound n = Agent006.depthBound n := rfl

theorem statement :
    (∀ n, 3 ≤ n → Agent005.CPWL n = Agent005.ReLUn n (Agent005.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent006.CPWL n = Agent006.ReLUn n (Agent006.depthBound n)) := by
  constructor
  · intro h n hn
    rw [← cpwl n, ← relun n (Agent006.depthBound n), ← depth n hn]
    exact h n hn
  · intro h n hn
    rw [cpwl n, relun n (Agent005.depthBound n), depth n hn]
    exact h n hn

end Bridge_005_006

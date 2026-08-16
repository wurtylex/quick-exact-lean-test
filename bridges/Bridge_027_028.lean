namespace Bridge_027_028

/-!
Bridge between `Agent027` and `Agent028`'s formalizations of Theorem 2.

Summary of the comparison:

* `CPWL` — both agents use essentially the *same* "local agreement" encoding:
  `f` is continuous and there is a finite family of scalar affine functions
  such that every point has a neighbourhood on which `f` coincides with one
  member of the family. Agent027 packages the family as a `Finset` of
  functions each satisfying an `IsAffine` predicate; Agent028 packages it as
  a `Fintype`-indexed family of `AffineFunc` structures. These carry the same
  information, so `cpwl` is fully proved below by converting between the two
  packagings (using choice to extract the affine coefficients on one side,
  and `Finset.image` to bundle them back up on the other).

* `depthBound` — Agent027 uses `⌈logb 3 ((n:ℝ) - 1)⌉₊ + 1` (subtract in ℝ);
  Agent028 uses `⌈logb 3 ((↑(n - 1) : ℝ))⌉₊ + 1` (subtract in ℕ, then cast).
  For `n ≥ 3` these agree by `Nat.cast_sub`, so `depth` is fully proved below.

* `ReLUn` — Agent027's `ReLUn n k` requires a network with *exactly* `k`
  hidden layers; Agent028's requires *at most* `k`. As the spec anticipates,
  these coincide only via a "padding" lemma: any network with `k' ≤ k` layers
  can be re-expressed with exactly `k` layers by appending layers that act as
  the identity (using `x = ReLU x - ReLU (-x)`, generalized componentwise and
  threaded through an inductive argument that also lets you precompose an
  arbitrary "exactly `j`-layer" network with an extra affine map). This is a
  genuine, nontrivial induction (on `k - k'`, with accompanying dimension
  bookkeeping for the padding maps) that nobody has supplied a proof of yet;
  building it from scratch is out of scope for a single link in this chain, so
  `relun` is left as `sorry` below with this exact gap identified.

  **Additionally**, `Agent027.AffineMap.apply` (line 40 of `Thm2_027.lean`) is
  defined via `T.A *ᵥ x + T.bias`, and that `*ᵥ` notation currently triggers
  a Mathlib elaboration failure (`Mathlib.Tactic.subscriptTerm` not
  implemented) in this environment. `Agent027.ComputesWithLayers` and hence
  `Agent027.ReLUn` are built directly on top of `AffineMap.apply`, so it is
  likely that `Agent027.ReLUn` fails to elaborate at all independent of the
  padding-lemma gap above — meaning even the *statement* of `relun` may not
  type-check in the harness. This does not affect `cpwl` or `depth`, since
  `Agent027.CPWL` and `Agent027.depthBound` do not go through `AffineMap`.

* `statement` — reduces, via `cpwl` and `depth`, to exactly the same missing
  `ReLUn027 n (depthBound n) = ReLUn028 n (depthBound n)` fact needed for
  `relun` (at the specific depth), so it is left as `sorry` too, for the same
  reason (compounded by the same `*ᵥ` elaboration risk noted above).
-/

theorem cpwl (n : ℕ) : Agent027.CPWL n = Agent028.CPWL n := by
  ext f
  constructor
  · rintro ⟨hf, S, hS, hcov⟩
    refine ⟨hf, ↥S, inferInstance,
        fun p => ⟨(hS p.1 p.2).choose, (hS p.1 p.2).choose_spec.choose⟩, ?_⟩
    intro x
    obtain ⟨g, hgS, hev⟩ := hcov x
    exact ⟨⟨g, hgS⟩, hev.mono fun y hy => hy.trans ((hS g hgS).choose_spec.choose_spec y)⟩
  · rintro ⟨hf, ι, hι, T, hcov⟩
    classical
    refine ⟨hf, Finset.image (fun i => (T i).eval) Finset.univ, ?_, ?_⟩
    · intro g hg
      obtain ⟨i, -, hgi⟩ := Finset.mem_image.mp hg
      refine ⟨(T i).w, (T i).b, fun x => ?_⟩
      simp only [← hgi, Agent028.AffineFunc.eval]
    · intro x
      obtain ⟨i, hev⟩ := hcov x
      exact ⟨(T i).eval, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, hev⟩

theorem depth (n : ℕ) (hn : 3 ≤ n) : Agent027.depthBound n = Agent028.depthBound n := by
  have h1 : (1 : ℕ) ≤ n := by omega
  have h : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub h1, Nat.cast_one]
  simp only [Agent027.depthBound, Agent028.depthBound, h]

-- Genuinely open: `Agent027.ReLUn n k` is "exactly `k` hidden layers" while
-- `Agent028.ReLUn n k` is "at most `k` hidden layers". These agree only via a
-- general padding lemma (any `k' ≤ k`-layer network can be re-expressed with
-- exactly `k` layers, by induction on `k - k'` using the ReLU identity
-- `x = ReLU x - ReLU (-x)` to build identity-acting layers) that is not
-- proved anywhere in either source file, and building it here is out of
-- scope for a single bridge. On top of that, `Agent027.ReLUn` is built on
-- `Agent027.AffineMap.apply`'s `*ᵥ` notation, which does not currently
-- elaborate in this environment (see module docstring), so even this
-- statement may fail to type-check independent of the missing lemma.
theorem relun (n k : ℕ) : Agent027.ReLUn n k = Agent028.ReLUn n k := sorry

-- Depends on the same missing fact as `relun`: after using `cpwl` and
-- `depth` to align the CPWL sets and the depth bound, what remains is
-- exactly `Agent027.ReLUn n (Agent027.depthBound n) =
-- Agent028.ReLUn n (Agent028.depthBound n)`, i.e. the padding lemma
-- discussed above, specialized to `k = depthBound n`. Not proved for the
-- same reason `relun` is not proved (and subject to the same `*ᵥ`
-- elaboration risk).
theorem statement :
    (∀ n, 3 ≤ n → Agent027.CPWL n = Agent027.ReLUn n (Agent027.depthBound n)) ↔
    (∀ n, 3 ≤ n → Agent028.CPWL n = Agent028.ReLUn n (Agent028.depthBound n)) := sorry

end Bridge_027_028

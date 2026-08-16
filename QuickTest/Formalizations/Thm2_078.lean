import Mathlib

namespace Agent078

/-
Design choices (see summary at the end of the task for a short recap):

* Vectors `ℝ^n` are modelled as `Fin n → ℝ`.
* Because a ReLU network's hidden layers can have arbitrary, layer-dependent widths, and
  Lean's dependent `Fin (width i) → ℝ` types make composing a *variable-length* sequence of
  layers with matching types annoying, we represent the values flowing through the network
  (inputs, hidden activations, outputs) uniformly as functions `ℕ → ℝ` ("infinite sequences",
  only finitely many coordinates of which are ever "active" for a given layer). The `width`
  field of a network records, for each layer, how many of these coordinates are meaningful;
  matrices/biases are like`wise indexed by natural numbers. This is purely a bookkeeping
  device to avoid dependent-type casts; mathematically it is the same notion of a ReLU
  network with layer widths `n = n_0, n_1, ..., n_k, n_{k+1} = 1`.
* `ReLUn n k` is defined as *at most* `k` hidden layers (there exists `k' ≤ k` and a network
  with exactly `k'` hidden layers computing `f`). This is the standard convention in the
  depth-separation literature, and it is the reading under which `ReLUn n k` is monotone in
  `k` (a `k`-hidden-layer network can always be padded to `k+1` hidden layers, e.g. using the
  identity `x = ReLU(x) - ReLU(-x)`), matching the "every CPWL function can be represented
  with ... hidden layers" phrasing used for Theorem 1's corollary and Theorem 2 itself.
* `CPWL n` is defined honestly as: `f` is continuous, and there is a *finite* family of
  genuinely affine functions `g_1, ..., g_m : ℝ^n → ℝ` such that every point `x` has a
  neighbourhood on which `f` coincides with one of the `g_i`. This is a standard, non-trivial
  characterization of continuous piecewise-linear functions; it does not mention ReLU
  networks and is not a max-of-affine normal form.
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded using `Real.logb 3` and `Nat.ceil` (`⌈·⌉₊`).
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise (vector) application of ReLU, for any index type `ι`. -/
def reluVec {ι : Type*} (x : ι → ℝ) : ι → ℝ := fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given explicitly by a matrix `A` and a bias `c`,
as `x ↦ A * x + c`. This is the canonical shape of the affine maps `T^{(i)}` in a ReLU
network. -/
def affineMap {a b : ℕ} (A : Fin b → Fin a → ℝ) (c : Fin b → ℝ) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun j => (∑ i, A j i * x i) + c j

/-- A ReLU network with input dimension `n` and `k` hidden layers, i.e. `k + 1` affine
transformations `T^{(1)}, ..., T^{(k+1)}` with layer widths `width 0 = n`, `width (k+1) = 1`.
Layer values (input, hidden activations, output) are represented as functions `ℕ → ℝ`, with
`width i` recording how many leading coordinates are meaningful at layer `i`; the matrix
`A i` and bias `b i` describe the affine map `T^{(i+1)} : ℝ^{width i} → ℝ^{width (i+1)}`. -/
structure ReLUNetwork (n k : ℕ) where
  width : ℕ → ℕ
  width_zero : width 0 = n
  width_last : width (k + 1) = 1
  A : ℕ → ℕ → ℕ → ℝ
  b : ℕ → ℕ → ℝ

/-- Apply the `i`-th affine transformation `T^{(i+1)}` of a `ReLUNetwork`, from the
`width i`-many active coordinates of `x` to the `width (i+1)`-many coordinates of the
output. -/
def ReLUNetwork.layerMap {n k : ℕ} (net : ReLUNetwork n k) (i : ℕ) (x : ℕ → ℝ) : ℕ → ℝ :=
  fun j => (∑ l ∈ Finset.range (net.width i), net.A i j l * x l) + net.b i j

/-- The value at every hidden layer / output of a `ReLUNetwork`, obtained by alternately
applying the affine transformations `T^{(1)}, ..., T^{(k+1)}` and componentwise ReLU, as in
`T^{(k+1)} ∘ ReLU ∘ T^{(k)} ∘ ... ∘ ReLU ∘ T^{(1)}`. ReLU is applied after every affine
transformation except the last one (`T^{(k+1)}`, i.e. layer index `k`). `netForward net m`
is the state of the network after applying the first `m` affine transformations (and the
ReLUs interleaved with them). -/
def ReLUNetwork.netForward {n k : ℕ} (net : ReLUNetwork n k) : ℕ → (ℕ → ℝ) → (ℕ → ℝ)
  | 0, x => x
  | m + 1, x =>
      let pre := net.layerMap m (net.netForward m x)
      if m + 1 = k + 1 then pre else reluVec pre

/-- Embed a vector `Fin n → ℝ` as a sequence `ℕ → ℝ`, zero outside the first `n`
coordinates. -/
def toSeq {n : ℕ} (x : Fin n → ℝ) : ℕ → ℝ :=
  fun i => if h : i < n then x ⟨i, h⟩ else 0

/-- A `ReLUNetwork` *computes* / *represents* a function `f : ℝ^n → ℝ` if feeding it any
input `x` and reading off the single output coordinate (coordinate `0` of the width-1 final
layer) yields `f x`. -/
def ReLUNetwork.Computes {n k : ℕ} (net : ReLUNetwork n k) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x : Fin n → ℝ, f x = net.netForward (k + 1) (toSeq x) 0

/-- `ReLUn n k` is the set of functions `ℝ^n → ℝ` representable by a ReLU network with *at
most* `k` hidden layers. -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ k' ≤ k, ∃ net : ReLUNetwork n k', net.Computes f }

/-- A function `ℝ^n → ℝ` is (genuinely) affine if it has the form `x ↦ a ⬝ x + c`. -/
def IsAffine (n : ℕ) (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (a : Fin n → ℝ) (c : ℝ), ∀ x : Fin n → ℝ, g x = (∑ i, a i * x i) + c

/-- `CPWL n` is the set of continuous, piecewise-linear functions `ℝ^n → ℝ`: those that are
continuous and admit a *finite* family of affine functions such that every point has a
neighbourhood on which `f` agrees with one member of the family. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | Continuous f ∧
        ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ),
          (∀ i, IsAffine n (g i)) ∧
          ∀ x : Fin n → ℝ, ∃ i, ∀ᶠ y in nhds x, f y = g i y }

/-- The depth bound `⌈log_3(n - 1)⌉ + 1` from Theorem 2. -/
noncomputable def depthBound (n : ℕ) : ℕ := ⌈Real.logb 3 ((n : ℝ) - 1)⌉₊ + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := sorry

end Agent078

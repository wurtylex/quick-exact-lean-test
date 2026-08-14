import Mathlib

namespace Agent091

/-!
# Formalization of Theorem 2 of arXiv:2505.14338

"Better Neural Network Expressivity: Subdividing the Simplex"
(Bakaev, Brunck, Hertrich, Stade, Yehudayoff)

Theorem 2. For n ≥ 3, we have CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}.

## Modelling choices

* Vectors `ℝ^n` are modelled as `Fin n → ℝ`.
* Affine maps `ℝ^a → ℝ^b` are modelled concretely as a pair `(weights, bias)` with
  `weights : Fin b → Fin a → ℝ` and `bias : Fin b → ℝ`, evaluated as `A * x + b`.
* A ReLU network with `k` hidden layers computing `f : ℝ^n → ℝ` is modelled by
  structural recursion on `k`: with `0` hidden layers it is a single affine map
  `ℝ^n → ℝ`; with `k+1` hidden layers it is an affine map `ℝ^n → ℝ^m` into some
  (existentially quantified) hidden width `m`, followed by componentwise ReLU,
  followed by a network with `k` hidden layers on the result. This literally
  encodes the alternating composition
  `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` from the paper.
* `ReLUn n k` is taken to be the set of functions representable with **at most**
  `k` hidden layers (not exactly `k`). This is the reading that makes the theorem
  true as an equality of sets: `ReLUn n k` is manifestly monotone increasing in
  `k` under this reading, its union over all `k` is exactly `CPWL n` (every CPWL
  function is representable by *some* network), and Theorem 1 provides the
  matching lower/upper bound machinery to pin down exactly the threshold
  `k = ⌈log_3(n-1)⌉ + 1` at which the increasing chain first reaches all of
  `CPWL n`. (Under the "exactly k" reading the same equality can also be argued
  via the standard identity-padding trick `x = ReLU(x) - ReLU(-x)`, but "at most"
  is the more direct and standard reading for this kind of depth-hierarchy
  statement, so we adopt it.)
* `CPWL n` is defined mathematically (not via ReLU networks!) as: `f` is
  continuous, and there is a *finite* collection of pieces, each cut out by a
  finite system of affine (half-space) inequalities, whose union is all of
  `ℝ^n`, such that on each piece `f` agrees with some affine function.  This is
  a genuine finite polyhedral subdivision condition.
* The depth bound `⌈log_3(n-1)⌉ + 1` is encoded using `Nat.clog 3 (n - 1) + 1`.
  For `b ≥ 2` and `m ≥ 1`, `Nat.clog b m` is (by Mathlib's characterization,
  `Nat.pow_pred_clog_lt_self` / `Nat.le_pow_clog`) the least `k` with `m ≤ b ^ k`,
  which is exactly `⌈Real.logb b m⌉₊` for `m ≥ 1`, `b ≥ 2`; since `n ≥ 3` we have
  `n - 1 ≥ 2 ≥ 1` so this coincides with the intended real ceiling of `log_3(n-1)`.
-/

/-- The ReLU activation function on `ℝ`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Componentwise ReLU on `ℝ^m`. -/
def reluVec {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ :=
  fun i => relu (x i)

/-- An affine transformation `ℝ^a → ℝ^b`, given concretely by a weight matrix
(as a function `Fin b → Fin a → ℝ`) and a bias vector `Fin b → ℝ`. -/
def AffineFun (a b : ℕ) : Type := (Fin b → Fin a → ℝ) × (Fin b → ℝ)

/-- Evaluate an affine transformation: `x ↦ A * x + bias`. -/
def AffineFun.eval {a b : ℕ} (T : AffineFun a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => (∑ j, T.1 i j * x j) + T.2 i

/-- `NetFunc n k f` : the function `f : ℝ^n → ℝ` is *exactly* computed by some ReLU
network with `n` inputs and `k` hidden layers, i.e. `f` is the alternating
composition `T^(k+1) ∘ ReLU ∘ T^(k) ∘ ⋯ ∘ ReLU ∘ T^(1)` of `k + 1` affine
transformations with componentwise ReLU, where all intermediate widths `n_1, …, n_k`
are existentially quantified natural numbers. -/
def NetFunc : (n k : ℕ) → ((Fin n → ℝ) → ℝ) → Prop
  | n, 0, f => ∃ T : AffineFun n 1, ∀ x, f x = T.eval x 0
  | n, (k + 1), f =>
      ∃ (m : ℕ) (T : AffineFun n m) (g : (Fin m → ℝ) → ℝ),
        NetFunc m k g ∧ ∀ x, f x = g (reluVec (T.eval x))

/-- `ReLUn n k` : the set of functions `ℝ^n → ℝ` representable by a ReLU network
with **at most** `k` hidden layers. (See the module docstring for why "at most"
rather than "exactly" is the reading that makes Theorem 2 a true equality.) -/
def ReLUn (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ k' ≤ k, NetFunc n k' f}

/-- A half-space `{x | ⟨c, x⟩ ≤ d}` in `ℝ^n`. -/
structure Halfspace (n : ℕ) where
  c : Fin n → ℝ
  d : ℝ

/-- The set of points satisfying a half-space inequality. -/
def Halfspace.set {n : ℕ} (H : Halfspace n) : Set (Fin n → ℝ) :=
  {x | (∑ i, H.c i * x i) ≤ H.d}

/-- `f : ℝ^n → ℝ` is continuous piecewise linear: it is continuous, and there is a
finite collection of `p` pieces, the `i`-th piece cut out by a finite system of
`m i` half-space inequalities, whose union covers all of `ℝ^n`, on each of which
`f` agrees with some affine function. This is a genuine finite polyhedral
subdivision condition (not a "max of affine functions" normal form, and not
phrased in terms of ReLU networks). -/
def IsCPWL (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  Continuous f ∧
  ∃ (p : ℕ) (m : Fin p → ℕ) (H : ∀ i, Fin (m i) → Halfspace n) (A : Fin p → AffineFun n 1),
    (⋃ i, ⋂ j, (H i j).set) = Set.univ ∧
    ∀ i (x : Fin n → ℝ), (∀ j, x ∈ (H i j).set) → f x = (A i).eval x 0

/-- `CPWL n` : the set of continuous piecewise linear functions `ℝ^n → ℝ`. -/
def CPWL (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | IsCPWL n f}

/-- The depth bound `⌈log_3(n - 1)⌉ + 1`, encoded via `Nat.clog`. -/
def depthBound (n : ℕ) : ℕ := Nat.clog 3 (n - 1) + 1

/-- **Theorem 2.** For `n ≥ 3`, `CPWL_n = ReLU_{n, ⌈log_3(n-1)⌉ + 1}`. -/
theorem theorem2 (n : ℕ) (hn : 3 ≤ n) :
    CPWL n = ReLUn n (depthBound n) := by
  sorry

end Agent091

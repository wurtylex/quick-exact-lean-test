# Bridge verification — machine-checked results

Every one of the 99 consecutive links was type-checked in a single Lean process
against Mathlib v4.27.0. For each link the probe inspects each obligation's
**axiom set**: PROVED = present and free of `sorryAx`; REFUTED = the `_ne` form
proved sorry-free; SORRY = present but depends on `sorryAx`; MISSING = the
declaration failed to elaborate at all.

## Totals across the 99 links

| obligation | PROVED | REFUTED | SORRY | MISSING/other |
|---|---:|---:|---:|---:|
| `cpwl` | 31 | 7 | 19 | 42 |
| `relun` | 11 | 0 | 87 | 1 |
| `depth` | 96 | 0 | 3 | 0 |
| `statement` | 2 | 0 | 97 | 0 |

Bridges with elaboration errors: **68** / 99

**Reading `SORRY`:** the declaration exists but its axiom set contains
`sorryAx`. That covers both an *honest* `sorry` the agent wrote deliberately
and a *failed* proof attempt (Lean records an error and admits the decl with
`sorryAx`). The `errors` column separates them: a link with 0 errors whose
obligations are `SORRY` left them open on purpose; a link with errors had
proofs that did not go through.

## Per-link table

| link | cpwl | relun | depth | statement | errors |
|---|---|---|---|---|---:|
| 001→002 | SORRY_NE | PROVED | PROVED | SORRY | 2 |
| 002→003 | SORRY | SORRY | PROVED | SORRY | 3 |
| 003→004 | PROVED | SORRY | PROVED | SORRY | 6 |
| 004→005 | SORRY | SORRY | PROVED | SORRY |  |
| 005→006 | PROVED | SORRY | PROVED | SORRY | 4 |
| 006→007 | SORRY | SORRY | PROVED | SORRY | 2 |
| 007→008 | SORRY_NE | SORRY | PROVED | SORRY | 10 |
| 008→009 | SORRY_NE | SORRY | PROVED | SORRY | 12 |
| 009→010 | PROVED | SORRY | PROVED | SORRY | 2 |
| 010→011 | PROVED | SORRY | PROVED | SORRY | 1 |
| 011→012 | PROVED | SORRY | PROVED | SORRY | 1 |
| 012→013 | SORRY | SORRY | PROVED | SORRY | 5 |
| 013→014 | SORRY_NE | SORRY | PROVED | SORRY | 9 |
| 014→015 | SORRY_NE | PROVED | PROVED | SORRY | 16 |
| 015→016 | PROVED | SORRY | PROVED | SORRY |  |
| 016→017 | PROVED | PROVED | SORRY | SORRY | 1 |
| 017→018 | PROVED | PROVED | SORRY | SORRY | 1 |
| 018→019 | PROVED | SORRY | PROVED | SORRY |  |
| 019→020 | SORRY | SORRY | PROVED | SORRY |  |
| 020→021 | SORRY | SORRY | PROVED | SORRY |  |
| 021→022 | SORRY_NE | SORRY | PROVED | SORRY | 12 |
| 022→023 | PROVED | SORRY | PROVED | SORRY | 2 |
| 023→024 | SORRY | SORRY | PROVED | SORRY | 12 |
| 024→025 | PROVED | SORRY | PROVED | SORRY |  |
| 025→026 | SORRY_NE | SORRY | PROVED | SORRY | 7 |
| 026→027 | SORRY_NE | SORRY | PROVED | SORRY | 2 |
| 027→028 | PROVED | SORRY | PROVED | SORRY |  |
| 028→029 | SORRY_NE | SORRY | PROVED | SORRY | 3 |
| 029→030 | PROVED | SORRY | PROVED | SORRY |  |
| 030→031 | REFUTED | SORRY | PROVED | SORRY | 3 |
| 031→032 | REFUTED | PROVED | PROVED | SORRY |  |
| 032→033 | SORRY_NE | PROVED | PROVED | SORRY | 1 |
| 033→034 | SORRY_NE | SORRY | PROVED | SORRY | 6 |
| 034→035 | SORRY_NE | SORRY | PROVED | SORRY | 4 |
| 035→036 | SORRY | SORRY | PROVED | SORRY | 3 |
| 036→037 | REFUTED | PROVED | PROVED | SORRY |  |
| 037→038 | SORRY_NE | SORRY | PROVED | SORRY | 8 |
| 038→039 | PROVED | SORRY | PROVED | SORRY | 9 |
| 039→040 | PROVED | SORRY | PROVED | SORRY |  |
| 040→041 | SORRY_NE | SORRY | PROVED | SORRY | 2 |
| 041→042 | SORRY | SORRY | PROVED | SORRY |  |
| 042→043 | SORRY_NE | SORRY | PROVED | SORRY | 8 |
| 043→044 | PROVED | PROVED | PROVED | PROVED |  |
| 044→045 | PROVED | SORRY | PROVED | SORRY | 5 |
| 045→046 | SORRY_NE | SORRY | PROVED | SORRY | 6 |
| 046→047 | SORRY_NE | SORRY | PROVED | SORRY | 8 |
| 047→048 | PROVED | SORRY | PROVED | SORRY |  |
| 048→049 | SORRY_NE | SORRY | PROVED | SORRY | 17 |
| 049→050 | PROVED | SORRY | PROVED | SORRY | 2 |
| 050→051 | SORRY_NE | SORRY | PROVED | SORRY | 6 |
| 051→052 | SORRY_NE | SORRY | PROVED | SORRY | 2 |
| 052→053 | SORRY_NE | SORRY | PROVED | SORRY | 6 |
| 053→054 | SORRY_NE | SORRY | PROVED | SORRY | 8 |
| 054→055 | SORRY | SORRY | PROVED | SORRY | 4 |
| 055→056 | PROVED | SORRY | PROVED | SORRY | 5 |
| 056→057 | SORRY_NE | SORRY | PROVED | SORRY | 2 |
| 057→058 | SORRY_NE | SORRY | PROVED | SORRY | 4 |
| 058→059 | REFUTED | SORRY | PROVED | SORRY |  |
| 059→060 | REFUTED | SORRY | PROVED | SORRY |  |
| 060→061 | PROVED | SORRY | PROVED | SORRY | 1 |
| 061→062 | SORRY_NE | SORRY | PROVED | SORRY | 6 |
| 062→063 | PROVED | SORRY | PROVED | SORRY | 2 |
| 063→064 | SORRY_NE | SORRY | PROVED | SORRY | 6 |
| 064→065 | PROVED | SORRY | PROVED | SORRY |  |
| 065→066 | SORRY | SORRY | PROVED | SORRY | 3 |
| 066→067 | SORRY | SORRY | PROVED | SORRY |  |
| 067→068 | SORRY_NE | SORRY | PROVED | SORRY | 8 |
| 068→069 | SORRY_NE | SORRY | PROVED | SORRY | 3 |
| 069→070 | PROVED | PROVED | PROVED | PROVED |  |
| 070→071 | PROVED | SORRY | PROVED | SORRY |  |
| 071→072 | SORRY_NE | SORRY | PROVED | SORRY | 6 |
| 072→073 | SORRY_NE | SORRY | PROVED | SORRY | 6 |
| 073→074 | SORRY_NE | SORRY | PROVED | SORRY | 4 |
| 074→075 | REFUTED | SORRY | PROVED | SORRY |  |
| 075→076 | PROVED | SORRY | PROVED | SORRY |  |
| 076→077 | PROVED | SORRY | PROVED | SORRY | 5 |
| 077→078 | PROVED | SORRY | PROVED | SORRY |  |
| 078→079 | PROVED | SORRY | PROVED | SORRY |  |
| 079→080 | PROVED | SORRY | PROVED | SORRY |  |
| 080→081 | SORRY_NE | SORRY | PROVED | SORRY | 8 |
| 081→082 | SORRY | PROVED | PROVED | SORRY |  |
| 082→083 | REFUTED | SORRY | PROVED | SORRY |  |
| 083→084 | SORRY | SORRY_NE | PROVED | SORRY | 3 |
| 084→085 | SORRY | SORRY | PROVED | SORRY |  |
| 085→086 | SORRY | SORRY | PROVED | SORRY |  |
| 086→087 | SORRY_NE | SORRY | PROVED | SORRY | 8 |
| 087→088 | SORRY_NE | SORRY | PROVED | SORRY | 2 |
| 088→089 | SORRY_NE | SORRY | PROVED | SORRY | 6 |
| 089→090 | SORRY_NE | SORRY | PROVED | SORRY | 5 |
| 090→091 | SORRY | SORRY | SORRY | SORRY | 1 |
| 091→092 | SORRY_NE | SORRY | PROVED | SORRY | 7 |
| 092→093 | SORRY_NE | SORRY | PROVED | SORRY | 7 |
| 093→094 | SORRY_NE | SORRY | PROVED | SORRY | 6 |
| 094→095 | SORRY | SORRY | PROVED | SORRY |  |
| 095→096 | SORRY_NE | PROVED | PROVED | SORRY | 6 |
| 096→097 | PROVED | SORRY | PROVED | SORRY |  |
| 097→098 | SORRY_NE | SORRY | PROVED | SORRY | 6 |
| 098→099 | SORRY_NE | SORRY | PROVED | SORRY | 9 |
| 099→100 | SORRY | SORRY | PROVED | SORRY | 3 |

Links whose bridge file compiled with **zero errors**: 31 / 99

## Links whose file failed to elaborate

* **001→002** — Application type mismatch: The argument   hx has type   x ∈ ![{x | 0 ≤ x 0}, {x | x 0 ≤ 0}] ⟨0, ⋯⟩ but is expected to have type   ?m.776 ≤ ?m.777 in the applica
* **002→003** — Unknown constant `Matrix.dotProduct`
* **003→004** — Too many variable names provided at alternative `step`: 3 provided, but 2 expected
* **005→006** — unsolved goals n : ℕ f : (Fin n → ℝ) → ℝ w : Fin n → ℝ c : ℝ hf : f = Agent005.affineScalar w c x : Fin n → ℝ ⊢ Agent005.affineScalar w c x = Agent006.affineApp
* **006→007** — Tactic `rewrite` failed: Did not find an occurrence of the pattern   ↑(e.symm (e ⟨a, haS⟩)) in the target expression   f y = ((fun i => toAffineFunc ↑(e.symm i)
* **007→008** — Invalid field `mulVec`: The environment does not contain `Function.mulVec`, so it is not possible to project the field `mulVec` from an expression   fun x x_1 =
* **008→009** — Unknown constant `Matrix.dotProduct`
* **009→010** — unsolved goals case h k : ℕ ih : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ), Agent009.ComputesWithHiddenLayers k n f ↔ Agent010.NetComputes n k f n : ℕ f : (Fin n → ℝ) → ℝ
* **010→011** — unsolved goals case succ.mp.h k : ℕ ih : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ), Agent010.NetComputes n k f ↔ ∃ net, f = net.eval n : ℕ f : (Fin n → ℝ) → ℝ m : ℕ T : A
* **011→012** — unsolved goals case succ.mpr.h k : ℕ ih : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ), (∃ net, f = net.eval) ↔ Agent012.IsReLUNetExact n k f n : ℕ f : (Fin n → ℝ) → ℝ m : ℕ
* **012→013** — unsolved goals case succ.mp.h k : ℕ ih : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ), Agent012.IsReLUNetExact n k f ↔ Agent013.IsReLURep n k f n : ℕ f : (Fin n → ℝ) → ℝ m :
* **013→014** — failed to synthesize instance of type class   OfNat (Fin (pieces14 true).numConstraints) 0 numerals are polymorphic in Lean, but the numeral `0` cannot be used 
* **014→015** — failed to synthesize instance of type class   OfNat (Fin piece1.numConstraints) 0 numerals are polymorphic in Lean, but the numeral `0` cannot be used in a cont
* **016→017** — mod_cast has type   ↑(n - 1) = ↑(n - 1) but is expected to have type   n - 1 = n - 1
* **017→018** — mod_cast has type   ↑(n - 1) = ↑(n - 1) but is expected to have type   n - 1 = n - 1
* **021→022** — Unknown constant `Matrix.dotProduct`
* **022→023** — unsolved goals k : ℕ ih : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ), Agent022.ExactReLUComputable k n f ↔ Agent023.IsReLUNetworkFunc k n f n : ℕ f : (Fin n → ℝ) → ℝ m : ℕ
* **023→024** — Unknown constant `Matrix.dotProduct`
* **025→026** — linarith failed to find a contradiction case h.mp.h hEq : Agent025.CPWL 1 = Agent026.CPWL 1 hCont : Continuous fun x => max 0 (x 0) x : Fin 1 → ℝ hx : x ∈ {x | 
* **026→027** — Type mismatch   max_eq_left hx0 has type   max 0 (x 0) = 0 but is expected to have type   max 0 (x 0) = ![A0, A1] ⟨0, ⋯⟩ 0 * x 0 + ![0, 0] ⟨0, ⋯⟩
* **028→029** — unsolved goals case h₀ m : ℕ z : Fin m w : Fin m → ℝ t : ℝ b : Fin m a✝ : b ∈ Finset.univ hb : b ≠ z ⊢ w b * 0 b = 0
* **030→031** — Unknown constant `Matrix.dotProduct`
* **032→033** — Tactic `unfold` failed to unfold `φ032` in   max 0 (x0 0) = ∑ j, a i j * x0 j + b i
* **033→034** — Application type mismatch: The argument   hx has type   x ∈ if True then {x | x 0 ≤ 0} else {x | 0 ≤ x 0} but is expected to have type   ?m.291 ≤ ?m.290 in the 
* **034→035** — linarith failed to find a contradiction case refine_2.«0».h.mp.h x : Fin 1 → ℝ hx : x ∈ ![{x | x 0 ≤ 0}, {x | 0 ≤ x 0}] ⟨0, ⋯⟩ a✝ : 0 < ∑ x_1, 1 * x x_1 + 0 ⊢ F
* **035→036** — unsolved goals k a b✝ : ℕ T : Agent035.AffineMap' a b✝ rest : Agent035.NetLayers k b✝ 1 x : Fin a → ℝ ⊢ (fun x => (Agent035.NetLayers.cons T rest).eval x 0) x =
* **037→038** — linarith failed to find a contradiction case refine_1.«1».h.mp.«0».h heq : Agent037.CPWL 1 = Agent038.CPWL 1 f : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0) hfdef :
* **038→039** — Unknown constant `Matrix.dotProduct`
* **040→041** — Unknown identifier `le_or_lt`
* **042→043** — linarith failed to find a contradiction case refine_1.«0».h.mp.«0».h hEq : Agent042.CPWL 1 = Agent043.CPWL 1 x : Fin 1 → ℝ h : x ∈ ![{x | 0 ≤ x 0}, {x | x 0 ≤ 0
* **044→045** — Unknown constant `Matrix.dotProduct`
* **045→046** — unsolved goals n : ℕ f : (Fin n → ℝ) → ℝ T : Agent046.AffineMap n 1 hT : f = fun x => T.apply x 0 x : Fin n → ℝ ⊢ (fun x => T.apply x 0) x = (toAT T).eval x 0
* **046→047** — linarith failed to find a contradiction case refine_2.«0».h.mp f : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0) hf : f = fun x => max 0 (x 0) hEq : Agent046.CPWL 1 =
* **048→049** — Invalid field `mulVec`: The environment does not contain `Function.mulVec`, so it is not possible to project the field `mulVec` from an expression   fun x x_1 =
* **049→050** — unsolved goals n : ℕ f : (Fin n → ℝ) → ℝ a : Fin n → ℝ b : ℝ hf : f = fun x => ∑ i, a i * x i + b ⊢ (fun x => ∑ i, a i * x i + b) = (Agent050.ReLUNet.last { A :
* **050→051** — Application type mismatch: The argument   hx has type   x ∈ ![{x | x 0 ≤ 0}, {x | 0 ≤ x 0}] ⟨0, ⋯⟩ but is expected to have type   ?m.1075 ≤ ?m.1074 in the appli
* **051→052** — Tactic `rewrite` failed: Did not find an occurrence of the pattern   H052 0 in the target expression   x ∈ Agent052.Polyhedron (H052 ((fun i => i) ⟨0, ⋯⟩))  cas
* **052→053** — Unknown identifier `le_or_lt`
* **053→054** — Tactic `rewrite` failed: Did not find an occurrence of the pattern   Agent054.AffineMap.eval ?T ?x in the target expression   (fun x => T.eval x 0) x = (toI T).
* **054→055** — Unknown constant `Matrix.dotProduct`
* **055→056** — Unknown constant `Matrix.dotProduct`
* **056→057** — No goals to be solved
* **057→058** — Application type mismatch: The argument   hx has type   x ∈ (fun b => if b = true then {x | 0 ≤ x 0} else {x | x 0 ≤ 0}) false but is expected to have type   ?m
* **060→061** — unsolved goals case succ.mpr k : ℕ ih : ∀ (n : ℕ) (f : Agent060.Vec n → ℝ), Agent060.represents n k f ↔ Agent061.NetComputes k n f n : ℕ f : Agent060.Vec n → ℝ 
* **061→062** — Unknown constant `Matrix.dotProduct`
* **062→063** — No goals to be solved
* **063→064** — Unknown identifier `le_or_lt`
* **065→066** — typeclass instance problem is stuck, it is often due to metavariables   Fin n → Module ?m.117 ℝ
* **067→068** — Tactic `rewrite` failed: Did not find an occurrence of the pattern   if i = 0 then ?m.86 else ?m.87 in the target expression   Agent068.IsAffineFun 1 ((fun i =>
* **068→069** — `simp` made no progress
* **071→072** — linarith failed to find a contradiction case h.mp.h x : Fin 1 → ℝ h : x ∈ ![{x | x 0 ≤ 0}, {x | 0 ≤ x 0}] ⟨1, ⋯⟩ a✝ : 0 < -1 * x 0 ⊢ False failed
* **072→073** — linarith failed to find a contradiction case h.mp.h x : Fin 1 → ℝ h : x ∈ ![{x | 0 ≤ x 0}, {x | x 0 ≤ 0}] ⟨0, ⋯⟩ a✝ : 0 < -1 * x 0 ⊢ False failed
* **073→074** — linarith failed to find a contradiction case h h : Agent073.CPWL 1 = Agent074.CPWL 1 hcont : Continuous kink hmem74 : kink ∈ Agent074.CPWL 1 S : Finset (Agent07
* **076→077** — Unknown constant `Matrix.dotProduct`
* **080→081** — linarith failed to find a contradiction case refine_2.«1».h.mp.«0».h heq : Agent080.CPWL 1 = Agent081.CPWL 1 x : Fin 1 → ℝ hx : x ∈ ![{x | x 0 ≤ 0}, {x | 0 ≤ x 
* **083→084** — Unknown constant `Matrix.dotProduct`
* **086→087** — linarith failed to find a contradiction case refine_1.«0».h.mp.h x : Fin 1 → ℝ h : x ∈ ![{x | 0 ≤ x 0}, {x | x 0 ≤ 0}] ⟨0, ⋯⟩ a✝ : 0 < -1 * x 0 ⊢ False failed
* **087→088** — Tactic `rewrite` failed: Did not find an occurrence of the pattern   max 0 (x 0) in the target expression   (fun x => max 0 (x 0)) x = ∑ i, (fun x => 0) i * x i
* **088→089** — linarith failed to find a contradiction case h.mp.h hEq : Agent088.CPWL 1 = Agent089.CPWL 1 f : (Fin 1 → ℝ) → ℝ := fun x => max 0 (x 0) hf : f = fun x => max 0 
* **089→090** — Unknown identifier `le_or_lt`
* **090→091** — omega could not prove the goal: a possible counterexample may satisfy the constraints   e ≥ 0   d ≥ 0   d - e ≥ 1   a ≥ 2   a - b ≤ 0   a - c ≥ 1 where  a := ↑(
* **091→092** — linarith failed to find a contradiction case refine_1.a.inr.h x : Fin 1 → ℝ hx : x 0 ≤ 0 x✝ : Fin ((fun x => 1) 1) a✝ : (![fun x => { c := fun x => 1, d := 0 }]
* **092→093** — linarith failed to find a contradiction case refine_2.«0».h.mp.h h : Agent092.CPWL 1 = Agent093.CPWL 1 x : Fin 1 → ℝ hh : x ∈ ![{x | 0 ≤ x 0}, {x | x 0 ≤ 0}] ⟨0
* **093→094** — Invalid field `eval`: The environment does not contain `Prod.eval`, so it is not possible to project the field `eval` from an expression   (fun x x_1 => w, fun 
* **095→096** — Unknown constant `Matrix.dotProduct`
* **097→098** — linarith failed to find a contradiction case h.mp.h x : Fin 1 → ℝ h : x ∈ ![{x | x 0 ≤ 0}, {x | 0 ≤ x 0}] ⟨1, ⋯⟩ a✝ : 0 < -x 0 ⊢ False failed
* **098→099** — linarith failed to find a contradiction case mp.h x : Fin 1 → ℝ h : x ∈ {x | 0 ≤ x 0} i : Fin 1 a✝ : 0 < -1 * x 0 ⊢ False failed
* **099→100** — Unknown constant `Matrix.dotProduct`

## Agent files: 28 of 100 still report errors (unchanged from the original type check)


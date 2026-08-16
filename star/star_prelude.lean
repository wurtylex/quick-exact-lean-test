import Mathlib

/-!
# Star-comparison harness

Every sampled formalization is compared against `Reference.lean` rather than
against its neighbour.  Two agents that both match the reference are equal to
each other for free, so `k` comparisons give a partition instead of a chain.

Each comparison's verdict is read off the declaration's **axiom set**, so a
`sorry` — even one laundered through another sorry-ed theorem — can never be
reported as a proof.  The `_ne` forms carry refutations.
-/

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

section StarHarness
open Lean Elab Meta Command

/-- Does this expression mention `sorryAx`? -/
def hasSorryAx (e : Expr) : Bool :=
  (e.find? (fun x => x.isConstOf ``sorryAx)).isSome

/-- For one comparison namespace, report for each obligation whether it was
    proved (present and sorry-free), refuted (its `_ne` form proved), sorried,
    broken, or absent.

    `ERROR` matters: when a tactic block dies on a runtime exception Lean's
    recovery rewrites the declaration as `theorem foo : sorry := sorry`, whose
    axiom set is *empty*.  Checking the type is what stops such a stub being
    reported as a proof. -/
def starProbe (ns : Name) : Elab.Term.TermElabM Unit := do
  let env ← getEnv
  let status (base : String) : MetaM String := do
    let pos := ns ++ base.toName
    let neg := ns ++ (base ++ "_ne").toName
    let judge (n : Name) : MetaM (Option String) := do
      match env.find? n with
      | none => return none
      | some ci =>
          if hasSorryAx ci.type then return some "ERROR"
          let ax ← collectAxioms n
          return some (if ax.contains ``sorryAx then "SORRY" else "OK")
    match (← judge pos), (← judge neg) with
    | some "OK", _      => return "PROVED"
    | _, some "OK"      => return "REFUTED"
    | some "SORRY", _   => return "SORRY"
    | _, some "SORRY"   => return "SORRY_NE"
    | some "ERROR", _   => return "ERROR"
    | _, some "ERROR"   => return "ERROR"
    | none, none        => return "MISSING"
    | _, _              => return "?"
  let c ← status "cpwl"
  let r ← status "relun"
  let d ← status "depth"
  let s ← status "statement"
  -- Optional bonus obligation: a direct proof that the file's *own* Theorem 2
  -- is false, which needs no reference to the unproved `Ref.theorem2`.
  let f ← status "agent_side_false"
  logInfo m!"@@STAR {ns} cpwl={c} relun={r} depth={d} statement={s} ownfalse={f}"

end StarHarness

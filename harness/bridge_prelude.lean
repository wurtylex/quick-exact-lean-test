import Mathlib

set_option maxErrors 100000

section BridgeHarness
open Lean Elab Meta Command

/-- For one bridge namespace, report for each obligation whether it was proved
    (present and sorry-free), sorried, refuted (the `_ne` form), or missing. -/
def bridgeProbe (ns : Name) : Elab.Term.TermElabM Unit := do
  let env ← getEnv
  let status (base : String) : MetaM String := do
    let pos := ns ++ base.toName
    let neg := ns ++ (base ++ "_ne").toName
    let judge (n : Name) : MetaM (Option String) := do
      match env.find? n with
      | none => return none
      | some _ =>
          let ax ← collectAxioms n
          return some (if ax.contains ``sorryAx then "SORRY" else "OK")
    match (← judge pos), (← judge neg) with
    | some "OK", _        => return "PROVED"
    | _, some "OK"        => return "REFUTED"
    | some "SORRY", _     => return "SORRY"
    | _, some "SORRY"     => return "SORRY_NE"
    | none, none          => return "MISSING"
    | _, _                => return "?"
  let c ← status "cpwl"
  let r ← status "relun"
  let d ← status "depth"
  let s ← status "statement"
  logInfo m!"@@BRIDGE {ns} cpwl={c} relun={r} depth={d} statement={s}"

end BridgeHarness

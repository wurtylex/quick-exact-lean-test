#!/usr/bin/env python3
"""Which formalizations match the reference *definitionally* — equal by `rfl`,
no proof needed?

    python3 defeq.py > Defeq.lean
    cd .. && lake env lean -DmaxErrors=1000000 star/Defeq.lean | grep '@@DF'
"""
import json, os, re

H = os.path.dirname(os.path.abspath(__file__))
IDS = json.load(open(os.path.join(H, "starmap.json")))["ids"]

PRELUDE = """import Mathlib
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

open Lean Elab Meta in
def dfCheck (ids : List String) : TermElabM Unit := do
  for i in ids do
    let mut row := ""
    for d in ["CPWL", "ReLUn", "depthBound"] do
      let a := ("Agent" ++ i ++ "." ++ d).toName
      let r := ("Ref." ++ d).toName
      let ok ←
        if ((← getEnv).find? a).isSome && ((← getEnv).find? r).isSome then
          try
            withOptions (fun o => o.setNat `maxHeartbeats 20000) <|
              Core.withCurrHeartbeats <| withNewMCtxDepth <|
                isDefEq (.const a []) (.const r [])
          catch _ => pure false
        else pure false
      row := row ++ " " ++ d ++ "=" ++ toString ok
    logInfo m!"@@DF {i}{row}"
"""


def strip(p):
    return "\n".join(l for l in open(p).read().splitlines()
                     if not l.strip().startswith("import "))


out = [PRELUDE, strip(os.path.join(H, "Reference.lean"))]
for i in IDS:
    out.append(strip(os.path.join(H, "..", "formalizations", f"Thm2_{i}.lean")))
out.append("set_option maxHeartbeats 0 in")
out.append("run_cmd Lean.Elab.Command.liftTermElabM (dfCheck [%s])"
           % ", ".join(f'"{i}"' for i in IDS))
print("\n\n".join(out))

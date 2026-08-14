import Mathlib

section AgentCheckHarness
open Lean Elab Meta Command

/-- Erase binder names so alpha-equivalent statements hash identically. -/
partial def acNorm (e : Expr) : Expr :=
  match e with
  | .forallE _ t b bi => .forallE `x (acNorm t) (acNorm b) bi
  | .lam _ t b bi     => .lam `x (acNorm t) (acNorm b) bi
  | .letE _ t v b nd  => .letE `x (acNorm t) (acNorm v) (acNorm b) nd
  | .app f a          => .app (acNorm f) (acNorm a)
  | .mdata _ b        => acNorm b
  | .proj s i b       => .proj s i (acNorm b)
  | e                 => e

/-- Delta-expand every constant living in namespace `ns`, with fuel. -/
partial def acUnfold (ns : Name) (fuel : Nat) (e : Expr) : MetaM Expr := do
  if fuel = 0 then return e
  let step (x : Expr) : MetaM TransformStep := do
    match x.getAppFn with
    | .const n _ =>
        if ns.isPrefixOf n then
          match (← unfoldDefinition? x) with
          | some x' => return .done x'.headBeta
          | none    => return .continue
        else return .continue
    | _ => return .continue
  let e' ← Meta.transform e (pre := step)
  if e' == e then return e else acUnfold ns (fuel - 1) e'

/-- Probe one agent's `theorem2`: emit structural hashes and a fully-unfolded
    one-line rendering of the statement. -/
def acProbe (ns : Name) : Elab.Term.TermElabM Unit := do
  match (← getEnv).find? (ns ++ `theorem2) with
  | none => logInfo m!"@@ERR {ns} no-theorem2"
  | some ci => do
      try
        let raw := ci.type
        let unf ← acUnfold ns 60 raw
        let unf ← Meta.zetaReduce unf
        let opts : Options → Options := fun o =>
          ((((o.setBool `pp.unicode.fun true).setBool `pp.deepTerms true).setBool
            `pp.proofs true).setNat `format.width 100000)
        let ppShallow ← withOptions opts do Meta.ppExpr raw
        let ppDeep ← withOptions opts do Meta.ppExpr unf
        logInfo m!"@@SHALLOW {ns} {(acNorm raw).hash}"
        logInfo m!"@@DEEP {ns} {(acNorm unf).hash}"
        logInfo m!"@@PPSHALLOW {ns} {ppShallow.pretty 1000000}"
        logInfo m!"@@PPDEEP {ns} {ppDeep.pretty 1000000}"
        let ppCanon ← withOptions opts do Meta.ppExpr (acNorm unf)
        logInfo m!"@@PPCANON {ns} {ppCanon.pretty 1000000}"
      catch ex =>
        logInfo m!"@@ERR {ns} probe-failed: {← ex.toMessageData.toString}"

end AgentCheckHarness

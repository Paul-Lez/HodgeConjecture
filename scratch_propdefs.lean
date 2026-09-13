import HodgeConjecture
import Other

open Lean Meta Elab

/-- Report every `def`-like (non-theorem) constant declared in this project whose
type is a `Prop`. -/
def report : MetaM Unit := do
  let env ← getEnv
  let mut out : Array String := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    match ci with
    | .defnInfo _ =>
      let some mod := env.getModuleFor? n | continue
      let ms := mod.toString
      unless ms.startsWith "HodgeConjecture" || ms.startsWith "Other" do continue
      let isProp ← Meta.isProp ci.type
      if isProp then
        let inst := if (← Meta.isInstance n) then "INSTANCE" else "DEF"
        let pos ←
          match ← findDeclarationRanges? n with
          | some r => pure s!"{r.range.pos.line}"
          | none => pure "?"
        out := out.push s!"{inst}\t{mod}\t{pos}\t{n}"
    | _ => pure ()
  for l in out.qsort (· < ·) do
    IO.println l
  IO.println s!"TOTAL {out.size}"

run_meta report

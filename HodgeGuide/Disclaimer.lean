/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VersoManual

/-!
# The work-in-progress banner

The site is rebuilt and redeployed from `main` on every push, so a reader can arrive at any moment
in the middle of a refactor. The `wip` directive wraps its contents in a red box, which the front
page uses to say so before anything else.
-/

open Lean Verso Doc Elab Genre Manual

namespace HodgeGuide

/-- The style for the work-in-progress banner: a red box with a heavier rule down its left edge. -/
def wipCss : String := "
.fc-wip {
  border: 1px solid #b3261e;
  border-left: 5px solid #b3261e;
  border-radius: 4px;
  background-color: #fdeceb;
  color: #7f1d1a;
  padding: 0.8em 1.1em;
  margin: 1.5em 0;
}
.fc-wip > *:first-child { margin-top: 0; }
.fc-wip > *:last-child { margin-bottom: 0; }
.fc-wip strong { color: #b3261e; }
.fc-wip a, .fc-wip a:visited { color: #8c1d18; }
"

block_extension Block.wip where
  extraCssFiles := Std.HashSet.ofList [{ filename := "fc-wip.css", contents := wipCss }]
  traverse _ _ _ := pure none
  toTeX := some fun _ go _ _ content => do
    pure <| .seq (← content.mapM go)
  toHtml :=
    open Verso.Output.Html in
    some fun _ blockHtml _ _ content => do
      pure {{
        <div class="fc-wip" role="note">
          {{← content.mapM blockHtml}}
        </div>
      }}

end HodgeGuide

/-- `:::wip` `:::` renders its contents in a red work-in-progress box. -/
@[directive_expander wip]
def wip : DirectiveExpander
  | #[], contents => do
    let blocks ← contents.mapM elabBlock
    pure #[← `(Verso.Doc.Block.other {HodgeGuide.Block.wip with data := Lean.Json.null}
      #[$[$blocks],*])]
  | _, _ => throwError "wip takes no arguments"

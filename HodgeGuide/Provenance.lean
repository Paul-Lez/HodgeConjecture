/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VersoManual
import HodgeConjecture
import Other

/-!
# Marking the declarations that belong to this repository

The guide quotes Lean code freely, and a reader cannot tell from a name alone whether it is
defined in Mathlib or in this repository. When this module is compiled, `repoDeclsJson%`
enumerates every declaration whose defining module belongs to the repository. The
`fcProvenance` directive ships that list to every page of the site together with a small script
that underlines those names wherever they appear: in code blocks, in the terms inside sentences,
and in the hover tooltips.
-/

open Lean Verso Doc Elab Genre Manual

namespace HodgeGuide

/-- Module-name prefixes that count as "this repository". -/
def repositoryPrefixes : List Name := [`HodgeConjecture, `Other, `Challenge]

/-- Whether `m` is a module of this repository. -/
def isRepositoryModule (m : Name) : Bool :=
  repositoryPrefixes.any (·.isPrefixOf m)

open Lean Elab Term in
/-- A JSON object mapping every repository declaration to its module, computed at compile time
from the environment of this module. -/
elab "repoDeclsJson%" : term => do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let entries : Array (String × Json) := env.constants.fold (init := #[]) fun acc n _ =>
    if n.isInternal then acc else
    match env.getModuleIdxFor? n with
    | Option.some idx =>
      let m := moduleNames[idx]!
      if isRepositoryModule m then acc.push (n.toString, Json.str m.toString) else acc
    | Option.none => acc
  return mkStrLit (Json.mkObj entries.toList).compress

/-- The declarations of this repository, as JSON text. -/
def repoDeclsJson : String := repoDeclsJson%

/-- The script that marks repository declarations, run on every page. -/
def markerJs : String := "
(function () {
  function mark(root) {
    var decls = window.fcDecls;
    if (!decls) { return; }
    var nodes = root.querySelectorAll('[data-binding^=\"const-\"]');
    for (var i = 0; i < nodes.length; i++) {
      var el = nodes[i];
      if (el.classList.contains('fc-decl') || el.classList.contains('fc-lib')) { continue; }
      var name = el.getAttribute('data-binding').slice(6);
      if (Object.prototype.hasOwnProperty.call(decls, name)) {
        el.classList.add('fc-decl');
        el.setAttribute('data-fc-module', decls[name]);
      } else {
        el.classList.add('fc-lib');
      }
    }
  }
  function start() {
    mark(document);
    new MutationObserver(function (muts) {
      for (var i = 0; i < muts.length; i++) {
        var added = muts[i].addedNodes;
        for (var j = 0; j < added.length; j++) {
          if (added[j].nodeType === 1) { mark(added[j]); }
        }
      }
    }).observe(document.body, { childList: true, subtree: true });
  }
  if (document.readyState === 'loading') { document.addEventListener('DOMContentLoaded', start); }
  else { start(); }
})();
"

/-- The style for repository declarations: a dotted underline. -/
def markerCss : String := "
.fc-decl {
  text-decoration-line: underline;
  text-decoration-style: dotted;
  text-decoration-color: #c9a227;
  text-decoration-thickness: 1.5px;
  text-underline-offset: 0.2em;
}
"

block_extension Block.fcProvenance where
  extraJsFiles := Std.HashSet.ofList [
    { filename := "fc-decls.js", contents := s!"window.fcDecls = {repoDeclsJson};\n", sourceMap? := none },
    { filename := "fc-mark.js", contents := markerJs, defer := true, after := #["fc-decls.js"],
      sourceMap? := none }]
  extraCssFiles := Std.HashSet.ofList [{ filename := "fc-mark.css", contents := markerCss }]
  traverse _ _ _ := pure none
  toTeX := some fun _ _ _ _ _ => pure .empty
  toHtml := some fun _ _ _ _ _ => pure .empty

end HodgeGuide

/-- `:::fcProvenance` `:::` installs the repository-declaration list and the marker script and
style on every page. It renders nothing. -/
@[directive_expander fcProvenance]
def fcProvenance : DirectiveExpander
  | #[], #[] => do
    pure #[← `(Verso.Doc.Block.other {HodgeGuide.Block.fcProvenance with data := Lean.Json.null} #[])]
  | _, _ => throwError "fcProvenance takes no arguments and no contents"

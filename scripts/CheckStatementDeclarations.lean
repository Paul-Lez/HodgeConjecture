/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import HodgeConjecture.Statement
import Lean.AutoDecl
import Lean.Meta.CompletionName
import Lean.Util.FoldConsts

/-!
# Audit declarations imported by the Hodge conjecture statement

This is a manual diagnostic for the boundary around `HodgeConjecture.Statement`. It reports public,
user-facing declarations from imported `HodgeConjecture` modules that are not in the dependency
closure of the declaration `HodgeConjecture`.

A declaration is in the dependency closure when it is the root, or occurs as a constant in the type
or value of another declaration in the closure. Values of opaque definitions and theorem proofs are
included. The traversal expands only project-local declarations: an already-compiled external module
cannot depend on a later `HodgeConjecture` module, so expanding external constants cannot add a local
declaration to the closure. Candidate filtering is separate from traversal: every referenced local
constant is expanded even when it is private, generated, or excluded from the final report, so such a
helper can connect the root to a public declaration.

The candidates deliberately exclude:

* private declarations, including declarations not exported by Lean's module system;
* reserved, macro-generated, and otherwise internal/automatic names;
* constructors, recursors, matchers, no-confusion declarations, and auxiliary recursors, which are
  generated along with a user declaration; and
* structure projections, which are generated from fields and need not occur when the structure
  itself is used.

The owning inductive or structure remains a candidate, so these exclusions remove redundant or
misleading reports rather than hiding a user-defined type. User-named definitions, theorems,
instances, inductive types, and structures remain candidates.

Readable generated names for source constructs such as anonymous instances and notation elaborators
also remain candidates. Imported environment metadata does not reliably distinguish them from an
explicitly named public declaration, and they can affect downstream elaboration. In particular, this
audit does not guess from prefixes such as `inst` or `term`.

This is kernel-term reachability, not an elaboration trace. A compiled declaration does not record
the notation or tactic that produced it, simp lemmas whose names do not survive in the result, or the
effects of environment extensions. Such declarations can therefore fall outside the kernel dependency closure even when they help
elaborate source elsewhere in the closure. Their appearance is useful evidence for manual
triage, but not by itself proof that the declaration or its module can be removed.

By default this file only reports findings. Set `HODGE_DECLARATION_AUDIT_STRICT=1` to make any findings an error. It is kept out of the default Lake targets because the report is informational
while the current findings are being triaged.
-/

open Lean Meta

namespace StatementDeclarationAudit

private def rootDeclaration : Name := `HodgeConjecture
private def localModuleRoot : Name := `HodgeConjecture

private def isLocalModule (moduleName : Name) : Bool :=
  localModuleRoot.isPrefixOf moduleName

private def moduleFor? (env : Environment) (declName : Name) : Option Name := do
  let moduleIdx ← env.getModuleIdxFor? declName
  env.allImportedModuleNames[moduleIdx.toNat]?

private def isLocalDeclaration (env : Environment) (declName : Name) : Bool :=
  (moduleFor? env declName).any isLocalModule

private inductive Exclusion where
  | privateDecl
  | internalOrAutomatic
  | constructor
  | recursorOrAuxiliary
  | projection

private def exclusion? (env : Environment) (name : Name) (info : ConstantInfo) :
    Elab.Command.CommandElabM (Option Exclusion) := do
  if isPrivateName name then
    return some .privateDecl
  if info matches .ctorInfo _ then
    return some .constructor
  if info matches .recInfo _ then
    return some .recursorOrAuxiliary
  if env.isProjectionFn name then
    return some .projection
  if isAuxRecursor env name || isNoConfusion env name || (← isRec name) || (← isMatcher name) then
    return some .recursorOrAuxiliary
  if name.isInternal || name.isInternalDetail ||
      (← Elab.Command.liftCoreM (isAutoDeclOrPrivate_Internal name)) then
    return some .internalOrAutomatic
  return none

private structure Entry where
  moduleName : Name
  declaration : Name

private structure ExclusionCounts where
  privateDecl : Nat := 0
  internalOrAutomatic : Nat := 0
  constructor : Nat := 0
  recursorOrAuxiliary : Nat := 0
  projection : Nat := 0

private def ExclusionCounts.add (counts : ExclusionCounts) : Exclusion → ExclusionCounts
  | .privateDecl => { counts with privateDecl := counts.privateDecl + 1 }
  | .internalOrAutomatic =>
      { counts with internalOrAutomatic := counts.internalOrAutomatic + 1 }
  | .constructor => { counts with constructor := counts.constructor + 1 }
  | .recursorOrAuxiliary =>
      { counts with recursorOrAuxiliary := counts.recursorOrAuxiliary + 1 }
  | .projection => { counts with projection := counts.projection + 1 }

private structure Audit where
  localModuleCount : Nat
  candidates : Array Entry
  reachableLocalDeclarations : NameSet
  unreachable : Array Entry
  exclusions : ExclusionCounts

private def dependencyClosure (env : Environment) : NameSet := Id.run do
  let mut visited : NameSet := {}
  let mut pending := #[rootDeclaration]
  while let some name := pending.back? do
    pending := pending.pop
    if visited.contains name then
      continue
    visited := visited.insert name
    if let some info := env.find? name then
      for dependency in info.getUsedConstantsAsSet do
        if isLocalDeclaration env dependency && !visited.contains dependency then
          pending := pending.push dependency
  return visited

private def entryLt (a b : Entry) : Bool :=
  if a.moduleName == b.moduleName then
    a.declaration.toString < b.declaration.toString
  else
    a.moduleName.toString < b.moduleName.toString

private def audit : Elab.Command.CommandElabM Audit := do
  let env ← getEnv
  unless env.contains rootDeclaration do
    throwError "declaration `{rootDeclaration}` was not found"
  let reachableLocalDeclarations := dependencyClosure env
  let mut localModuleCount := 0
  let mut candidates := #[]
  let mut exclusions := {}
  for h : moduleIdx in *...env.header.moduleNames.size do
    let moduleName := env.header.moduleNames[moduleIdx]
    if !isLocalModule moduleName then
      continue
    localModuleCount := localModuleCount + 1
    let moduleData := env.header.moduleData[moduleIdx]!
    for info in moduleData.constants do
      let name := info.name
      if let some reason ← exclusion? env name info then
        exclusions := exclusions.add reason
      else
        candidates := candidates.push { moduleName, declaration := name }
  candidates := candidates.qsort entryLt
  let unreachable := candidates.filter (fun entry => !reachableLocalDeclarations.contains entry.declaration)
  return { localModuleCount, candidates, reachableLocalDeclarations, unreachable, exclusions }

private def render (result : Audit) : String := Id.run do
  let reachableCandidates := result.candidates.size - result.unreachable.size
  let mut lines := #[
    "Statement declaration audit",
    s!"  root declaration: {rootDeclaration}",
    s!"  local imported modules: {result.localModuleCount}",
    s!"  public user declarations considered: {result.candidates.size}",
    s!"  reachable public user declarations: {reachableCandidates}",
    s!"  public user declarations outside the kernel dependency closure: {result.unreachable.size}",
    "  excluded generated/non-public declarations:",
    s!"    private or non-exported: {result.exclusions.privateDecl}",
    s!"    internal or automatic: {result.exclusions.internalOrAutomatic}",
    s!"    constructors: {result.exclusions.constructor}",
    s!"    recursors/matchers/auxiliaries: {result.exclusions.recursorOrAuxiliary}",
    s!"    structure projections: {result.exclusions.projection}"
  ]
  if result.unreachable.isEmpty then
    lines := lines.push "\nAll considered declarations are reachable."
    return "\n".intercalate lines.toList
  lines := lines.push "\nDeclarations outside the kernel dependency closure by source module:"
  let mut currentModule : Option Name := none
  for entry in result.unreachable do
    if currentModule != some entry.moduleName then
      currentModule := some entry.moduleName
      lines := lines.push s!"\n{entry.moduleName}:"
    lines := lines.push s!"  {entry.declaration}"
  return "\n".intercalate lines.toList

def run : Elab.Command.CommandElabM Unit := do
  let result ← audit
  let report := render result
  IO.println report
  let strict := (← IO.getEnv "HODGE_DECLARATION_AUDIT_STRICT") == some "1"
  if strict && !result.unreachable.isEmpty then
    throwError "statement declaration audit found {result.unreachable.size} declaration(s) outside the kernel dependency closure"

end StatementDeclarationAudit

run_cmd StatementDeclarationAudit.run

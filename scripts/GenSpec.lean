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
import Lean

/-!
# Generator for `Challenge/Constructed.lean`, the self-contained statement of `HodgeConjecture`

Run `scripts/genspec.sh` from the repository root after `lake build HodgeConjecture`. It runs

    lake env lean scripts/GenSpec.lean

to a fixpoint with the compiler (`scripts/genspec_fallback.py` records the `sorry` ascriptions the
compiler rejects) and with `scripts/SpecAudit.lean` (which records the declarations unreachable
from the statement in the compiled file); both records live in `scripts/genspec-state/`.

For the root proposition this script computes the transitive closure of *definitions* the
proposition unfolds through (constants occurring in types, and in the bodies of everything that is not a
theorem or a proof), re-elaborates the source modules that contain them, and writes one file that
imports only Mathlib and contains, in dependency order:

* every declaration in that closure, with its docstring, verbatim from the source, except that
  every maximal proof subterm in a definition body is replaced by `sorry`;
* every Prop-valued instance the closure needs for elaboration, with its proof replaced by `sorry`;
* the notations, `open`/`namespace`/`section`/`variable`/`set_option` context, and module
  docstrings of those modules.

No theorem or lemma survives. Each `sorry` is a proof obligation discharged in the repository.
-/

open Lean Elab Meta

namespace GenSpec

def isLocalModule (m : Name) : Bool :=
  (`HodgeConjecture).isPrefixOf m || (`Other).isPrefixOf m

/-- Map a generated constant to the source-level declaration that produced it. -/
partial def parentName (env : Environment) (n : Name) : Name :=
  match n with
  | .str p s =>
    let generated := s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "_eq_" ||
      s.startsWith "eq_" || s == "mk" || s == "rec" || s == "casesOn" || s == "recOn" ||
      s == "noConfusion" || s == "noConfusionType" || s == "below" || s == "brecOn" ||
      s == "binductionOn" || s == "ibelow" || s == "sizeOf_spec" || s == "inj" ||
      s == "injEq" || s.startsWith "_"
    if generated && env.contains p then parentName env p
    else match getStructureInfo? env p with
      | some si => if si.fieldNames.contains (Name.mkSimple s) then p else n
      | none => n
  | _ => n

structure Kept where
  name : Name
  module : Name
  startLine : Nat
  endLine : Nat
  deriving Inhabited

/-- `foo._proof_n`: a proof the elaborator abstracted out of the body of `foo`. -/
def isAuxProof (n : Name) : Bool :=
  match n with
  | .str _ s => s.startsWith "_proof_"
  | _ => false

/-- Repository constants with a propositional type that typeclass synthesis supplied in
instance-implicit argument positions of `v`, looking through abstracted auxiliary proofs. These
are the (possibly `local`) instances the definition needs for elaboration; no attribute in the
imported environment records local ones, and abstraction hides both kinds from a plain constant
scan. -/
def synthesizedPropInstances (isLocal : Name → Bool) (v : Expr) : MetaM (Array Name) := do
  let acc ← IO.mkRef (#[] : Array Name)
  let env ← getEnv
  let _ ← Meta.transform v (pre := fun e => do
    if e.isApp then
      let fn := e.getAppFn
      let args := e.getAppArgs
      let info? ← (try some <$> getFunInfoNArgs fn args.size catch _ => pure none)
      if let some info := info? then
        for i in [0:args.size] do
          if h : i < info.paramInfo.size then
            if info.paramInfo[i].isInstImplicit then
              let mut cs := args[i]!.getUsedConstants
              let mut seen : Std.HashSet Name := {}
              let mut j := 0
              while j < cs.size do
                let c := cs[j]!
                j := j + 1
                if seen.contains c then continue
                seen := seen.insert c
                if isAuxProof c then
                  if let some (.thmInfo t) := env.find? c then cs := cs ++ t.value.getUsedConstants
                else if isLocal c then
                  if let some ci := env.find? c then
                    let propValued ← (try forallTelescope ci.type fun _ b => isProp b catch _ => pure false)
                    if propValued then acc.modify (·.push c)
    return .continue)
  acc.get

/-- Source-level declarations the root unfolds through, plus the Prop-valued instances they need. -/
def closure (root : Name) (force : Array Name) :
    MetaM (Array Kept × Std.HashSet Name × Nat × Nat) := do
  let env ← getEnv
  let modOf (n : Name) : Name :=
    match env.getModuleIdxFor? n with
    | some i => env.header.moduleNames[i.toNat]!
    | none => Name.anonymous
  let isLocal (n : Name) : Bool := isLocalModule (modOf n)
  let mut visited : Std.HashSet Name := {}
  let mut stack : Array Name := #[root] ++ force
  let mut kept : Std.HashSet Name := {}
  let mut keptRaw : Std.HashSet Name := {}
  let mut synthInst : Std.HashSet Name := {}
  let mut ctors : Std.HashSet Name := {}
  let mut nDefs := 0
  let mut nPropInst := 0
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if visited.contains n then continue
    visited := visited.insert n
    let some ci := env.find? n | continue
    if !isLocal n then continue
    let tyIsProp ← (try isProp ci.type catch _ => pure false)
    let proofLike := ci.isTheorem || tyIsProp
    let mut deps := ci.type.getUsedConstants
    if !proofLike then
      if let some v := ci.value? then
        deps := deps ++ v.getUsedConstants
        let insts ← synthesizedPropInstances isLocal v
        for c in insts do synthInst := synthInst.insert c
        deps := deps ++ insts
      if let .inductInfo ii := ci then
        deps := deps ++ ii.ctors.toArray
        for c in ii.ctors do ctors := ctors.insert c
      nDefs := nDefs + 1
      kept := kept.insert (parentName env n)
      keptRaw := keptRaw.insert n
    else if (← isInstance n) || synthInst.contains n then
      nPropInst := nPropInst + 1
      kept := kept.insert (parentName env n)
      keptRaw := keptRaw.insert n
    else if ctors.contains n || env.isProjectionFn n then
      -- a propositional constructor or projection of a kept structure: its type spells out the
      -- fields, which the structure declaration needs, so follow it without keeping it
      pure ()
    else
      -- a proof that will be elided: its statement may mention definitions the conjecture does
      -- not need, so it contributes nothing to the closure
      continue
    for d in deps do
      if !visited.contains d then stack := stack.push d
  let mut out : Array Kept := #[]
  for p in kept do
    match ← findDeclarationRanges? p with
    | some r => out := out.push ⟨p, modOf p, r.range.pos.line, r.range.endPos.line⟩
    | none => IO.eprintln s!"warning: no declaration range for {p} (module {modOf p}); skipped"
  return (out, keptRaw, nDefs, nPropInst)

def declKinds : List Name :=
  [``Parser.Command.declaration, ``Parser.Command.«in»]

/-- Commands that define syntax: notations (including Mathlib's `notation3`), macros,
elaborators, binder predicates. Their kind names are matched by substring so that library-defined
command kinds are covered. -/
def isNotationKind (k : Name) : Bool :=
  let s := k.toString
  ["notation", "macro", "syntax", "elab", "infix", "prefix", "postfix", "mixfix",
   "binderPredicate", "syntaxCat"].any fun w => (s.splitOn w).length > 1

def contextKinds : List Name :=
  [``Parser.Command.«open», ``Parser.Command.«namespace», ``Parser.Command.«section»,
   ``Parser.Command.«end», ``Parser.Command.«variable», ``Parser.Command.«set_option»,
   ``Parser.Command.«universe»,
   ``Parser.Command.include, ``Parser.Command.«omit»,
   ``Parser.Command.attribute, ``Parser.Command.«export»]

/-- The innermost command of an `… in` chain. -/
partial def innermost (stx : Syntax) : Syntax :=
  if stx.getKind == ``Parser.Command.«in» then innermost stx[2] else stx

def bytesToString (bs : ByteArray) (a b : Nat) : String :=
  String.fromUTF8! (bs.extract a b)

/-- Strip module-system syntax that a plain file does not accept. -/
def stripModuleSyntax (s : String) : String :=
  let s := s.replace "@[expose] public noncomputable section" "noncomputable section"
  let s := s.replace "@[expose] public section" "section"
  let s := s.replace "public noncomputable section" "noncomputable section"
  let s := s.replace "public section" "section"
  let s := s.replace "@[expose] public " ""
  let s := s.replace "@[expose]\npublic " ""
  let s := s.replace "@[expose, " "@["
  let s := s.replace ", expose]" "]"
  let s := s.replace "@[expose]" ""
  let s := s.replace "\npublic " "\n"
  let s := s.replace "\nprivate " "\nprivate "
  s

structure ModuleResult where
  module : Name
  text : String
  keptDecls : Nat
  sorries : Nat
  imports : Array Name

structure CmdRec where
  s : Nat
  e : Nat
  kind : Name
  ik : Name
  dk : Name
  ns : String
  inc : String
  /-- (start, end, ascribed, bare, statement constants, proof constants, isTactic, section
  variables, isExpansion) -/
  reps : Array (Nat × Nat × String × String × Array Name × Array Name × Bool × Array String × Bool)
  /-- for a notation command: (token, full name) of the identifiers in its expansion -/
  quals : Array (String × String)
  /-- (start, end, full name) of identifiers that denote a global constant by a shorter name -/
  idents : Array (Nat × Nat × String)
  deriving Inhabited

def helperCfg : IO.Process.StdioConfig := { stdin := .null, stdout := .null, stderr := .null }

def helperArgs (modName : Name) (path : System.FilePath) : Array String :=
  #["env", "lean", "--run", "scripts/ElabInfo.lean", modName.toString, path.toString,
    s!".lake/genspec/elab/{modName}.json"]

/-- Modification time of a file, as a comparable pair. -/
def mtime (p : System.FilePath) : IO (Int × Nat) := do
  let m ← p.metadata
  return (m.modified.sec, m.modified.nsec.toNat)

def newer (a b : Int × Nat) : Bool := a.1 > b.1 || (a.1 == b.1 && a.2 > b.2)

/-- Whether the helper's report for a module is newer than the module and the helper itself. -/
def reportFresh (modName : Name) (path : System.FilePath) : IO Bool := do
  let json : System.FilePath := s!".lake/genspec/elab/{modName}.json"
  if !(← json.pathExists) then return false
  let tj ← mtime json
  return newer tj (← mtime path) && newer tj (← mtime "scripts/ElabInfo.lean")

/-- Run the helper on the given modules, `parallel` processes at a time. -/
def runHelpers (todo : Array (Name × System.FilePath)) (parallel : Nat := 3) : IO Unit := do
  IO.FS.createDirAll ".lake/genspec/elab"
  let mut pending := todo
  while !pending.isEmpty do
    let n := min parallel pending.size
    let batch := pending.extract 0 n
    pending := pending.extract n pending.size
    let mut children : Array (Name × IO.Process.Child helperCfg) := #[]
    for (m, path) in batch do
      IO.eprintln s!"elaborating {m}"
      let child ← IO.Process.spawn { toStdioConfig := helperCfg, cmd := "lake", args := helperArgs m path }
      children := children.push (m, child)
    for (m, child) in children do
      let rc ← child.wait
      if rc != 0 then throw <| IO.userError s!"helper failed on {m} (exit {rc})"

/-- Read the helper's report for a module, running the helper first if the report is stale. -/
def runHelper (modName : Name) (path : System.FilePath) :
    IO (String × Array Name × Array CmdRec × Nat) := do
  let jsonPath : System.FilePath := s!".lake/genspec/elab/{modName}.json"
  IO.FS.createDirAll ".lake/genspec/elab"
  if !(← reportFresh modName path) then
    let out ← IO.Process.output { cmd := "lake", args := helperArgs modName path }
    if out.exitCode != 0 then
      throw <| IO.userError s!"helper failed on {modName}: {out.stderr}"
  let j ← match Json.parse (← IO.FS.readFile jsonPath) with
    | .ok j => pure j
    | .error e => throw <| IO.userError s!"bad json for {modName}: {e}"
  let getStr (j : Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""
  let getNat (j : Json) (k : String) : Nat := (j.getObjValAs? Nat k).toOption.getD 0
  let source := getStr j "source"
  let errors := getNat j "errors"
  let imports := ((j.getObjValAs? (Array String) "imports").toOption.getD #[]).map String.toName
  let cmds := (j.getObjValAs? (Array Json) "commands").toOption.getD #[]
  let recs := cmds.map fun c =>
    let names (j : Json) : Array Name :=
      (j.getArr?.toOption.getD #[]).filterMap fun x => (x.getStr?.toOption).map String.toName
    let reps := ((c.getObjValAs? (Array Json) "reps").toOption.getD #[]).filterMap fun r =>
      match r.getArrVal? 0, r.getArrVal? 1, r.getArrVal? 2, r.getArrVal? 3 with
      | .ok a, .ok b, .ok t, .ok u =>
        match a.getNat?, b.getNat?, t.getStr?, u.getStr? with
        | .ok a, .ok b, .ok t, .ok u =>
          let cs := names ((r.getArrVal? 4).toOption.getD Json.null)
          let tl := names ((r.getArrVal? 5).toOption.getD Json.null)
          let tac := ((r.getArrVal? 6).toOption.bind (·.getBool?.toOption)).getD true
          let fv := ((r.getArrVal? 7).toOption.bind (·.getArr?.toOption)).getD #[] |>.filterMap (·.getStr?.toOption)
          let isExp := ((r.getArrVal? 8).toOption.bind (·.getBool?.toOption)).getD false
          some (a, b, t, u, cs, tl, tac, fv, isExp)
        | _, _, _, _ => none
      | _, _, _, _ => none
    let quals := ((c.getObjValAs? (Array Json) "quals").toOption.getD #[]).filterMap fun q =>
      match q.getArrVal? 0, q.getArrVal? 1 with
      | .ok a, .ok b =>
        match a.getStr?, b.getStr? with
        | .ok a, .ok b => some (a, b)
        | _, _ => none
      | _, _ => none
    let idents := ((c.getObjValAs? (Array Json) "idents").toOption.getD #[]).filterMap fun q =>
      match q.getArrVal? 0, q.getArrVal? 1, q.getArrVal? 2 with
      | .ok a, .ok b, .ok n =>
        match a.getNat?, b.getNat?, n.getStr? with
        | .ok a, .ok b, .ok n => some (a, b, n)
        | _, _, _ => none
      | _, _, _ => none
    { s := getNat c "s", e := getNat c "e", kind := (getStr c "kind").toName, ik := (getStr c "ik").toName,
      dk := (getStr c "dk").toName, ns := getStr c "ns", inc := getStr c "inc", reps, quals, idents }
  return (source, imports, recs, errors)

def modulePath (modName : Name) : System.FilePath := (modName.toString.replace "." "/") ++ ".lean"

/-- The modules a source file imports, read from its header text. -/
def headerImports (path : System.FilePath) : IO (Array Name) := do
  let src ← IO.FS.readFile path
  let mut out : Array Name := #[]
  for line in src.splitOn "\n" do
    let l : String := line.trimLeft
    let l : String := if l.startsWith "public " then (l.drop 7).toString else l
    let l : String := if l.startsWith "meta " then (l.drop 5).toString else l
    if l.startsWith "import " then
      let body := ((l.drop 7).toString.splitOn "--").headD ""
      for w in body.splitOn " " do
        if w.length > 0 && (w.get 0).isAlpha then out := out.push w.toName
  return out

def isNotationLine (l : String) : Bool :=
  l.startsWith "notation" || l.startsWith "scoped notation" || l.startsWith "local notation" ||
  l.startsWith "macro" || l.startsWith "syntax" || l.startsWith "scoped syntax" ||
  l.startsWith "infix" || l.startsWith "prefix" || l.startsWith "postfix" ||
  l.startsWith "scoped infix" || l.startsWith "scoped prefix" || l.startsWith "scoped postfix" ||
  l.startsWith "elab" || l.startsWith "macro_rules" || l.startsWith "scoped macro"

/-- Whether a module defines notation-like syntax: a textual test on lines outside comments. -/
def moduleHasNotation (modName : Name) : IO Bool := do
  let src ← IO.FS.readFile (modulePath modName)
  let mut depth : Nat := 0
  for line in src.splitOn "\n" do
    let l : String := line.trimLeft
    if depth == 0 && !(l.startsWith "--") && isNotationLine l then return true
    let opens := (line.splitOn "/-").length - 1
    let closes := (line.splitOn "-/").length - 1
    depth := (depth + opens) - min (depth + opens) closes
  return false

/-- Replacements the compile step found ill-typed when ascribed, keyed by (module, start, end);
they are emitted as bare `sorry` on the next run. Written by `scripts/genspec_fallback.py`. -/
def readBareMarks (root : Name) : IO (Std.HashSet (String × Nat × Nat)) := do
  let path : System.FilePath := s!"scripts/genspec-state/{root}.bare.json"
  if !(← path.pathExists) then return {}
  match Json.parse (← IO.FS.readFile path) with
  | .ok (Json.arr items) =>
    return items.foldl (init := {}) fun acc j =>
      match j.getObjValAs? String "module", j.getObjValAs? Nat "a", j.getObjValAs? Nat "b" with
      | .ok m, .ok a, .ok b => acc.insert (m, a, b)
      | _, _, _ => acc
  | _ => return {}

/-- Remove every comment (docstrings, module docs, block and line comments) outside string
literals; block comments nest. The file is meant to be read as code only. -/
def stripComments (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let mut out : Array Char := #[]
  let mut i := 0
  let mut depth := 0
  while i < cs.size do
    let c := cs[i]!
    let next := if i + 1 < cs.size then cs[i+1]! else ' '
    if depth > 0 then
      if c == '-' && next == '/' then
        depth := depth - 1
        i := i + 2
      else if c == '/' && next == '-' then
        depth := depth + 1
        i := i + 2
      else i := i + 1
    else if c == '/' && next == '-' then
      depth := 1
      i := i + 2
    else if c == '-' && next == '-' then
      while i < cs.size && cs[i]! != '\n' do i := i + 1
    else if c == '"' then
      out := out.push c
      i := i + 1
      while i < cs.size do
        let d := cs[i]!
        out := out.push d
        if d == '\\' && i + 1 < cs.size then
          out := out.push cs[i+1]!
          i := i + 2
        else if d == '"' then
          i := i + 1
          break
        else i := i + 1
    else
      out := out.push c
      i := i + 1
  return String.mk out.toList

/-- Drop trailing spaces, leading and trailing blank lines, and runs of blank lines. -/
def tidy (s : String) : String := Id.run do
  let mut out : Array String := #[]
  let mut prevBlank := true
  for l in s.splitOn "\n" do
    let l := String.mk ((l.toList.reverse.dropWhile (· == ' ')).reverse)
    if l.isEmpty then
      if !prevBlank then out := out.push l
      prevBlank := true
    else
      out := out.push l
      prevBlank := false
  while !out.isEmpty && out.back!.isEmpty do out := out.pop
  return "\n".intercalate out.toList

/-- The environment with the repository's `app.FooCat.of` delaborators erased, so that bundled
objects print as `CommRingCat.of ℂ` rather than through the `↧` notation the challenge file lacks. -/
def withoutBundlingDelabs (env : Environment) : Environment :=
  let st := PrettyPrinter.Delaborator.delabAttribute.ext.getState env
  let victims := st.table.fold (init := #[]) fun acc key entries =>
    if key.getRoot == `app && (match key with | .str _ "of" => true | _ => false) then
      entries.foldl (init := acc) fun acc e =>
        let m := (env.getModuleIdxFor? e.declName).map (fun i => env.header.moduleNames[i.toNat]!) |>.getD .anonymous
        if isLocalModule m then acc.push e.declName else acc
    else acc
  if victims.isEmpty then env
  else
    PrettyPrinter.Delaborator.delabAttribute.ext.modifyState env fun s =>
      { s with erased := victims.foldl (init := s.erased) fun acc n => acc.insert n }

/-- For a proof-valued declaration (a sorried instance), the instance hypotheses its source takes
anonymously from `variable` that nothing else in its signature mentions, printed with full names.
Lean includes such a section variable only if the body uses it; once the proof that used it is a
`sorry`, the hypothesis would vanish and the sorried statement would be stronger than the
repository's, so the challenge file states it as an explicit binder. -/
def forcedBinders (n : Name) : MetaM (Array String) := do
  let some ci := (← getEnv).find? n | return #[]
  if !ci.isTheorem then return #[]
  forallTelescope ci.type fun xs body => do
    let mut out : Array String := #[]
    for i in [0:xs.size] do
      let x := xs[i]!
      let d ← x.fvarId!.getDecl
      if d.binderInfo.isInstImplicit && d.userName.hasMacroScopes then
        let mut mentioned := body.containsFVar x.fvarId!
        for j in [i+1:xs.size] do
          if (← xs[j]!.fvarId!.getType).containsFVar x.fvarId! then mentioned := true
        if !mentioned then
          let s ← withOptions (fun o => pp.fullNames.set o true) do ppExpr d.type
          out := out.push ((toString s).replace "\n" " ")
    return out

/-- The byte offset, inside a declaration's text, of the colon that starts its type: the first
colon at bracket depth zero after the declaration keyword, outside comments and strings. -/
def headerColon (text : String) : Option Nat := Id.run do
  let cs := text.toList.toArray
  let mut i := 0
  let mut depth : Nat := 0
  let mut seenKeyword := false
  let keywords := ["instance", "theorem", "lemma", "def", "abbrev", "example"]
  while i < cs.size do
    let c := cs[i]!
    let next := if i + 1 < cs.size then cs[i+1]! else ' '
    if c == '/' && next == '-' then
      -- comment (docstrings nest)
      let mut k := 1
      i := i + 2
      while i < cs.size && k > 0 do
        if cs[i]! == '/' && i + 1 < cs.size && cs[i+1]! == '-' then
          k := k + 1
          i := i + 2
        else if cs[i]! == '-' && i + 1 < cs.size && cs[i+1]! == '/' then
          k := k - 1
          i := i + 2
        else i := i + 1
    else if c == '-' && next == '-' then
      while i < cs.size && cs[i]! != '\n' do i := i + 1
    else if c == '"' then
      i := i + 1
      while i < cs.size && cs[i]! != '"' do
        if cs[i]! == '\\' then i := i + 1
        i := i + 1
      i := i + 1
    else if c == '(' || c == '[' || c == '{' || c == '⦃' || c == '⟨' then
      depth := depth + 1
      i := i + 1
    else if c == ')' || c == ']' || c == '}' || c == '⦄' || c == '⟩' then
      depth := depth - 1
      i := i + 1
    else if !seenKeyword && isIdFirst c then
      let mut j := i + 1
      while j < cs.size && isIdRest cs[j]! do j := j + 1
      let tok := String.mk (cs.extract i j).toList
      if depth == 0 && keywords.contains tok then seenKeyword := true
      i := j
    else if seenKeyword && depth == 0 && c == ':' && next != '=' then
      return some (String.mk (cs.extract 0 i).toList).utf8ByteSize
    else i := i + 1
  return none

/-- Constants whose uses must be written with their full name, because the audit found that the
challenge file resolved a shorter name to a different constant than the repository did. -/
def readQualifyList (root : Name) : IO (Std.HashSet String) := do
  let path : System.FilePath := s!"scripts/genspec-state/{root}.qualify.json"
  if !(← path.pathExists) then return {}
  match Json.parse (← IO.FS.readFile path) with
  | .ok (Json.arr items) =>
    return items.foldl (init := {}) fun acc j =>
      match j.getStr? with
      | .ok s => acc.insert s
      | _ => acc
  | _ => return {}

/-- Rewrite the identifiers after the first `=>` of a notation command with their full names. -/
def qualifyText (s : String) (quals : Array (String × String)) : String := Id.run do
  if quals.isEmpty then return s
  let cs := s.toList.toArray
  let mut out : Array Char := #[]
  let mut i := 0
  let mut afterArrow := false
  while i < cs.size do
    let c := cs[i]!
    if c == '"' then
      out := out.push c
      i := i + 1
      while i < cs.size && cs[i]! != '"' do
        if cs[i]! == '\\' then
          out := out.push cs[i]!
          i := i + 1
        if i < cs.size then
          out := out.push cs[i]!
          i := i + 1
      if i < cs.size then
        out := out.push cs[i]!
        i := i + 1
    else if !afterArrow then
      if c == '=' && i + 1 < cs.size && cs[i+1]! == '>' then afterArrow := true
      out := out.push c
      i := i + 1
    else if c == '.' && i + 1 < cs.size && cs[i+1]! == '{' then
      -- universe levels, not term identifiers
      while i < cs.size && cs[i]! != '}' do
        out := out.push cs[i]!
        i := i + 1
      if i < cs.size then
        out := out.push cs[i]!
        i := i + 1
    else if isIdFirst c then
      let mut j := i + 1
      while j < cs.size && (isIdRest cs[j]! || (cs[j]! == '.' && j + 1 < cs.size && isIdFirst cs[j+1]!)) do
        j := j + 1
      let tok := String.mk (cs.extract i j).toList
      let rep := ((quals.find? (·.1 == tok)).map (·.2)).getD tok
      out := out ++ rep.toList.toArray
      i := j
    else
      out := out.push c
      i := i + 1
  return String.mk out.toList

/-- Declarations that `scripts/SpecAudit.lean` found unreachable from the root in the compiled
file (instances mined from proofs that end up elided), to be left out. -/
def readDropList (root : Name) : IO (Std.HashSet Name) := do
  let path : System.FilePath := s!"scripts/genspec-state/{root}.drop.json"
  if !(← path.pathExists) then return {}
  match Json.parse (← IO.FS.readFile path) with
  | .ok (Json.arr items) =>
    return items.foldl (init := {}) fun acc j =>
      match j.getStr? with
      | .ok s => acc.insert s.toName
      | _ => acc
  | _ => return {}

def processModule (modName : Name) (kept : Array Kept) (localNames : Array String)
    (okConst : Name → Bool) (bare : Std.HashSet (String × Nat × Nat))
    (qualify : Std.HashSet String) (forced : Std.HashMap Name (Array String)) : IO (Option ModuleResult) := do
  let path := modulePath modName
  let keptHere := kept.filter (·.module == modName)
  let hasNotation ← moduleHasNotation modName
  if keptHere.isEmpty && !hasNotation then return none
  let (input, imports, cmds, errors) ← runHelper modName path
  if errors > 0 then IO.eprintln s!"  {errors} elaboration errors reported for {modName}"
  let bs := input.toUTF8
  let fileMap := FileMap.ofString input
  -- (text, tag): 0 = declaration or notation, 1 = context command, 2 = scope opener, 3 = end
  let mut out : Array (String × Nat) := #[]
  let mut scopes : Array (Option Name) := #[]
  let mut nKept := 0
  let mut nSorry := 0
  for c in cmds do
    let (cs, ce) := (c.s, c.e)
    let cmdLine := (fileMap.toPosition ⟨cs⟩).line
    let cmdEndLine := (fileMap.toPosition ⟨ce⟩).line
    let isDecl := c.ik == ``Parser.Command.declaration
    let keep : Bool :=
      if isDecl then
        keptHere.any fun d => cmdLine ≤ d.startLine && d.startLine ≤ cmdEndLine
      -- notation commands are kept (a module included only for them contributes nothing else);
      -- a notation whose expansion needs a repository declaration that is not kept is one the
      -- kept text does not use, since a use would have pulled that declaration into the closure
      else if isNotationKind c.ik then true
      else if contextKinds.contains c.ik then
        if c.ik == ``Parser.Command.attribute && c.kind != ``Parser.Command.«in» then
          -- a standalone `attribute` command is dropped only if it mentions a repository
          -- declaration that is not kept (typically a lemma); Mathlib names are fine
          let text := bytesToString bs cs ce
          let words := (text.splitOn " ").filter fun w => w.length > 0 && !w.startsWith "["
            && !w.startsWith "@" && w != "attribute" && !w.startsWith "in"
          words.all fun w =>
            let isLocal := localNames.any fun n => n == w || n.endsWith ("." ++ w)
            !isLocal || kept.any fun d => d.name.toString == w || d.name.toString.endsWith ("." ++ w)
        else true
      else false
    if !keep then continue
    -- standalone `include` only affects theorems, of which the spec has none
    if c.ik == ``Parser.Command.include && c.kind != ``Parser.Command.«in» then continue
    let tag : Nat :=
      if isDecl || isNotationKind c.ik then 0
      else if c.ik == ``Parser.Command.«namespace» || c.ik == ``Parser.Command.«section» then 2
      else if c.ik == ``Parser.Command.«end» then 3
      else 1
    if c.ik == ``Parser.Command.«namespace» then scopes := scopes.push (some c.ns.toName)
    else if c.ik == ``Parser.Command.«section» then scopes := scopes.push none
    else if c.ik == ``Parser.Command.«end» then scopes := scopes.pop
    -- splice replacements into the command text; on overlap the outermost one wins
    let splice (chosenText : Array (Nat × Nat × String)) : String × Nat := Id.run do
      let inside := chosenText.filter fun (a, b, _) => cs ≤ a && b ≤ ce
      let ordered := inside.qsort fun x y => x.1 < y.1 || (x.1 == y.1 && x.2.1 > y.2.1)
      let mut chosen : Array (Nat × Nat × String) := #[]
      let mut maxEnd := 0
      for r in ordered do
        if r.1 ≥ maxEnd then
          chosen := chosen.push r
          maxEnd := r.2.1
      let mut pieces : Array String := #[]
      let mut cursor := cs
      for (a, b, t) in chosen do
        pieces := pieces.push (bytesToString bs cursor a)
        pieces := pieces.push t
        cursor := b
      pieces := pieces.push (bytesToString bs cursor ce)
      -- `↧` expansions are replacements too, but not proof obligations
      let obligations := (chosen.filter fun (_, _, t) => (t.splitOn "sorry").length > 1).size
      return (String.join pieces.toList, obligations)
    let mut text := bytesToString bs cs ce
    -- identifiers the audit asked to write in full
    let identReps : Array (Nat × Nat × String) := c.idents.filterMap fun (a, b, n) =>
      if qualify.contains n then some (a, b, n) else none
    if !isDecl then
      -- `variable` binders and other context commands only have their `↧` uses expanded
      let (spliced, _) := splice ((c.reps.filterMap fun (a, b, t, _, _, _, _, _, isExp) =>
        if isExp then some (a, b, t) else none) ++ identReps)
      text := spliced
      -- a notation's expansion is resolved where the notation is used: write it in full
      if isNotationKind c.ik then text := qualifyText text c.quals
    if isDecl then
      nKept := nKept + 1
      -- a term-mode proof whose repository constants are all in the spec is kept as written
      -- (Mathlib is imported); otherwise it is elided, ascribed with its statement only when every
      -- repository constant the statement mentions is in the spec
      let mentions (txt : String) (v : String) : Bool := Id.run do
        -- crude token test: the variable name as a whole identifier
        let mut cur := ""
        for ch in txt.toList do
          if ch.isAlphanum || ch == '_' || ch == '\'' then cur := cur.push ch
          else
            if cur == v then return true
            cur := ""
        return cur == v
      let chosenText : Array (Nat × Nat × String × Bool) := c.reps.filterMap fun (a, b, t, u, cs, tl, tac, fv, isExp) =>
        if isExp then some (a, b, t, false)
        else if !tac && tl.all okConst then none
        else
          let txt := if bare.contains (modName.toString, a, b) then u
            else if cs.all okConst then t else u
          -- a replacement must keep mentioning the section variables the proof used, or the
          -- definition loses those parameters (`include` only works for theorems)
          let lost := fv.filter fun v => !mentions txt v
          if lost.isEmpty then some (a, b, txt, true)
          else
            -- tactic-suffix replacements have identical bare/ascribed texts and no constants
            if tac && t == u && cs.isEmpty && tl.isEmpty then
              let haves := " ".intercalate (lost.toList.map fun v => s!"have _ := {v};")
              some (a, b, s!"{haves} {txt}", true)
            else
              -- a term-level `let` elaborates eagerly, so the ascription still determines implicit
              -- arguments (a `by` block would be postponed and could not)
              let lets := " ".intercalate (lost.toList.map fun v => s!"let _ := {v};")
              if txt.startsWith ":= " then
                some (a, b, s!":= ({lets} {txt.drop 3})", true)
              else
                some (a, b, s!"({lets} {txt})", true)
      -- instance hypotheses the source signature took from `variable` and only the (now elided)
      -- proof used: stated as explicit binders before the colon of the signature
      let forcedHere : Array String := (keptHere.filter fun d => cmdLine ≤ d.startLine && d.startLine ≤ cmdEndLine)
        |>.foldl (init := #[]) fun acc d => (forced.getD d.name #[]).foldl (fun acc t => if acc.contains t then acc else acc.push t) acc
      let binderReps : Array (Nat × Nat × String) := Id.run do
        if forcedHere.isEmpty then return #[]
        match headerColon (bytesToString bs cs ce) with
        | some off => #[(cs + off, cs + off, " ".intercalate (forcedHere.toList.map fun t => s!"[{t}]") ++ " ")]
        | none => #[]
      if !forcedHere.isEmpty && binderReps.isEmpty then
        IO.eprintln s!"note: {modName}: could not place the binders {forcedHere} in a declaration at line {cmdLine}"
      let chosenText : Array (Nat × Nat × String) := chosenText.map fun (a, b, t, _) => (a, b, t)
      let (spliced, obligations) := splice (chosenText ++ identReps ++ binderReps)
      text := spliced
      nSorry := nSorry + obligations
      -- force the section variables the original signature included but that no longer occur
      -- in the text once their proofs are gone (Lean includes a variable only when it is used)
      let isIdent (w : String) := w.length > 0 && w.all fun ch => ch.isAlphanum || ch == '_' || ch == '\''
      let incVars : List String := ((c.inc.splitOn " ").map (toString ·)).filter fun w =>
        isIdent w && w != "include" && w != "in"
      -- tokens of the code, skipping comments and docstrings (a docstring mentioning `d` is not
      -- a use of the variable `d`)
      let mut toks : List String := []
      let mut cur := ""
      let mut depth : Nat := 0      -- block comment nesting
      let mut lineComment := false
      let chars := text.toList.toArray
      let mut i := 0
      while i < chars.size do
        let ch := chars[i]!
        let next := if i + 1 < chars.size then chars[i+1]! else ' '
        if lineComment then
          if ch == '\n' then lineComment := false
          i := i + 1
        else if depth > 0 then
          if ch == '-' && next == '/' then depth := depth - 1; i := i + 2
          else if ch == '/' && next == '-' then depth := depth + 1; i := i + 2
          else i := i + 1
        else if ch == '/' && next == '-' then
          if cur != "" then toks := cur :: toks; cur := ""
          depth := 1; i := i + 2
        else if ch == '-' && next == '-' then
          if cur != "" then toks := cur :: toks; cur := ""
          lineComment := true; i := i + 2
        else
          if ch.isAlphanum || ch == '_' || ch == '\'' then cur := cur.push ch
          else if cur != "" then
            toks := cur :: toks
            cur := ""
          i := i + 1
      if cur != "" then toks := cur :: toks
      let missing : List String := incVars.filter fun v => !(toks.any (· == v))
      if !missing.isEmpty then
        -- `include` would only help theorems; every elided proof already re-mentions the section
        -- variables it used, so anything left here deserves a look
        IO.eprintln s!"note: {modName}: section variable(s) {" ".intercalate missing} no longer mentioned in a kept declaration"
    text := tidy (stripComments text)
    if !text.isEmpty then out := out.push (text, tag)
  for sc in scopes.reverse do
    match sc with
    | some n => out := out.push (s!"end {n}", 3)
    | none => out := out.push ("end", 3)
  -- Emit context commands (`variable`, `open`, scope openers, …) only when a kept declaration or
  -- notation follows them in the same scope; scopes that end up empty disappear, together with
  -- `variable`s whose types may mention dropped declarations.
  let mut emitted : Array String := #[]
  let mut pending : Array String := #[]
  -- for each open scope: index in `pending` of its opener, or none once flushed
  let mut stack : Array (Option Nat) := #[]
  for (t, tag) in out do
    if tag == 2 then
      stack := stack.push (some pending.size)
      pending := pending.push t
    else if tag == 3 then
      match stack.back? with
      | some (some idx) =>
        pending := pending.extract 0 idx
        stack := stack.pop
      | some none =>
        emitted := emitted ++ pending
        pending := #[]
        emitted := emitted.push t
        stack := stack.pop
      | none => emitted := emitted.push t
    else if tag == 1 then
      pending := pending.push t
    else
      emitted := emitted ++ pending
      pending := #[]
      emitted := emitted.push t
      stack := stack.map fun _ => none
  let body := String.intercalate "\n\n" emitted.toList ++ "\n"
  return some ⟨modName, body, nKept, nSorry, imports⟩

/-- Local modules in the import closure of `root`'s module, in import (dependency) order. -/
def modulesInOrder (env : Environment) (rootModule : Name) : Array Name := Id.run do
  let names := env.header.moduleNames
  let idxOf : Std.HashMap Name Nat := names.zipIdx.foldl (fun m (n, i) => m.insert n i) {}
  let mut needed : Std.HashSet Name := {}
  let mut stack := #[rootModule]
  while !stack.isEmpty do
    let m := stack.back!
    stack := stack.pop
    if needed.contains m || !isLocalModule m then continue
    needed := needed.insert m
    if let some i := idxOf[m]? then
      for imp in env.header.moduleData[i]!.imports do
        stack := stack.push imp.module
  return names.filter needed.contains

def generate (root : Name) (outPath : System.FilePath) (title : String) (force : Array Name := #[]) :
    MetaM Unit := do
  let env ← getEnv
  let (kept, keptRaw, nDefs, nPropInst) ← closure root force
  let drop ← readDropList root
  if !drop.isEmpty then IO.eprintln s!"{drop.size} declaration(s) left out by scripts/genspec-state/{root}.drop.json"
  let kept := kept.filter fun k => !drop.contains k.name
  let keptRaw : Std.HashSet Name := keptRaw.fold (fun s n => if drop.contains n then s else s.insert n) {}
  let some rootIdx := env.getModuleIdxFor? root | throwError "no module for {root}"
  let rootModule := env.header.moduleNames[rootIdx.toNat]!
  let mods := modulesInOrder env rootModule
  let localNames : Array String := env.constants.map₁.fold (init := #[]) fun acc n _ =>
    if isLocalModule ((env.getModuleIdxFor? n).map (fun i => env.header.moduleNames[i.toNat]!) |>.getD .anonymous)
    then acc.push n.toString else acc
  -- modules to include: those with kept declarations, plus notation-defining modules that one of
  -- them imports directly (notations reached only through dropped modules are not needed)
  let keptModules : Std.HashSet Name := kept.foldl (fun s k => s.insert k.module) {}
  let mut direct : Std.HashSet Name := {}
  for m in keptModules.toList do
    for imp in ← headerImports (modulePath m) do
      if isLocalModule imp then direct := direct.insert imp
  let mut included : Std.HashSet Name := keptModules
  for m in mods do
    if !included.contains m && direct.contains m && (← moduleHasNotation m) then
      included := included.insert m
  -- the `↧` notation is implemented by meta code; its uses are expanded instead of copying it
  included := included.erase `HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
  -- elaborate the included modules that need it, in parallel, reusing fresh reports
  let mut todo : Array (Name × System.FilePath) := #[]
  for m in mods do
    if included.contains m && !(← reportFresh m (modulePath m)) then todo := todo.push (m, modulePath m)
  IO.eprintln s!"{todo.size} modules to elaborate, {included.size} included, {mods.size} in the import closure"
  let parallel := ((← IO.getEnv "GENSPEC_PARALLEL").bind (·.toNat?)).getD 4
  runHelpers todo parallel
  -- Instance mining cannot tell a Prop-valued `local instance` (needed: typeclass synthesis used
  -- it invisibly) from a plain theorem the source binds with `let :=` (its use site is a visible
  -- proof, to be elided). Both are stored as theorems without an instance attribute; the helper
  -- reports know the source keyword, so drop the ones declared with `theorem`.
  let mut dropped : Std.HashSet Name := {}
  for k in kept do
    if let some (.thmInfo _) := env.find? k.name then
      if !(← isInstance k.name) then
        let (input, _, cmds, _) ← runHelper k.module (modulePath k.module)
        let fm := FileMap.ofString input
        for c in cmds do
          let l0 := (fm.toPosition ⟨c.s⟩).line
          let l1 := (fm.toPosition ⟨c.e⟩).line
          if l0 ≤ k.startLine && k.startLine ≤ l1 && c.dk == ``Parser.Command.theorem then
            dropped := dropped.insert k.name
  if !dropped.isEmpty then
    IO.eprintln s!"{dropped.size} theorem(s) mined as instances dropped; their uses are elided"
  let kept := kept.filter fun k => !dropped.contains k.name
  let keptRaw : Std.HashSet Name := keptRaw.fold (fun s n => if dropped.contains n then s else s.insert n) {}
  let keptParents : Std.HashSet Name := kept.foldl (fun s k => s.insert k.name) {}
  let okConst (c : Name) : Bool :=
    keptRaw.contains c || keptParents.contains (parentName env c) ||
      !isLocalModule ((env.getModuleIdxFor? c).map (fun i => env.header.moduleNames[i.toNat]!) |>.getD .anonymous)
  let bare ← readBareMarks root
  if !bare.isEmpty then IO.eprintln s!"{bare.size} replacements forced bare by scripts/genspec-state/{root}.bare.json"
  let qualify ← readQualifyList root
  if !qualify.isEmpty then IO.eprintln s!"{qualify.size} constant(s) written in full by scripts/genspec-state/{root}.qualify.json"
  modifyEnv withoutBundlingDelabs
  let mut forced : Std.HashMap Name (Array String) := {}
  for k in kept do
    let ts ← forcedBinders k.name
    if !ts.isEmpty then forced := forced.insert k.name ts
  -- the constants each kept declaration uses in the repository (auxiliary constants grouped with
  -- their declaration, private names unmangled), for the audit's drift check
  let heads : Std.HashSet Name := kept.foldl (fun s k => s.insert k.name) {}
  -- a constant belongs to a kept declaration if it is that declaration, one of its auxiliary
  -- constants (`_proof_n`, `match_n`, recursors, …), or a field or constructor of that structure;
  -- other declarations of the same namespace do not belong to it
  let isAuxComponent (s : String) : Bool :=
    s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "eq_" ||
    ["mk", "rec", "recOn", "casesOn", "noConfusion", "noConfusionType", "below", "brecOn", "ibelow",
     "binductionOn", "sizeOf_spec", "inj", "injEq", "ctorIdx", "toCtorIdx"].contains s
  let headOf (n : Name) : Option Name := Id.run do
    if heads.contains n then return some n
    let mut p := n.getPrefix
    let mut suffixHead : String := match n with | .str _ s => s | _ => ""
    while !p.isAnonymous do
      if heads.contains p then
        if n == p || isAuxComponent suffixHead then return some p
        -- fields of a kept structure, constructors of a kept inductive
        let fields := (getStructureInfo? env p).map (·.fieldNames.map toString) |>.getD #[]
        let ctors := match env.find? p with
          | some (.inductInfo v) => v.ctors.map toString
          | _ => []
        if fields.contains suffixHead || ctors.contains n.toString then return some p
        return none
      suffixHead := match p with | .str _ s => s | _ => ""
      p := p.getPrefix
    if heads.contains n then some n else none
  let norm (n : Name) : Name := (privateToUserName? n).getD n
  let isMatcher (n : Name) : Bool := n.components.any fun c => (c.toString.startsWith "match_")
  let uses : Std.HashMap String (Std.HashSet String) := env.constants.map₁.fold (init := {}) fun acc n ci =>
    if !isLocalModule ((env.getModuleIdxFor? n).map (fun i => env.header.moduleNames[i.toNat]!) |>.getD .anonymous) then acc
    else match headOf n with
      | none => acc
      | some h =>
        let key := (norm h).toString
        -- the data of the declaration: types always, values unless they are proofs (the
        -- challenge file replaces those by `sorry`)
        let consts : NameSet :=
          if ci.isTheorem then (if n == h then ci.type.getUsedConstantsAsSet else {})
          else ci.getUsedConstantsAsSet
        let cur := consts.toList.foldl (init := acc.getD key {}) fun s u =>
          let u := norm u
          if u == norm h || (norm h).isPrefixOf u || u == ``sorryAx || isMatcher u then s else s.insert u.toString
        acc.insert key cur
  IO.FS.writeFile ".lake/genspec/source-uses.json"
    (Json.mkObj (uses.toList.map fun (h, s) => (h, Json.arr (s.toList.toArray.map Json.str)))).compress
  let mut results : Array ModuleResult := #[]
  for m in mods do
    if included.contains m then
      if let some r ← processModule m kept localNames okConst bare qualify forced then results := results.push r
  let totalDecls := results.foldl (· + ·.keptDecls) 0
  let totalSorry := results.foldl (· + ·.sorries) 0
  let license := "/-\nCopyright 2026 The Formal Conjectures Authors.\n\nLicensed under the Apache License, Version 2.0 (the \"License\");\nyou may not use this file except in compliance with the License.\nYou may obtain a copy of the License at\n\n    https://www.apache.org/licenses/LICENSE-2.0\n\nUnless required by applicable law or agreed to in writing, software\ndistributed under the License is distributed on an \"AS IS\" BASIS,\nWITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.\nSee the License for the specific language governing permissions and\nlimitations under the License.\n-/\n"
  -- a plain comment: a module docstring is a command and could not precede the import
  let doc := s!"/-\n# {title}\n\nThis file is generated by `scripts/genspec.sh`; do not edit it by hand. `scripts/SpecAudit.lean` checks\nthat every declaration in it is reachable from the statement by unfolding definitions.\n\nIt imports only Mathlib and contains the transitive closure of the definitions needed to state\n`{root}`, in dependency order, verbatim from the repository (docstrings and comments stripped)\ntogether with the notations and context they need. It contains no theorem: every maximal proof\nsubterm inside a definition body, and the proof of every Prop-valued instance the definitions need,\nis replaced by `sorry`. Each of those `sorry`s is a proof obligation that is discharged in the\nrepository, and none of them affects what the definitions mean. The whole file is a\n`noncomputable section`, since nothing in it needs executable code.\n\nDeclarations kept: {totalDecls} (from {nDefs} data constants and {nPropInst} Prop-valued instances).\nProof obligations elided as `sorry`: {totalSorry}.\n-/\n"
  let opts := "set_option autoImplicit false\nset_option relaxedAutoImplicit false\nset_option pp.unicode.fun true\nset_option linter.unusedVariables false\nset_option linter.style.longLine false\n\nnoncomputable section\n"
  let body := String.intercalate "\n" (results.toList.map (·.text))
  IO.FS.writeFile outPath (license ++ "\n" ++ doc ++ "import Mathlib\n\n" ++ opts ++ "\n" ++ body ++ "\nend\n")
  IO.println s!"== {root}: wrote {outPath}: {results.size} modules, {totalDecls} declarations, {totalSorry} sorries; import Mathlib"
  for r in results do
    IO.println s!"   {r.module}: {r.keptDecls} declarations, {r.sorries} sorries"

end GenSpec

/-- Generate `Challenge/Constructed.lean`, the self-contained statement of `HodgeConjecture`. -/
def GenSpec.main : MetaM Unit :=
  GenSpec.generate `HodgeConjecture "Challenge/Constructed.lean"
    "The Hodge conjecture: self-contained statement"

#eval GenSpec.main

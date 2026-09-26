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
import Lean

/-!
# Helper for `scripts/GenSpec.lean`: elaborate one module and report proof positions

Usage (normally invoked by the generator, one process per module):

    lake env lean --run scripts/ElabInfo.lean <module name> <source path> <output json>

The output lists every top-level command of the module with its byte range and syntax kinds,
and, for declaration commands, the byte ranges of every maximal proof subterm in the elaborated
declaration and of every Prop-goal suffix of a tactic block, each with the text that replaces it.
-/

open Lean Elab Meta

namespace ElabInfo

/-- Byte range of a syntax node. -/
def rangeOf (stx : Syntax) : Option (Nat × Nat) :=
  match stx.getPos?, stx.getTailPos? with
  | some a, some b => if b.byteIdx > a.byteIdx then some (a.byteIdx, b.byteIdx) else none
  | _, _ => none

/-- Position of the command a tree belongs to. -/
partial def treeCmdPos : InfoTree → Option Nat
  | .context _ t => treeCmdPos t
  | .node (.ofCommandInfo ci) _ => (rangeOf ci.stx).map (·.1)
  | .node _ cs => cs.toList.findSome? treeCmdPos
  | .hole _ => none

structure TacInfo where
  range : Nat × Nat
  allProp : Bool
  goals : Nat
  goalsBefore : List MVarId
  mctxAfter : MetavarContext

/-- Byte ranges of structure-instance fields (`f x y := v`) in a command. The elaborator attaches
proof information for a field with binders to a synthetic node spanning the whole field, so such
nodes are descended into rather than replaced, and the field's value is replaced instead. -/
partial def fieldRanges (stx : Syntax) (acc : Std.HashSet (Nat × Nat)) : Std.HashSet (Nat × Nat) := Id.run do
  let mut acc := acc
  if stx.getKind == ``Parser.Term.structInstField then
    if let some r := rangeOf stx then acc := acc.insert r
  for c in stx.getArgs do
    acc := fieldRanges c acc
  return acc

def isLocalName (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i =>
    let m := env.header.moduleNames[i.toNat]!
    (`HodgeConjecture).isPrefixOf m || (`Other).isPrefixOf m || (`Challenge.Roots).isPrefixOf m
  | none => true

/-- The environment with every repository-defined `app.FooCat.of` delaborator erased, so that
bundled objects print as `CommRingCat.of ℂ` rather than through the `↧` notation, which the
self-contained file does not define. -/
def withoutBundlingDelabs (env : Environment) : Environment :=
  let st := PrettyPrinter.Delaborator.delabAttribute.ext.getState env
  let victims := st.table.fold (init := #[]) fun acc key entries =>
    if key.getRoot == `app && (match key with | .str _ "of" => true | _ => false) then
      entries.foldl (init := acc) fun acc e =>
        if isLocalName env e.declName then acc.push e.declName else acc
    else acc
  if victims.isEmpty then env
  else
    PrettyPrinter.Delaborator.delabAttribute.ext.modifyState env fun s =>
      { s with erased := victims.foldl (init := s.erased) fun acc n => acc.insert n }

/-- The type of a proof, pretty printed on one line in its own context, together with the
repository constants it mentions; `none` if printing fails or the text could not be re-read. -/
def proofTypeString (ctx : ContextInfo) (ti : TermInfo) : IO (Option (String × Array Name)) := do
  let ctx := { ctx with env := withoutBundlingDelabs ctx.env }
  let s? ← (try
      ctx.runMetaM ti.lctx do
        let t ← instantiateMVars (← inferType ti.expr)
        if t.hasMVar then return none
        let t ← Core.betaReduce t
        let env ← getEnv
        let locals := t.getUsedConstants.filter (isLocalName env)
        withOptions (fun o => pp.fullNames.set (pp.funBinderTypes.set (pp.numericTypes.set (pp.coercions.types.set o true) true) true) true) do
          let f ← ppExpr t
          return some (toString f, locals)
    catch _ => pure none)
  match s? with
  | none => return none
  | some (s, locals) =>
    let s := s.replace "\n" " "
    let s := (s.splitOn " ").filter (· != "") |> String.intercalate " "
    if s.any (fun c => c == '?' || c == '✝' || c == '↧') || (s.splitOn "⋯").length > 1 then return none
    return some (s, locals)

/-- Whether a proof term must be elided. Proofs that only project out of hypotheses and
structures (`h.2`, `V.isIntegral`) survive unchanged; anything mentioning a theorem, an axiom, an
opaque constant, a Prop-valued definition, or an unassigned tactic block is replaced. -/
def needsElision (ctx : ContextInfo) (ti : TermInfo) : IO Bool := do
  (try
    ctx.runMetaM ti.lctx do
      let e ← instantiateMVars ti.expr
      if e.hasExprMVar then return true
      let env ← getEnv
      -- a proof survives only if it is assembled from projections of hypotheses and structures
      -- and ordinary definitions; theorems, axioms, Prop-valued definitions, and the constructors
      -- and recursors of propositional inductives (`rfl`, `And.intro`, `Eq.rec`) all go, since
      -- they may stop type-checking once the definitions they unfold contain `sorry`
      let propValued (n : Name) : MetaM Bool := do
        match env.find? n with
        | some ci => (try forallTelescope ci.type fun _ b => isProp b catch _ => pure true)
        | none => pure true
      for c in e.getUsedConstants do
        if env.isProjectionFn c then continue
        match env.find? c with
        | some (.thmInfo _) | some (.axiomInfo _) | some (.opaqueInfo _) => return true
        | some (.defnInfo _) => if ← propValued c then return true
        | some (.ctorInfo cv) => if ← propValued cv.induct then return true
        | some (.recInfo rv) => if ← propValued (rv.all.headD .anonymous) then return true
        | _ => continue
      return false
  catch _ => pure true)

/-- Syntax that must never be replaced: holes (they carry the goal for later tactics) and nodes
whose source text is a bare keyword (the elaborator attaches proof information to synthetic
`have`/`show` nodes positioned on the keyword alone). -/
def keywordOrHole (stx : Syntax) (bs : ByteArray) : Bool :=
  stx.getKind == ``Parser.Term.syntheticHole || stx.getKind == ``Parser.Term.hole || stx.isAtom ||
  match rangeOf stx with
  | some (a, b) =>
    let txt := (String.fromUTF8! (bs.extract a b)).trim
    ["have", "show", "let", "obtain", "suffices", "calc", "from", "by", "fun", "at", "with",
     "this"].contains txt
  | none => true

def isIdentByte (c : UInt8) : Bool :=
  (c ≥ 48 && c ≤ 57) || (c ≥ 65 && c ≤ 90) || (c ≥ 97 && c ≤ 122) || c == 95 || c == 39 ||
  c == 46 || c == 33 || c == 63 || c ≥ 128

/-- Field notation on a proof (`U.isOpen_foo`, `(h.comp g).symm`) attaches the proof node to a
syntax starting after the dot; the replacement must also cover the receiver. -/
partial def extendDotPrefix (bs : ByteArray) (a : Nat) : Nat := Id.run do
  let mut a := a
  let mut go := true
  while go do
    go := false
    if a ≥ 2 && bs[a-1]! == 46 then
      let prev := bs[a-2]!
      if prev == 41 then  -- ')'
        let mut depth := 0
        let mut i := a - 2
        let mut found := false
        while !found do
          let c := bs[i]!
          if c == 41 then depth := depth + 1
          else if c == 40 then
            depth := depth - 1
            if depth == 0 then found := true
          if !found then
            if i == 0 then found := true else i := i - 1
        a := i; go := true
      else if a ≥ 4 && bs[a-2]! == 0xA9 && bs[a-3]! == 0x9F && bs[a-4]! == 0xE2 then  -- '⟩'
        let mut depth := 0
        let mut i := a - 4
        let mut found := false
        while !found do
          if bs[i]! == 0xE2 && bs[i+1]! == 0x9F && bs[i+2]! == 0xA9 then depth := depth + 1
          else if bs[i]! == 0xE2 && bs[i+1]! == 0x9F && bs[i+2]! == 0xA8 then
            depth := depth - 1
            if depth == 0 then found := true
          if !found then
            if i == 0 then found := true else i := i - 1
        a := i; go := true
      else if isIdentByte prev then
        let mut i := a - 2
        while i > 0 && isIdentByte bs[i-1]! do i := i - 1
        a := i; go := true
  return a

/-- A replacement: byte range, text with the obligation ascribed, bare text, and the repository
constants the ascription mentions (the generator uses the bare text when one of them is absent
from the spec). -/
structure Rep where
  a : Nat
  b : Nat
  ascribed : String
  bare : String
  consts : Array Name
  /-- Repository constants the proof term itself uses; if all of them are in the spec (and the
  proof is not a tactic block), the generator keeps the proof as written. -/
  termLocals : Array Name
  isTactic : Bool
  /-- Section variables the proof used; a replacement that no longer mentions them must, or the
  definition loses those parameters. -/
  fvars : Array String

/-- User names of the section variables (from `vars`) among the free variables of `e`. -/
def sectionFVars (lctx : LocalContext) (vars : Array Name) (e : Expr) : Array String := Id.run do
  let mut out : Array String := #[]
  for fv in (collectFVars {} e).fvarIds do
    if let some d := lctx.find? fv then
      if vars.contains d.userName && !d.userName.hasMacroScopes && !out.contains d.userName.toString then
        out := out.push d.userName.toString
  return out

/-- The `↧x` notation of `HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation` is
implemented by an elaborator, which a self-contained file should not carry; every use is replaced
by the `FooCat.of … x` application it elaborated to. -/
def bundlingNotationKind : Name := `CategoryTheory.«term↧_»

/-- Number of explicit binders of a type. -/
partial def explicitArity : Expr → Nat
  | .forallE _ _ b bi => (if bi.isExplicit then 1 else 0) + explicitArity b
  | .mdata _ e => explicitArity e
  | _ => 0

/-- Collect maximal proof subterm ranges (with replacement text) and tactic information. -/
partial def collect (ctx? : Option ContextInfo) (t : InfoTree) (fields : Std.HashSet (Nat × Nat))
    (bs : ByteArray) (vars : Array Name) (rootCtx : IO.Ref (Option ContextInfo))
    (proofs : IO.Ref (Array Rep)) (tacs : IO.Ref (Array TacInfo))
    (expansions : IO.Ref (Array (Nat × Nat × String)))
    (idents : IO.Ref (Array (Nat × Nat × String))) : IO Unit := do
  match t with
  | .context pci t' => collect (pci.mergeIntoOuter? ctx?) t' fields bs vars rootCtx proofs tacs expansions idents
  | .hole _ => pure ()
  | .node info children =>
    let descend : IO Unit := do
      for c in children do collect ctx? c fields bs vars rootCtx proofs tacs expansions idents
    match ctx?, info with
    | some ctx, .ofTermInfo ti =>
      -- how each identifier resolved in the repository, so that a use can be qualified when the
      -- challenge file's larger import would resolve the shorter name elsewhere
      if ti.stx.isIdent then
        if let .const c _ := ti.expr then
          if let some (a, b) := rangeOf ti.stx then
            let txt := String.fromUTF8! (bs.extract a b)
            -- only a plain identifier token (synthetic syntax can span a whole command)
            let plain := !txt.isEmpty && isIdFirst txt.front && txt.all fun ch => isIdRest ch || ch == '.'
            if plain && !isPrivateName c && txt != c.toString && !txt.startsWith "_root_." then
              idents.modify (·.push (a, b, c.toString))
      if ti.stx.getKind == bundlingNotationKind then
        -- `↧x` ↦ `(FooCat.of _ … x)`, with the argument's own source text
        match rangeOf ti.stx, rangeOf ti.stx[1] with
        | some (a, b), some (xa, xb) =>
          let e ← (try ctx.runMetaM ti.lctx (instantiateMVars ti.expr) catch _ => pure ti.expr)
          if let .const ofName _ := e.getAppFn then
            let arity := match ctx.env.find? ofName with
              | some ci => explicitArity ci.type
              | none => 1
            let holes := String.join (List.replicate (arity - 1) "_ ")
            let arg := String.fromUTF8! (bs.extract xa xb)
            expansions.modify (·.push (a, b, s!"({ofName} {holes}{arg})"))
          else descend
        | _, _ => descend
      else if ti.isBinder || ti.expr.isFVar || keywordOrHole ti.stx bs then descend
      else
        let isPrf ← (try ctx.runMetaM ti.lctx (isProof ti.expr) catch _ => pure false)
        if isPrf then
          match rangeOf ti.stx with
          | some r =>
            if fields.contains r then descend
            else if ← needsElision ctx ti then
              let (ascribed, consts) := match ← proofTypeString ctx ti with
                | some (ty, cs) => (s!"(sorry : {ty})", cs)
                | none => ("sorry", #[])
              let termLocals ← (try ctx.runMetaM ti.lctx do
                  let e ← instantiateMVars ti.expr
                  let env ← getEnv
                  return e.getUsedConstants.filter (isLocalName env)
                catch _ => pure #[])
              let isTactic := ti.stx.getKind == ``Parser.Term.byTactic || ti.expr.isMVar
              let fvars ← (try ctx.runMetaM ti.lctx do
                  let e ← instantiateMVars ti.expr
                  return sectionFVars ti.lctx vars e
                catch _ => pure #[])
              proofs.modify (·.push ⟨extendDotPrefix bs r.1, r.2, ascribed, "sorry", consts, termLocals, isTactic, fvars⟩)
            else pure ()
          | none => descend
        else descend
    | some ctx, .ofTacticInfo ti =>
      if let some r := rangeOf ti.stx then
        let allProp ← (try ctx.runMetaM {} (do
            setMCtx ti.mctxBefore
            ti.goalsBefore.allM fun g => do isProp (← g.getType)) catch _ => pure false)
        tacs.modify (·.push ⟨r, allProp, ti.goalsBefore.length, ti.goalsBefore, ti.mctxAfter⟩)
        if (← rootCtx.get).isNone then rootCtx.set (some ctx)
      descend
    | _, _ => descend

/-- Prop-goal suffixes of tactic sequences: range, number of goals at the start, the goals, and
the metavariable context after the last tactic (to recover the section variables they used). -/
partial def tacticSuffixes (stx : Syntax) (tacs : Std.HashMap (Nat × Nat) TacInfo) :
    Array ((Nat × Nat) × Nat × List MVarId × MetavarContext) := Id.run do
  let mut out : Array ((Nat × Nat) × Nat × List MVarId × MetavarContext) := #[]
  let k := stx.getKind
  if k == ``Parser.Tactic.tacticSeq1Indented || k == ``Parser.Tactic.tacticSeqBracketed then
    let items := if k == ``Parser.Tactic.tacticSeq1Indented then stx[0].getSepArgs else stx[1].getSepArgs
    let infos := items.map fun it => (rangeOf it).bind fun r => tacs[r]?
    let mut j := items.size
    for i in (List.range items.size).reverse do
      match infos[i]! with
      | some ti => if ti.allProp && ti.goals > 0 then j := i else break
      | none => break
    if j < items.size then
      if let some (a, _) := rangeOf items[j]! then
        if let some (_, b) := rangeOf stx then
          let first := infos[j]!
          let last := infos[items.size - 1]!
          let goals := first.map (·.goals) |>.getD 1
          let gs := first.map (·.goalsBefore) |>.getD []
          let mctx := (last.map (·.mctxAfter)).getD {}
          out := out.push ((a, b), goals, gs, mctx)
      for i in [0:j] do
        out := out ++ tacticSuffixes items[i]! tacs
      return out
  for c in stx.getArgs do
    out := out ++ tacticSuffixes c tacs
  return out

/-- Names bound by a `variable` command. -/
def variableNames (stx : Syntax) : Array Name := Id.run do
  let mut out := #[]
  for b in stx[1].getArgs do
    let k := b.getKind
    if k == ``Parser.Term.explicitBinder || k == ``Parser.Term.implicitBinder ||
        k == ``Parser.Term.strictImplicitBinder then
      for x in b[1].getArgs do
        if x.isIdent then out := out.push x.getId
    else if k == ``Parser.Term.instBinder then
      if b[1].getNumArgs > 0 && b[1][0].isIdent then out := out.push b[1][0].getId
  return out

/-- Leading binder names of a type. -/
partial def leadingBinders (e : Expr) : Array Name :=
  match e with
  | .forallE n _ b _ => #[n] ++ leadingBinders b
  | _ => #[]

def isAuxName (n : Name) : Bool :=
  match n with
  | .str _ s => s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "_" ||
      s.startsWith "eq_" || s == "rec" || s == "casesOn" || s == "recOn" || s == "noConfusion" ||
      s == "noConfusionType" || s == "below" || s == "brecOn" || s == "mk" || s == "inj" ||
      s == "injEq" || s == "sizeOf_spec"
  | _ => false

/-- The innermost command of an `… in` chain. -/
partial def innermost (stx : Syntax) : Syntax :=
  if stx.getKind == ``Parser.Command.«in» then innermost stx[2] else stx

/-- Rewrite module-system syntax so the file elaborates as a plain (non-module) file. Byte ranges
reported by this helper refer to the rewritten text, which is returned in the output. -/
def stripModuleSyntax (s : String) : String :=
  let lines := s.splitOn "\n"
  let lines := lines.map fun l =>
    if l == "module" || l.startsWith "module " then ""
    else if l.startsWith "public meta import " then "import " ++ (l.drop 19)
    else if l.startsWith "public import " then "import " ++ (l.drop 14)
    else if l.startsWith "meta import " then "import " ++ (l.drop 12)
    else l
  let s := String.intercalate "\n" lines
  let s := s.replace "@[expose] public noncomputable section" "noncomputable section"
  let s := s.replace "@[expose] public section" "section"
  let s := s.replace "public noncomputable section" "noncomputable section"
  let s := s.replace "public section" "section"
  let s := s.replace "@[expose] public " ""
  let s := s.replace "@[expose, " "@["
  let s := s.replace ", expose]" "]"
  let s := s.replace "@[expose]" ""
  let s := s.replace "\npublic " "\n"
  s

/-- The context (namespace, `open`s, environment) a command was elaborated in. -/
partial def cmdContext : InfoTree → Option ContextInfo
  | .context pci t => match pci.mergeIntoOuter? none with
    | some ci => some ci
    | none => cmdContext t
  | .node _ cs => cs.toList.findSome? cmdContext
  | .hole _ => none

/-- Identifier tokens of a text, outside string literals; a dotted name is one token. -/
def identTokens (s : String) : Array String := Id.run do
  let cs := s.toList.toArray
  let mut out : Array String := #[]
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    if c == '"' then
      i := i + 1
      while i < cs.size && cs[i]! != '"' do
        if cs[i]! == '\\' then i := i + 1
        i := i + 1
      i := i + 1
    else if c == '.' && i + 1 < cs.size && cs[i+1]! == '{' then
      while i < cs.size && cs[i]! != '}' do i := i + 1
      i := i + 1
    else if isIdFirst c then
      let mut j := i + 1
      while j < cs.size && (isIdRest cs[j]! || (cs[j]! == '.' && j + 1 < cs.size && isIdFirst cs[j+1]!)) do
        j := j + 1
      out := out.push (String.mk (cs.extract i j).toList)
      i := j
    else i := i + 1
  return out

/-- The text after the first `=>` outside string literals. -/
def afterArrow (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    if c == '"' then
      i := i + 1
      while i < cs.size && cs[i]! != '"' do
        if cs[i]! == '\\' then i := i + 1
        i := i + 1
      i := i + 1
    else if c == '=' && i + 1 < cs.size && cs[i+1]! == '>' then
      return String.mk (cs.extract (i + 2) cs.size).toList
    else i := i + 1
  return ""

/-- For a notation-like command, the identifiers of its expansion that the repository resolves to
a unique global constant, with that constant's full name. With more of Mathlib imported a shorter
name can resolve elsewhere: the current namespace takes precedence over `open`. -/
def qualifications (ctx : ContextInfo) (text : String) : Array (String × String) := Id.run do
  let mut out : Array (String × String) := #[]
  for tok in identTokens (afterArrow text) do
    if tok.startsWith "_root_" then continue
    let cands := ResolveName.resolveGlobalName ctx.env ctx.options ctx.currNamespace ctx.openDecls tok.toName
    let names := ((cands.filter fun (n, fs) => fs.isEmpty && !isPrivateName n).map (·.1)).eraseDups
    match names with
    | [n] => if n.toString != tok && !out.any (·.1 == tok) then out := out.push (tok, n.toString)
    | _ => pure ()
  return out

def run (modName : Name) (path : System.FilePath) (out : System.FilePath) : IO UInt32 := do
  let input := stripModuleSyntax (← IO.FS.readFile path)
  let inputCtx := Parser.mkInputContext input path.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  -- plain-file elaboration can unfold more than module mode; be generous with heartbeats
  let opts : Options := maxHeartbeats.set (async.set {} false) 1000000
  let (env, messages) ← processHeaderCore 0 (HeaderSyntax.imports header) false
    opts messages inputCtx (trustLevel := 1024) (mainModule := modName)
  for m in messages.toList do
    IO.eprintln s!"header message for {modName}: {← m.data.toString}"
  IO.eprintln s!"{modName}: imported {env.header.moduleNames.size} modules"
  let env := env.setMainModule modName
  let cmdState := { Command.mkState env messages opts with infoState := { enabled := true } }
  let s ← IO.processCommands inputCtx parserState cmdState
  let mut nErr := 0
  for m in s.commandState.messages.toList do
    if m.severity == .error then
      nErr := nErr + 1
      IO.eprintln s!"error in {modName}: {← m.data.toString}"
  let mut treeAt : Std.HashMap Nat InfoTree := {}
  for t in s.commandState.infoState.trees.toArray do
    if let some p := treeCmdPos t then treeAt := treeAt.insert p t
  -- declaration ranges of the constants this module declares, to find what each command declares
  let env := s.commandState.env
  let mut declStarts : Array (Name × Nat) := #[]
  for (n, _) in env.constants.map₂.toList do
    if let some r := declRangeExt.find? env n then
      declStarts := declStarts.push (n, r.range.pos.line)
  let fileMap := FileMap.ofString input
  let mut cmdsJson : Array Json := #[]
  let mut vars : Array Name := #[]
  let mut scopeStack : Array (Array Name) := #[]
  for cmd in s.commands do
    let some (cs, ce) := rangeOf cmd | continue
    let inner := innermost cmd
    let mut reps : Array Json := #[]
    let idents ← IO.mkRef (#[] : Array (Nat × Nat × String))
    let isDecl := inner.getKind == ``Parser.Command.declaration
    let dk := if isDecl then toString inner[1].getKind else ""
    -- section-variable bookkeeping
    if inner.getKind == ``Parser.Command.«variable» then vars := vars ++ variableNames inner
    else if inner.getKind == ``Parser.Command.«section» || inner.getKind == ``Parser.Command.«namespace» then
      scopeStack := scopeStack.push vars
    else if inner.getKind == ``Parser.Command.«end» then
      if let some v := scopeStack.back? then
        vars := v
        scopeStack := scopeStack.pop
    -- the section variables the original signature included, to be forced by `include`
    let mut inc := ""
    if isDecl then
      let l0 := (fileMap.toPosition ⟨cs⟩).line
      let l1 := (fileMap.toPosition ⟨ce⟩).line
      let mut included : Array Name := #[]
      for (n, line) in declStarts do
        if l0 ≤ line && line ≤ l1 && !isAuxName n then
          if let some ci := env.find? n then
            for b in leadingBinders ci.type do
              if vars.contains b then
                if !included.contains b then included := included.push b
              else if b.hasMacroScopes then
                -- an anonymous instance binder from `variable`; section variables may follow
                continue
              else break
      if !included.isEmpty then
        inc := "include " ++ " ".intercalate (included.toList.map toString) ++ " in\n"
    if isDecl then
      if let some t := treeAt[cs]? then
        let proofs ← IO.mkRef (#[] : Array Rep)
        let tacs ← IO.mkRef (#[] : Array TacInfo)
        let rootCtx ← IO.mkRef (none : Option ContextInfo)
        let expansions ← IO.mkRef (#[] : Array (Nat × Nat × String))
        collect none t (fieldRanges cmd {}) input.toUTF8 vars rootCtx proofs tacs expansions idents
        for (a, b, txt) in ← expansions.get do
          -- reported like a replacement, but one the generator must always apply
          reps := reps.push (Json.arr #[a, b, txt, txt, Json.arr #[], Json.arr #[], Json.bool true, Json.arr #[], Json.bool true])
        let tacMap : Std.HashMap (Nat × Nat) TacInfo :=
          (← tacs.get).foldl (fun m ti => m.insert ti.range ti) {}
        for rp in ← proofs.get do
          let original := String.fromUTF8! (input.toUTF8.extract rp.a rp.b)
          let fix (t : String) := if original.startsWith "where" then ":= " ++ t else t
          reps := reps.push (Json.arr #[rp.a, rp.b, fix rp.ascribed, fix rp.bare,
            Json.arr (rp.consts.map (Json.str ·.toString)),
            Json.arr (rp.termLocals.map (Json.str ·.toString)), Json.bool rp.isTactic,
            Json.arr (rp.fvars.map Json.str)])
        for ((a, b), goals, gs, mctx) in tacticSuffixes cmd tacMap do
          let t := if goals ≤ 1 then "sorry" else "all_goals sorry"
          -- section variables used by the elided tactics: free variables of the goals' proofs
          let fvars ← match ← rootCtx.get with
            | some ctx => (try ctx.runMetaM {} do
                setMCtx mctx
                let mut acc : Array String := #[]
                for g in gs do
                  let e ← instantiateMVars (mkMVar g)
                  let lctx := (← g.getDecl).lctx
                  for n in sectionFVars lctx vars e do
                    if !acc.contains n then acc := acc.push n
                return acc
              catch _ => pure #[])
            | none => pure #[]
          reps := reps.push (Json.arr #[a, b, t, t, Json.arr #[], Json.arr #[], Json.bool true,
            Json.arr (fvars.map Json.str)])
    else if let some t := treeAt[cs]? then
      -- a non-declaration command (`variable` binders, …) only needs its `↧` uses expanded
      let proofs ← IO.mkRef (#[] : Array Rep)
      let tacs ← IO.mkRef (#[] : Array TacInfo)
      let rootCtx ← IO.mkRef (none : Option ContextInfo)
      let expansions ← IO.mkRef (#[] : Array (Nat × Nat × String))
      collect none t (fieldRanges cmd {}) input.toUTF8 vars rootCtx proofs tacs expansions idents
      for (a, b, txt) in ← expansions.get do
        reps := reps.push (Json.arr #[a, b, txt, txt, Json.arr #[], Json.arr #[], Json.bool true, Json.arr #[], Json.bool true])
    let nsName := if inner.getKind == ``Parser.Command.«namespace» then inner[1].getId.toString else ""
    let identsJson : Array Json := (← idents.get).map fun (a, b, c) => Json.arr #[a, b, c]
    let mut quals : Array Json := #[]
    let kindStr := toString inner.getKind
    if (kindStr.splitOn "notation").length > 1 || (kindStr.splitOn "macro").length > 1 ||
        (kindStr.splitOn "mixfix").length > 1 then
      if let some t := treeAt[cs]? then
        if let some ctx := cmdContext t then
          for (tok, full) in qualifications ctx (String.fromUTF8! (input.toUTF8.extract cs ce)) do
            quals := quals.push (Json.arr #[tok, full])
    cmdsJson := cmdsJson.push <| Json.mkObj [
      ("s", cs), ("e", ce), ("kind", toString cmd.getKind), ("ik", toString inner.getKind),
      ("dk", dk), ("ns", nsName), ("inc", inc), ("reps", Json.arr reps),
      ("quals", Json.arr quals), ("idents", Json.arr identsJson)]
  let imports := (HeaderSyntax.imports header).map (fun i => Json.str i.module.toString)
  let j := Json.mkObj [("module", modName.toString), ("errors", nErr),
    ("imports", Json.arr imports), ("source", input), ("commands", Json.arr cmdsJson)]
  IO.FS.writeFile out j.compress
  return 0

end ElabInfo

unsafe def main (args : List String) : IO UInt32 := do
  -- the outer frontend disables initializer execution after its own imports; the nested import
  -- of Mathlib needs it for `initialize` declarations
  enableInitializersExecution
  match args with
  | [m, path, out] => ElabInfo.run m.toName path out
  | _ => do IO.eprintln "usage: ElabInfo <module> <path> <out.json>"; return 1

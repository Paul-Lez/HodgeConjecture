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
import ImportGraph.Graph.Filter
import ImportGraph.Lean.Environment

/-!
# The blueprint dependency graph of the statement

This script generates `blueprint/src/generated.tex`, the body of the
[leanblueprint](https://github.com/PatrickMassot/leanblueprint) document whose dependency graph
shows what the statement of the conjecture is made of. Run it, after `lake build HodgeConjecture`,
with

```
lake env lean --run scripts/BlueprintGraph.lean
```

The nodes are `HodgeConjecture` itself and every definition (structure, class, inductive type,
`def` or `abbrev`) of the `HodgeConjecture` library that it transitively uses. Lemmas, instances and
auxiliary declarations are not nodes, but the edges are computed *through* them: a node uses
another when the second occurs in the type or body of the first, possibly via such intermediate
declarations. Mathlib is the boundary; nothing outside the `HodgeConjecture` library is shown.

The edge set is then transitively reduced with `importGraph`'s `NameMap.transitiveReduction`,
which drops the edges implied by a longer path. That is what the rendered graph displays anyway,
and it removes about four fifths of them, so the generated file stays readable in a diff.

Each node is a `definition` environment (a `conjecture` for the statement) carrying `\lean`,
`\leanok` and `\uses`, whose text is the docstring of the declaration followed by a link to its
source. Chapters follow the folders of the library and sections its modules, in import order, with
the module docstring as introduction.
-/

open Lean Meta

namespace BlueprintGraph

/-- The root library: modules outside it are the boundary of the graph. -/
def libraryName : Name := `HodgeConjecture

/-- The declaration whose transitive dependencies form the graph. -/
def rootDecl : Name := `HodgeConjecture

/-- Where the source links point. -/
def sourceBase : String := "https://github.com/Paul-Lez/HodgeConjecture/blob/main/"

/-- The output, relative to the project root. -/
def outputPath : System.FilePath := "blueprint" / "src" / "generated.tex"

/-- A node of the graph, ready to be printed. -/
structure Node where
  name : Name
  module : Name
  line : Nat
  kind : String
  doc : Option String
  uses : Array Name
  deriving Inhabited

/-! ### Escaping -/

/-- Escape a piece of text for LaTeX. Unicode is left alone: the web version is HTML and the
print version uses `unicode-math`. -/
def escapeTeX (s : String) : String := Id.run do
  let mut out := ""
  for c in s.toList do
    out := out ++ match c with
      | '\\' => "\\textbackslash{}"
      | '{' => "\\{"
      | '}' => "\\}"
      | '$' => "\\$"
      | '&' => "\\&"
      | '#' => "\\#"
      | '%' => "\\%"
      | '_' => "\\_"
      | '^' => "\\^{}"
      | '~' => "\\textasciitilde{}"
      | '<' => "\\textless{}"
      | '>' => "\\textgreater{}"
      | '|' => "\\textbar{}"
      | c => c.toString
  return out

/-- Render the inline markdown of one line of docstring: code spans become `\texttt`, `**bold**`
becomes `\textbf`, `[text](url)` becomes `\href`, and everything else is escaped. -/
partial def renderInline (s : String) : String := Id.run do
  let mut out := ""
  let mut rest := s
  while !rest.isEmpty do
    if rest.startsWith "`" then
      let body := (rest.drop 1).toString
      match body.splitOn "`" with
      | code :: after :: more =>
        out := out ++ "\\texttt{" ++ escapeTeX code ++ "}"
        rest := "`".intercalate (after :: more)
      | _ => out := out ++ escapeTeX rest; rest := ""
    else if rest.startsWith "**" then
      let body := (rest.drop 2).toString
      match body.splitOn "**" with
      | bold :: after :: more =>
        out := out ++ "\\textbf{" ++ renderInline bold ++ "}"
        rest := "**".intercalate (after :: more)
      | _ => out := out ++ escapeTeX rest; rest := ""
    else if rest.startsWith "[" then
      -- A markdown link `[text](url)`, if the brackets close and are followed by a URL.
      let body := (rest.drop 1).toString
      match body.splitOn "](" with
      | text :: after :: more =>
        let after := (")".intercalate (after :: more)).dropWhile (· == '<') |>.toString
        match after.splitOn ")" with
        | url :: tail :: tailMore =>
          if !text.contains ']' && url.startsWith "http" then
            out := out ++ "\\href{" ++ (url.takeWhile (· != '>')).toString ++ "}{" ++ renderInline text ++ "}"
            rest := ")".intercalate (tail :: tailMore)
          else
            out := out ++ "["; rest := body
        | _ => out := out ++ "["; rest := body
      | _ => out := out ++ "["; rest := body
    else
      let chunk := (rest.takeWhile fun c => c != '`' && c != '*' && c != '[').toString
      let chunk := if chunk.isEmpty then (rest.take 1).toString else chunk
      out := out ++ escapeTeX chunk
      rest := (rest.drop chunk.length).toString
  return out

/-- Render a docstring: fenced code blocks become `verbatim`, `## headings` become paragraphs,
bullet lists become `itemize`, and the rest goes through `renderInline`. -/
def renderDoc (doc : String) : String := Id.run do
  let parts := doc.splitOn "```"
  let mut out := ""
  let mut inCode := false
  for part in parts do
    if inCode then
      -- Drop an optional language tag on the first line.
      let body := match part.splitOn "\n" with
        | [] => ""
        | first :: rest =>
          if first.trimAscii.toString.all Char.isAlphanum then "\n".intercalate rest else part
      out := out ++ "\\begin{verbatim}\n" ++ body.trimAsciiEnd.toString ++ "\n\\end{verbatim}\n"
    else
      out := out ++ renderText part
    inCode := !inCode
  return out
where
  renderText (s : String) : String := Id.run do
    let mut out := ""
    let mut inList := false
    for line in s.splitOn "\n" do
      let stripped := line.trimAscii.toString
      let isBullet := stripped.startsWith "* " || stripped.startsWith "- "
      if inList && !isBullet && !stripped.isEmpty && line.startsWith " " then
        -- A continuation line of the current item.
        out := out ++ renderInline stripped ++ "\n"
        continue
      if inList && !isBullet then
        out := out ++ "\\end{itemize}\n"
        inList := false
      if isBullet then
        unless inList do
          out := out ++ "\\begin{itemize}\n"
          inList := true
        out := out ++ "\\item " ++ renderInline (stripped.drop 2).toString ++ "\n"
      else if stripped.startsWith "#" then
        let title := (stripped.dropWhile (· == '#')).trimAscii.toString
        out := out ++ "\\paragraph{" ++ renderInline title ++ "}\n"
      else
        out := out ++ renderInline line ++ "\n"
    if inList then out := out ++ "\\end{itemize}\n"
    return out

/-- Turn a module name into the path of its source file. -/
def modulePath (m : Name) : String :=
  "/".intercalate (m.components.map (·.toString)) ++ ".lean"

/-- The chapter a module belongs to: `Statement` for the statement, otherwise the first one or two
folders below the library root, e.g. `Definitions.AlgebraicGeometry`. -/
def chapterKey (m : Name) : String :=
  match m.components.drop 1 with
  | [] => libraryName.toString
  | [single] => single.toString
  | folder :: sub :: _ :: _ => s!"{folder}.{sub}"
  | folder :: _ => folder.toString

/-- Chapters in reading order: the statement, then the folders in the order of the README. -/
def chapterRank (key : String) : Nat × String :=
  if key == "Statement" then (0, key)
  else if key.startsWith "Definitions" then (1, key)
  else if key.startsWith "Lemmas" then (2, key)
  else if key.startsWith "Mathlib" then (3, key)
  else (4, key)

/-- The human title of a chapter. -/
def chapterTitle (key : String) : String :=
  if key == "Statement" then "The statement"
  else match key.splitOn "." with
    | [folder, sub] => s!"{folder}: {sub}"
    | _ => key

/-! ### Selecting the nodes -/

/-- Last components of automatically generated declarations that are neither caught by
`Name.isInternalDetail` nor registered as auxiliary recursors. -/
def generatedSuffixes : List String :=
  ["noConfusionType", "noConfusion", "below", "ibelow", "brecOn", "binductionOn", "sizeOf",
    "ctorIdx", "toCtorIdx", "ofNat", "ctorElim", "ctorElimType"]

/-- Is `n` a definition worth a node? Only genuine definitions and types qualify; theorems,
instances, constructors, recursors, projections and compiler-generated helpers are walked through
but not displayed. -/
def isNodeCandidate (env : Environment) (n : Name) : CoreM Bool := do
  let some info := env.find? n | return false
  let structural := match info with
    | .defnInfo _ | .inductInfo _ => true
    | _ => false
  if !structural then return false
  if n.isInternalDetail || isAuxRecursor env n || isNoConfusion env n || isRecCore env n
      || isCasesOnRecursor env n || isMatcherCore env n || env.isProjectionFn n then
    return false
  if generatedSuffixes.contains n.getString! then return false
  -- `isInstance` misses instances whose attribute lives in a private scope, hence the name check.
  if (← isInstance n) || n.getString!.startsWith "inst" then return false
  return true

/-- The display kind of a node. -/
def nodeKind (env : Environment) (n : Name) : CoreM String := do
  match env.find? n with
  | some (.inductInfo _) =>
    return if isClass env n then "class" else if isStructure env n then "structure" else "inductive"
  | _ =>
    return if (← getReducibilityStatus n) matches .reducible then "abbrev" else "def"

/-- Is the constant part of the library (as opposed to Mathlib, core, or the other dependencies)?
`getModuleFor?` is `importGraph`'s. -/
def inLibrary (env : Environment) (n : Name) : Bool :=
  match env.getModuleFor? n with
  | some m => libraryName.isPrefixOf m
  | none => false

/-- The constants used by a declaration, restricted to the library. -/
def libraryUses (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | some info => info.getUsedConstantsAsSet.toArray.filter (inLibrary env ·)
  | none => #[]

/-- Every library constant reachable from the root through uses. -/
def reachable (env : Environment) : NameSet := Id.run do
  let mut seen : NameSet := NameSet.empty.insert rootDecl
  let mut stack : Array Name := #[rootDecl]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    for d in libraryUses env n do
      unless seen.contains d do
        seen := seen.insert d
        stack := stack.push d
  return seen

/-- The nodes reachable from the *direct* uses of a constant, walking through non-node library
constants. Memoised; a constant currently being explored counts as having no dependencies, which
cuts the trivial cycles through constructors and recursors. -/
partial def nodeUses (env : Environment) (isNode : Name → Bool) (n : Name) :
    StateRefT (Std.HashMap Name NameSet) IO NameSet := do
  if let some r := (← get).get? n then return r
  modify (·.insert n {})
  let mut acc : NameSet := {}
  for d in libraryUses env n do
    if d == n then continue
    if isNode d then acc := acc.insert d
    else
      for x in (← nodeUses env isNode d).toArray do acc := acc.insert x
  modify (·.insert n acc)
  return acc

/-! ### Output -/

/-- The label of a node. -/
def labelOf (n : Name) : String :=
  (if n == rootDecl then "conj:" else "def:") ++ n.toString

/-- Render one node. -/
def renderNode (node : Node) : String := Id.run do
  let env := if node.name == rootDecl then "conjecture" else "definition"
  let title := if node.name == rootDecl then "Hodge conjecture" else escapeTeX node.name.toString
  let path := modulePath node.module
  let mut out := s!"\\begin\{{env}}[{title}]\\label\{{labelOf node.name}}\n"
  out := out ++ s!"\\lean\{{node.name}}\\leanok\n"
  unless node.uses.isEmpty do
    out := out ++ "\\uses{" ++ ", ".intercalate (node.uses.toList.map labelOf) ++ "}\n"
  match node.doc with
  | some doc => out := out ++ (renderDoc doc).trimAscii.toString ++ "\n\n"
  | none => pure ()
  out := out ++ s!"\\noindent\\emph\{Lean:} \\texttt\{{node.kind} {escapeTeX node.name.toString}}, \
    \\href\{{sourceBase}{path}#L{node.line}}\{\\texttt\{{escapeTeX path}:{node.line}}}.\n"
  out := out ++ s!"\\end\{{env}}\n\n"
  return out

/-- Split a module docstring into an optional `# Title` and the rest. -/
def splitModuleDoc (doc : String) : Option String × String :=
  match doc.trimAscii.toString.splitOn "\n" with
  | first :: rest =>
    if first.startsWith "# " then (some (first.drop 2).trimAscii.toString, "\n".intercalate rest)
    else (none, doc)
  | [] => (none, doc)

/-- Render the section of one module. -/
def renderModule (env : Environment) (m : Name) (nodes : Array Node) : String := Id.run do
  let path := modulePath m
  let (title, intro) := match getModuleDoc? env m with
    | some docs => if h : 0 < docs.size then splitModuleDoc docs[0].doc else (none, "")
    | none => (none, "")
  let title := escapeTeX (title.getD m.getString!)
  let mut out := s!"\\section\{{title}}\\label\{sec:{m}}\n"
  out := out ++ s!"\\noindent\\emph\{File:} \\href\{{sourceBase}{path}}\{\\texttt\{{escapeTeX path}}}.\n\n"
  unless intro.trimAscii.toString.isEmpty do
    out := out ++ (renderDoc intro).trimAscii.toString ++ "\n\n"
  for node in nodes do
    out := out ++ renderNode node
  return out

unsafe def main (_args : List String) : IO Unit := do
  Lean.enableInitializersExecution
  initSearchPath (← findSysroot)
  -- Import every module of the library with its private scope, so that the bodies of
  -- non-exposed definitions are visible.
  let root : System.FilePath := libraryName.toString
  let files ← root.walkDir
  let modules := files.filterMap fun f =>
    if f.extension == some "lean" then
      let parts := f.withExtension "" |>.components
      some (parts.foldl (fun n s => n.str s) Name.anonymous)
    else none
  let modules := modules.push libraryName
  IO.println s!"Importing {modules.size} modules of {libraryName}..."
  let env ← importModules (loadExts := true)
    (modules.map fun m => { module := m, importAll := true }) {}
  IO.println s!"Environment loaded with {env.header.moduleNames.size} modules."
  let reached := reachable env
  IO.println s!"{reached.size} constants of the library are reachable from {rootDecl}."
  let ctx : Core.Context := { fileName := "<BlueprintGraph>", fileMap := default }
  let (nodes, _) ← (do
    let mut nodeNames : NameSet := {}
    for n in reached.toArray do
      if n == rootDecl || (← isNodeCandidate env n) then nodeNames := nodeNames.insert n
    let isNode := fun n => nodeNames.contains n
    let collect : StateRefT (Std.HashMap Name NameSet) IO (Array (Name × NameSet)) :=
      nodeNames.toArray.mapM fun n => do
        let s ← nodeUses env isNode n
        return (n, s)
    let (usesOf, _) ← collect.run {}
    -- The contracted graph, in the `NameMap (Array Name)` shape `importGraph` works with. A
    -- structure reaches itself through its constructor, so drop the self-loops first: they are
    -- meaningless as dependencies, and plasTeX recurses forever on them.
    let graph : NameMap (Array Name) := usesOf.foldl (init := {}) fun g (n, used) =>
      g.insert n (used.erase n).toArray
    let graph := graph.transitiveReduction
    let mut nodes : Array Node := #[]
    for n in nodeNames.toArray do
      let some m := env.getModuleFor? n | continue
      let line := match ← findDeclarationRanges? n with
        | some r => r.range.pos.line
        | none => 1
      let doc ← findDocString? env n
      let uses := (graph.find? n |>.getD #[]).qsort (·.toString < ·.toString)
      nodes := nodes.push { name := n, module := m, line, kind := ← nodeKind env n, doc, uses }
    return nodes : CoreM (Array Node)).toIO ctx { env }
  IO.println s!"{nodes.size} nodes, {nodes.foldl (· + ·.uses.size) 0} edges after reduction."
  -- Group by module, modules in import order, chapters by folder.
  let moduleOrder : Std.HashMap Name Nat :=
    Std.HashMap.ofList (env.header.moduleNames.toList.zipIdx)
  let byModule : Std.HashMap Name (Array Node) := nodes.foldl (init := {}) fun acc node =>
    acc.alter node.module fun
      | some arr => some (arr.push node)
      | none => some #[node]
  let modules := byModule.keys.toArray.qsort fun a b =>
    moduleOrder.getD a 0 < moduleOrder.getD b 0
  let chapters := (modules.map chapterKey).toList.eraseDups.toArray.qsort fun a b =>
    let (ra, ka) := chapterRank a
    let (rb, kb) := chapterRank b
    ra < rb || (ra == rb && ka < kb)
  let mut out := "% Generated by `lake env lean --run scripts/BlueprintGraph.lean`; do not edit.\n\n"
  for chapter in chapters do
    out := out ++ s!"\\chapter\{{escapeTeX (chapterTitle chapter)}}\n\n"
    for m in modules do
      if chapterKey m == chapter then
        let nodes := (byModule.getD m #[]).qsort (·.line < ·.line)
        out := out ++ renderModule env m nodes
  IO.FS.createDirAll outputPath.parent.get!
  IO.FS.writeFile outputPath out
  IO.println s!"Wrote {outputPath}."

end BlueprintGraph

unsafe def main := BlueprintGraph.main

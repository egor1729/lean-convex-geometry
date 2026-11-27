module

public import Lean

/-!
# Environment-Wide Axiom & Module Audit (`convexgeom-audit`)

Checks every declaration (public and private, in every namespace) in modules under a root module
(default `ConvexGeom`, excluding `ConvexGeom.Verification`):

1. Module completeness (`--check-dir`): every `.lean` file outside `Verification/` is imported by
   the root module.
2. No project-defined `axiom` declarations (even unused or private).
3. Transitive axiom check at `OLeanLevel.private` (without executing initializers), rejecting any
   axiom outside `{propext, Classical.choice, Quot.sound}`.
4. Optional JSON output (`--json <path>`), exiting nonzero on any violation.
-/

open Lean

namespace ConvexGeomAudit

private def allowedAxioms : NameSet :=
  NameSet.empty
    |>.insert ``propext
    |>.insert ``Classical.choice
    |>.insert ``Quot.sound

private def parseModuleName (s : String) : Name :=
  s.splitOn "." |>.foldl (init := Name.anonymous) fun acc part =>
    if part.isEmpty then acc else Name.mkStr acc part

private def isExcludedVerificationMod (rootMod modName : Name) : Bool :=
  let verifMod := Name.mkStr rootMod "Verification"
  modName == verifMod || verifMod.isPrefixOf modName

private def isProjectModule (rootMod modName : Name) : Bool :=
  (modName == rootMod || rootMod.isPrefixOf modName) &&
    !isExcludedVerificationMod rootMod modName

private def pathToModuleName (path : System.FilePath) : Name :=
  let stripped := path.withExtension ""
  let parts := stripped.components.filter fun p => p != "." && p != "/" && !p.isEmpty
  parts.foldl (init := Name.anonymous) fun acc part => Name.mkStr acc part

private partial def collectLeanFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out : Array System.FilePath := #[]
  if !(← dir.pathExists) then
    return out
  for entry in (← dir.readDir) do
    let name := entry.fileName
    if name == "Verification" then
      continue
    let path := entry.path
    if ← path.isDir then
      out := out ++ (← collectLeanFiles path)
    else if path.extension == some "lean" then
      out := out.push path
  return out

private structure KindCounts where
  axioms : Nat := 0
  theorems : Nat := 0
  definitions : Nat := 0
  opaques : Nat := 0
  inductives : Nat := 0
  constructors : Nat := 0
  recursors : Nat := 0
  quotients : Nat := 0

private def KindCounts.total (c : KindCounts) : Nat :=
  c.axioms + c.theorems + c.definitions + c.opaques +
    c.inductives + c.constructors + c.recursors + c.quotients

private def KindCounts.bump (c : KindCounts) : ConstantInfo → KindCounts
  | .axiomInfo _  => { c with axioms := c.axioms + 1 }
  | .thmInfo _    => { c with theorems := c.theorems + 1 }
  | .defnInfo _   => { c with definitions := c.definitions + 1 }
  | .opaqueInfo _ => { c with opaques := c.opaques + 1 }
  | .inductInfo _ => { c with inductives := c.inductives + 1 }
  | .ctorInfo _   => { c with constructors := c.constructors + 1 }
  | .recInfo _    => { c with recursors := c.recursors + 1 }
  | .quotInfo _   => { c with quotients := c.quotients + 1 }

private structure CollectState where
  seen   : NameMap (Array Name) := {}
  axioms : NameSet := {}

private abbrev CollectM := ReaderT Environment (StateM CollectState)

private def insertArray (s : NameSet) (axs : Array Name) : NameSet :=
  axs.foldl (init := s) fun acc ax => acc.insert ax

/-- Shared-cache kernel axiom collector mirroring `Lean.CollectAxioms.collect`, operating directly
on the full private environment without loading environment extensions or running initializers. -/
private partial def collectConst (c : Name) : CollectM Unit := do
  let s ← get
  if let some axs := s.seen.find? c then
    modify fun st => { st with axioms := insertArray st.axioms axs }
    return
  let env ← read
  let savedAxioms := s.axioms
  modify fun st => { st with axioms := {}, seen := st.seen.insert c #[] }
  let collectExpr (e : Expr) : CollectM Unit := e.getUsedConstants.forM collectConst
  match env.checked.get.find? c with
  | some (.axiomInfo v)  =>
      modify fun st => { st with axioms := st.axioms.insert c }
      collectExpr v.type
  | some (.defnInfo v)   => collectExpr v.type *> collectExpr v.value
  | some (.thmInfo v)    => collectExpr v.type *> collectExpr v.value
  | some (.opaqueInfo v) => collectExpr v.type *> collectExpr v.value
  | some (.quotInfo _)   => pure ()
  | some (.ctorInfo v)   => collectExpr v.type
  | some (.recInfo v)    => collectExpr v.type
  | some (.inductInfo v) => collectExpr v.type *> v.ctors.forM collectConst
  | none                 => pure ()
  let collected := (← get).axioms
  let result := collected.toArray.qsort Name.lt
  modify fun st => {
    seen   := st.seen.insert c result
    axioms := insertArray savedAxioms result
  }

private def collectAndGet (c : Name) : CollectM (Array Name) := do
  collectConst c
  return (← get).seen.find? c |>.getD #[]

private structure Config where
  rootMod : Name := `ConvexGeom
  checkDir? : Option System.FilePath := some (System.FilePath.mk "ConvexGeom")
  jsonOut? : Option System.FilePath := none

private def parseArgs (args : List String) : IO Config := do
  let mut cfg : Config := {}
  let mut explicitCheckDir := false
  let mut noCheckDir := false
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--module" :: m :: tl =>
      cfg := { cfg with rootMod := parseModuleName m }
      rest := tl
    | "--check-dir" :: d :: tl =>
      cfg := { cfg with checkDir? := some (System.FilePath.mk d) }
      explicitCheckDir := true
      rest := tl
    | "--no-check-dir" :: tl =>
      cfg := { cfg with checkDir? := none }
      noCheckDir := true
      rest := tl
    | "--json" :: p :: tl =>
      cfg := { cfg with jsonOut? := some (System.FilePath.mk p) }
      rest := tl
    | "--help" :: _ | "-h" :: _ =>
      IO.println "Usage: convexgeom-audit [--module <Name>] [--check-dir <Dir> | --no-check-dir] [--json <Path>]"
      IO.Process.exit 0
    | flag :: _ =>
      throw <| IO.userError s!"Unknown or incomplete argument: {flag}"
    | [] => break
  if !explicitCheckDir && !noCheckDir && cfg.rootMod != `ConvexGeom then
    cfg := { cfg with checkDir? := none }
  return cfg

private def jsonEscape (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '"'  => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t"
    | _    => acc.push c

private def jsonString (s : String) : String :=
  "\"" ++ jsonEscape s ++ "\""

private def jsonStringArray (xs : Array String) : String :=
  "[" ++ String.intercalate ", " (xs.toList.map jsonString) ++ "]"

private def formatJsonReport
    (rootMod : Name)
    (projectMods : Array Name)
    (counts : KindCounts)
    (observedAxioms : Array Name)
    (violations : Array String) : String :=
  let lines : List String := [
    "{",
    s!"  \"leanVersion\": {jsonString Lean.versionString},",
    s!"  \"rootModule\": {jsonString rootMod.toString},",
    s!"  \"passed\": {if violations.isEmpty then "true" else "false"},",
    s!"  \"moduleCount\": {projectMods.size},",
    s!"  \"modules\": {jsonStringArray (projectMods.map Name.toString)},",
    s!"  \"totalDeclarations\": {counts.total},",
    "  \"countsByKind\": {",
    s!"    \"axioms\": {counts.axioms},",
    s!"    \"theorems\": {counts.theorems},",
    s!"    \"definitions\": {counts.definitions},",
    s!"    \"opaques\": {counts.opaques},",
    s!"    \"inductives\": {counts.inductives},",
    s!"    \"constructors\": {counts.constructors},",
    s!"    \"recursors\": {counts.recursors},",
    s!"    \"quotients\": {counts.quotients}",
    "  },",
    s!"  \"observedAxioms\": {jsonStringArray (observedAxioms.map Name.toString)},",
    s!"  \"violations\": {jsonStringArray violations}",
    "}"
  ]
  String.intercalate "\n" lines ++ "\n"

end ConvexGeomAudit

open ConvexGeomAudit in
public def main (args : List String) : IO UInt32 := do
  let cfg ← parseArgs args
  Lean.initSearchPath (← Lean.findSysroot)
  -- Load the full transitive environment at `.private` level (all public + private constants,
  -- without running module initializers).
  let env ← Lean.importModules #[{ module := cfg.rootMod, importAll := true }] {}
    (loadExts := false) (level := .private)
  let privateEnv := env.setExporting false
  let mut projectMods : Array Name := #[]
  for modName in env.header.moduleNames do
    if isProjectModule cfg.rootMod modName then
      projectMods := projectMods.push modName
  projectMods := projectMods.qsort Name.lt
  let mut violations : Array String := #[]
  if projectMods.isEmpty then
    violations := violations.push
      s!"No project modules matched root module '{cfg.rootMod}'."
  -- Verify filesystem completeness against the loaded module graph when `--check-dir` is active.
  if let some dir := cfg.checkDir? then
    let mut fsFiles ← collectLeanFiles dir
    let rootFile := System.FilePath.mk (dir.toString ++ ".lean")
    if ← rootFile.pathExists then
      fsFiles := fsFiles.push rootFile
    let loadedSet : NameSet := projectMods.foldl (init := {}) NameSet.insert
    let expectedMods := (fsFiles.map pathToModuleName).qsort Name.lt
    for expected in expectedMods do
      if !loadedSet.contains expected then
        violations := violations.push
          s!"Filesystem module '{expected}' is not transitively imported by '{cfg.rootMod}'."
  -- Collect every project-owned constant (public and private, in every namespace).
  let mut decls : Array (Name × Name × ConstantInfo) := #[]
  for (name, info) in privateEnv.constants.map₁.toList do
    if let some modIdx := privateEnv.getModuleIdxFor? name then
      if h : modIdx.toNat < privateEnv.header.moduleNames.size then
        let modName := privateEnv.header.moduleNames[modIdx.toNat]
        if isProjectModule cfg.rootMod modName then
          decls := decls.push (name, modName, info)
  decls := decls.qsort fun a b => Name.lt a.1 b.1
  -- Walk the kernel dependency graph with a shared cache across all project declarations.
  let collectAll : CollectM (Array (Name × Name × ConstantInfo × Array Name)) :=
    decls.mapM fun (name, modName, info) => do
      let axs ← collectAndGet name
      return (name, modName, info, axs)
  let results : Array (Name × Name × ConstantInfo × Array Name) :=
    (collectAll.run privateEnv).run' {}
  let mut counts : KindCounts := {}
  let mut observedAxioms : NameSet := {}
  for (name, modName, info, axs) in results do
    counts := counts.bump info
    if info matches .axiomInfo _ then
      violations := violations.push
        s!"Project-defined axiom '{name}' in module '{modName}'."
    for ax in axs do
      observedAxioms := observedAxioms.insert ax
      if !allowedAxioms.contains ax then
        violations := violations.push
          s!"Disallowed axiom '{ax}' used by '{name}' (in module '{modName}')."
  let observedSorted := observedAxioms.toArray.qsort Name.lt
  IO.println s!"convexgeom-audit (Lean {Lean.versionString})"
  IO.println s!"  Root module        : {cfg.rootMod}"
  IO.println s!"  Audited modules    : {projectMods.size}"
  IO.println s!"  Total declarations : {counts.total} (theorems: {counts.theorems}, defs: {counts.definitions}, opaques: {counts.opaques}, axioms: {counts.axioms}, inductives: {counts.inductives}, ctors: {counts.constructors}, recs: {counts.recursors}, quots: {counts.quotients})"
  IO.println s!"  Observed axioms    : {observedSorted.map Name.toString}"
  if let some jsonPath := cfg.jsonOut? then
    let report := formatJsonReport cfg.rootMod projectMods counts observedSorted violations
    IO.FS.writeFile jsonPath report
    IO.println s!"  JSON report        : {jsonPath}"
  if violations.isEmpty then
    IO.println "AUDIT PASSED: zero violations."
    return 0
  else
    IO.eprintln s!"AUDIT FAILED with {violations.size} violation(s):"
    for v in violations do
      IO.eprintln s!"  - {v}"
    return 1

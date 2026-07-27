import Lean.Meta.ExprLens
import ProofWidgets.Component.Basic
import ProofWidgets.Data.Html
import ProofWidgets.Component.OfRpcMethod
import ProofWidgets.Component.MakeEditLink
import ProofWidgets.Component.Panel.Basic
import ProofWidgets.Component.Panel.SelectionPanel
import ProofWidgets.Presentation.Expr

import FormalRamsey.G6
import GraphMaker.GraphTypes

open ProofWidgets
open Lean Meta Server Elab Tactic
/-!
This file defines the `draw_graph` tactic for interactive graph construction and an expression presenter that visualizes graph expressions.
-/

/-! ## Layout attribute

`@[graph_layout "concentric"]` on a graph definition records a preferred widget
layout. `draw_graph` reads this off the head constant of the graph expression and
applies it by default. Supported layouts: `"circle"`, `"concentric"`, `"hub"`,
`"cube"`, `"spring"`. -/

/-- Attribute syntax: `@[graph_layout "concentric"]`. -/
syntax (name := graphLayoutStx) "graph_layout " str : attr

/-- Maps a graph declaration name to its preferred layout string. -/
initialize graphLayoutAttr : ParametricAttribute String ←
  registerParametricAttribute {
    name := `graphLayoutStx
    descr := "preferred widget layout for a graph declaration"
    getParam := fun _ stx =>
      match stx with
      | `(attr| graph_layout $s:str) => pure s.getString
      | _ => throwError "invalid graph_layout syntax; expected `@[graph_layout \"concentric\"]`"
  }

/-- Look up the layout registered for a declaration name (if any). -/
def getGraphLayout (env : Environment) (n : Name) : Option String :=
  graphLayoutAttr.getParam? env n


/-- Props for the graph widget. -/
structure GraphWidgetProps where
  adjMatrix : String := ""
  subgraphMatrix : String := ""
  walkExpr : String := ""
  walkStart : String := ""
  walkEnd : String := ""
  graphIdent : String := ""
  layout : String := ""
  directed : Bool := false
  weighted : Bool := false
  readOnly : Bool := false
  /-- When set, "Send to Lean" emits a top-level `def` (used by the `#draw_graph`
      command) rather than a `let` binding (used by the `draw_graph` tactic). -/
  topLevel : Bool := false
  initialMatrix : Array (Array Nat) := #[]
  replaceRange : Lsp.Range
  deriving Server.RpcEncodable

open scoped Jsx in
/-- RPC method that generates the edit request to replace the tactic with the string -/
@[server_rpc_method]
def graphWidget.updateGraph (props : GraphWidgetProps) : RequestM (RequestTask MakeEditLinkProps) :=
  RequestM.asTask do
    let doc : FileWorker.EditableDocument ← RequestM.readDoc

    let constructor := match props.directed, props.weighted with
      | false, false => "Matrix.toSimpleGraph"
      | true,  false => "Matrix.toDigraph"
      | false, true  => "Matrix.toWeightedSimpleGraph"
      | true,  true  => "Matrix.toWeightedDigraph"

    let graphName := if props.graphIdent.isEmpty then "G" else props.graphIdent
    let subgraphExpr := s!"{graphName}.subgraphOfMatrix {props.subgraphMatrix}"

    let graphChanged := !props.adjMatrix.isEmpty
    let hasSubgraph := !props.subgraphMatrix.isEmpty
    let hasWalk := !props.walkExpr.isEmpty
    let indent := String.ofList (List.replicate props.replaceRange.start.character ' ')
    let walkType := if props.directed then
        s!"{graphName}.Walk {props.walkStart} {props.walkEnd}"
      else
        s!"{graphName}.toSimpleGraph.Walk {props.walkStart} {props.walkEnd}"

    -- The tactic emits `let` bindings inside a proof; the `#draw_graph` command
    -- emits a top-level `def`. Walks/subgraphs are proof-context only, so the
    -- top-level path just writes the graph definition.
    let kw := if props.topLevel then "def" else "let"
    let newLeanText :=
      if props.topLevel then
        if graphChanged then s!"def {graphName} := {constructor} {props.adjMatrix}" else ""
      else if hasWalk then
        if graphChanged then
          s!"{kw} {graphName} := {constructor} {props.adjMatrix}\n{indent}let p : {walkType} := {props.walkExpr}"
        else
          s!"let p : {walkType} := {props.walkExpr}"
      else match graphChanged, hasSubgraph with
      | false, false => ""
      | false, true  => s!"let G' := {subgraphExpr}"
      | true,  false => s!"{kw} {graphName} := {constructor} {props.adjMatrix}"
      | true,  true  => s!"{kw} {graphName} := {constructor} {props.adjMatrix}\n{indent}let G' := {subgraphExpr}"

    let editLinkProps : MakeEditLinkProps := .ofReplaceRange doc.meta props.replaceRange newLeanText
    return editLinkProps

@[widget_module]
def graphWidget : Component GraphWidgetProps where
  javascript := include_str ".." / "widget" / "widget_graph.js"

def lspRangeOfStx? (text : FileMap) (stx : Syntax) (canonicalOnly := false) : Option Lsp.Range :=
  text.utf8RangeToLspRange <$> stx.getRange? canonicalOnly

/-! ## Helper functions for matrix extraction -/

/-- Infer directed/weighted flags from the type of a graph expression. -/
private def classifyGraphType (e : Expr) : MetaM (Bool × Bool) := do
  let t ← inferType e
  let name := t.getAppFn.constName?.getD .anonymous
  let isDirected := name == ``Digraph || name == ``WeightedDigraph
  let isWeighted := name == ``WeightedSimpleGraph || name == ``WeightedDigraph
  return (isDirected, isWeighted)

/-- Check if an expression head is `Matrix.vecCons` or `Fin.cons`. -/
private def isVecCons (fn : Expr) : Bool :=
  fn.isConst && (fn.constName! == ``Matrix.vecCons || fn.constName! == ``Fin.cons)

/-- Check if an expression head is `Matrix.vecEmpty` or `Fin.elim0`. -/
private def isVecEmpty (fn : Expr) : Bool :=
  fn.isConst && (fn.constName! == ``Matrix.vecEmpty || fn.constName! == ``Fin.elim0)

/-- Walk a `vecCons` chain to extract Nat entries from a single row. -/
private partial def extractNats (e : Expr) : MetaM (Array Nat) := do
  let fn := e.getAppFn
  if isVecCons fn then
    let args := e.getAppArgs
    if args.size < 4 then return #[]
    let head ← whnf args[2]!
    let val := match head with
      | .lit (.natVal n) => n
      | _ => 0
    let rest ← extractNats args[3]!
    return #[val] ++ rest
  else if isVecEmpty fn then
    return #[]
  else
    return #[]

/-- Walk a `vecCons` chain to extract row vectors from a matrix expression. -/
private partial def extractRows (e : Expr) : MetaM (Array (Array Nat)) := do
  let fn := e.getAppFn
  if isVecCons fn then
    let args := e.getAppArgs
    if args.size < 4 then return #[]
    let row ← extractNats args[2]!
    let rest ← extractRows args[3]!
    return #[row] ++ rest
  else if isVecEmpty fn then
    return #[]
  else
    return #[]

/-- Check if a type has `Matrix` as its head constant (without unfolding). -/
private def isMatrixType (t : Expr) : Bool :=
  t.getAppFn.constName?.getD .anonymous == ``Matrix

/-- Find the first `vecCons`-rooted subexpression among the app args of `e`. -/
private def findVecConsArg (e : Expr) : Option Expr :=
  let args := e.getAppArgs
  args.findSome? fun arg =>
    if isVecCons arg.getAppFn then some arg else none

/-- Decode a graph6 string into an adjacency matrix. -/
private def decodeG6 (s : String) : Array (Array Nat) := Id.run do
  if s.isEmpty then return #[]
  let n := s.toList.head!.toNat - 63
  let chars := (s.toList).drop 1
  let bits : Array Nat := chars.foldl (fun acc c =>
    let v := c.toNat - 63
    acc ++ #[v / 32 % 2, v / 16 % 2, v / 8 % 2, v / 4 % 2, v / 2 % 2, v % 2]) #[]
  let mut result : Array (Array Nat) := Array.replicate n (Array.replicate n 0)
  let mut bitIdx := 0
  for j in [:n] do
    for i in [:j] do
      if h : bitIdx < bits.size then
        if bits[bitIdx] == 1 then
          result := result.modify i (·.set! j 1)
          result := result.modify j (·.set! i 1)
      bitIdx := bitIdx + 1
  return result

/-- Extract `n` from a `Fin n` expression (as a raw nat literal). -/
private def finCardOf? (finTy : Expr) : MetaM (Option Nat) := do
  unless finTy.getAppFn.isConstOf ``Fin do return none
  let args := finTy.getAppArgs
  if args.size == 0 then return none
  let nExpr ← whnf args[0]!
  return nExpr.rawNatLit?

/-- Evaluate a `SimpleGraph (Fin n)` (or `Digraph (Fin n)`) into an adjacency matrix by
    computing `G.Adj i j` for every pair via its `DecidableRel` instance.
    Returns `#[]` if the graph is not over `Fin n` or has no decidable adjacency. -/
private def evalAdjMatrix (e : Expr) : MetaM (Array (Array Nat)) := do
  let t ← inferType e
  let fn := t.getAppFn
  let isSimple := fn.isConstOf ``SimpleGraph
  let isDigraph := fn.isConstOf ``Digraph
  unless isSimple || isDigraph do return #[]
  let args := t.getAppArgs
  if args.size == 0 then return #[]
  let some n ← finCardOf? args[0]! | return #[]
  let finN := args[0]!            -- the type `Fin n`
  let nLit := mkNatLit n          -- the nat literal `n`
  -- Build: (List.finRange n).map (fun i => (List.finRange n).map (fun j => decide (G.Adj i j)))
  let t ← inferType e
  let isSimpleGraph := t.getAppFn.isConstOf ``SimpleGraph
  let matExpr ← withLocalDeclD `i finN fun i => do
    let inner ← withLocalDeclD `j finN fun j => do
      let adjIJ ← if isSimpleGraph then
          mkAppM ``SimpleGraph.Adj #[e, i, j]
        else
          mkAppM ``Digraph.Adj #[e, i, j]
      let inst ← synthInstance (← mkAppM ``Decidable #[adjIJ])
      let dec ← mkAppOptM ``decide #[adjIJ, inst]
      mkLambdaFVars #[j] dec
    let finRangeN ← mkAppM ``List.finRange #[nLit]
    let rowExpr ← mkAppM ``List.map #[inner, finRangeN]
    mkLambdaFVars #[i] rowExpr
  let finRangeN ← mkAppM ``List.finRange #[nLit]
  let fullExpr ← mkAppM ``List.map #[matExpr, finRangeN]
  let listType ← inferType fullExpr
  let boolMatrix ← unsafe evalExpr (List (List Bool)) listType fullExpr
  return boolMatrix.toArray.map (fun row => row.toArray.map (fun b => if b then 1 else 0))

/-- Extract adjacency matrix data from a graph or matrix expression. -/
private def extractMatrixFromExpr (e : Expr) : MetaM (Array (Array Nat)) := do
  let t ← inferType e
  if isMatrixType t then
    match findVecConsArg e with
    | some vc => extractRows vc
    | none => return #[]
  else
    -- Check if it's readG6 applied to a string literal
    let fn := e.getAppFn
    if fn.isConst && fn.constName! == ``readG6 then
      let args := e.getAppArgs
      for arg in args do
        let arg ← whnf arg
        match arg with
        | .lit (.strVal s) => return decodeG6 s
        | _ => pure ()
    -- Look for a Matrix-typed argument with vecCons
    let args := e.getAppArgs
    for arg in args do
      let argT ← try inferType arg catch _ => pure (mkConst ``Unit)
      if isMatrixType argT then
        match findVecConsArg arg with
        | some vc =>
          let rows ← extractRows vc
          if rows.size > 0 then return rows
        | none => pure ()
    -- Fallback: evaluate the adjacency relation directly (handles named graphs
    -- like `cycleGraph n`, complete graphs, complements, etc. — any
    -- `SimpleGraph`/`Digraph` over `Fin n` with a `DecidableRel` instance).
    try
      let rows ← evalAdjMatrix e
      if rows.size > 0 then return rows
    catch _ => pure ()
    return #[]

/-! ## Shared widget helpers -/

/-- Display the graph widget for a given matrix. Used by both `draw_graph` and `cex_graph`. -/
def showGraphWidget (stx : Syntax) (replaceRange : Lsp.Range)
    (rows : Array (Array Nat) := #[])
    (directed := false) (weighted := false) (readOnly := false)
    (graphIdent : String := "") (layout : String := "") : TacticM Unit := do
  let props : GraphWidgetProps :=
    { adjMatrix := if readOnly then
        let rowStrs := rows.map fun row =>
          String.intercalate ", " (row.toList.map toString)
        "!![" ++ String.intercalate ";\n    " rowStrs.toList ++ "]"
      else ""
      «graphIdent» := graphIdent
      «layout» := layout
      «directed» := directed
      «weighted» := weighted
      «readOnly» := readOnly
      initialMatrix := rows
      replaceRange := replaceRange }
  Widget.savePanelWidgetInfo graphWidget.javascriptHash (rpcEncode props) stx

/-! ## draw_graph: interactive graph construction widget -/

syntax (name := drawGraphTac) "draw_graph" (colGt ident)? : tactic

@[tactic drawGraphTac] def drawGraph : Tactic := fun stx => do
  let fm ← getFileMap
  let some replaceRange := (lspRangeOfStx? fm stx false) | return

  let mut rows : Array (Array Nat) := #[]
  let mut directed := false
  let mut weighted := false
  let mut layout := ""

  -- If an ident is given, pre-populate the widget with that graph (use last match for shadowing)
  if !stx[1].isNone then
    let name := stx[1][0].getId
    let goal ← getMainGoal
    let lctx ← goal.getDecl >>= fun md => pure md.lctx
    -- First look for a local `let`-bound value with this name (respecting shadowing).
    let mut lastVal : Option Expr := none
    for decl in lctx do
      let some val := decl.value? | continue
      if decl.userName != name then continue
      lastVal := some val
    -- Otherwise resolve as a global constant (top-level `def`).
    if lastVal.isNone then
      let fullName? ← (do
          try pure (some (← resolveGlobalConstNoOverload (mkIdent name)))
          catch _ => pure none)
      if let some fullName := fullName? then
        lastVal := some (mkConst fullName)
    if let some origVal := lastVal then
      -- Layout is read from the ORIGINAL value's head constant (before whnf unfolds it).
      let headName := origVal.getAppFn.constName?.getD .anonymous
      layout := (getGraphLayout (← getEnv) headName).getD ""
      let val ← goal.withContext do
        let rows ← extractMatrixFromExpr origVal
        if rows.size > 0 then return origVal
        whnf origVal
      let (d, w) ← goal.withContext do classifyGraphType val
      directed := d
      weighted := w
      rows ← goal.withContext do extractMatrixFromExpr val

  let identName := if !stx[1].isNone then stx[1][0].getId.toString else ""
  showGraphWidget stx replaceRange rows directed weighted
    (graphIdent := identName) (layout := layout)

/-! ## `#view_graph` / `#draw_graph` commands

Top-level commands to visualize (`#view_graph`) or author (`#draw_graph`) a graph
without the `example : True := by … trivial` proof scaffolding needed by the
`draw_graph` tactic. `#view_graph` renders read-only; `#draw_graph`'s "Send to
Lean" replaces the command with a top-level `def`. -/

open Elab.Command in
/-- Shared implementation: elaborate `t?` (if given) to a graph, extract its
    adjacency matrix, and save the widget on `stx`. `readOnly`/`topLevel` select
    viewer vs. authoring behaviour. -/
def showGraphCommand (stx : Syntax) (t? : Option Term)
    (readOnly topLevel : Bool) : CommandElabM Unit := do
  let fm ← getFileMap
  let some replaceRange := lspRangeOfStx? fm stx false | return
  -- Prefer a bare identifier as the graph/def name; otherwise default to `G`.
  let identName := match t? with
    | some t => if t.raw.isIdent then t.raw.getId.toString else ""
    | none => ""
  let mut rows : Array (Array Nat) := #[]
  let mut directed := false
  let mut weighted := false
  let mut layout := ""
  if let some t := t? then
    (rows, directed, weighted, layout) ← liftTermElabM do
      let e ← Term.elabTerm t none
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      -- Layout is read from the head constant before `whnf` unfolds it.
      let headName := e.getAppFn.constName?.getD .anonymous
      let layout := (getGraphLayout (← getEnv) headName).getD ""
      let val ← do
        let rs ← extractMatrixFromExpr e
        if rs.size > 0 then pure e else whnf e
      let (d, w) ← classifyGraphType val
      let rows ← extractMatrixFromExpr val
      pure (rows, d, w, layout)
  let props : GraphWidgetProps :=
    { adjMatrix := if readOnly then
        let rowStrs := rows.map fun row =>
          String.intercalate ", " (row.toList.map toString)
        "!![" ++ String.intercalate ";\n    " rowStrs.toList ++ "]"
      else ""
      «graphIdent» := identName
      «layout» := layout
      «directed» := directed
      «weighted» := weighted
      «readOnly» := readOnly
      «topLevel» := topLevel
      initialMatrix := rows
      replaceRange := replaceRange }
  liftCoreM <| Widget.savePanelWidgetInfo graphWidget.javascriptHash (rpcEncode props) stx

/-- `#view_graph t` renders the graph `t` read-only in the infoview. Accepts any
    `SimpleGraph`/`Digraph`/weighted graph over `Fin n` with a `DecidableRel`
    adjacency instance, an adjacency matrix, or a `graph6` string — no proof
    context required. -/
syntax (name := viewGraphCmd) "#view_graph " term : command

open Elab.Command in
@[command_elab viewGraphCmd]
def elabViewGraph : CommandElab := fun
  | stx@`(#view_graph $t:term) => showGraphCommand stx (some t) (readOnly := true) (topLevel := false)
  | _ => throwUnsupportedSyntax

/-- `#draw_graph` opens the interactive editor as a top-level command. With a
    term argument the canvas is pre-populated with that graph; without one you
    draw from scratch. "Send to Lean" replaces the command with a top-level
    `def` for the graph you drew. -/
syntax (name := drawGraphCmd) "#draw_graph" (ppSpace term)? : command

open Elab.Command in
@[command_elab drawGraphCmd]
def elabDrawGraph : CommandElab := fun
  | stx@`(#draw_graph $[$t?:term]?) => showGraphCommand stx t? (readOnly := false) (topLevel := true)
  | _ => throwUnsupportedSyntax

/-! ## Graph expression presenter (shift-click to visualize) -/

/-- Check if an expression is a matrix literal or a g6 string literal. -/
private def isMatrixOrG6 (e : Expr) : MetaM Bool := do
  let t ← inferType e
  -- Check if it's a Matrix type
  if isMatrixType t then return true
  -- Check if it's a String (g6)
  if t.isConstOf ``String then return true
  return false

open scoped Jsx in
/-- Presenter that renders adjacency matrices and g6 strings as graph visualizations. -/
@[expr_presenter]
def graphExprPresenter : ExprPresenter where
  userName := "Graph Visualizer"
  layoutKind := .block
  present e := do
    let valid ← isMatrixOrG6 e
    if !valid then
      return Html.text "Select an adjacency matrix (!![...]) or a graph6 string."

    let t ← inferType e
    let mut rows : Array (Array Nat) := #[]
    let mut isDirected := false
    let mut isWeighted := false

    if t.isConstOf ``String then
      -- Try to extract g6 string literal
      let e' ← whnf e
      match e' with
      | .lit (.strVal s) => rows := decodeG6 s
      | _ => pure ()
    else
      -- Matrix expression
      match findVecConsArg e with
      | some vc => rows ← extractRows vc
      | none => pure ()

    if rows.size == 0 then
      return Html.text "Could not extract matrix data from this expression."

    -- Detect if matrix is asymmetric (directed) or has values > 1 (weighted)
    let n := rows.size
    for i in [:n] do
      for j in [:n] do
        let vij := (rows[i]!)[j]!
        let vji := (rows[j]!)[i]!
        if vij != vji then isDirected := true
        if vij > 1 then isWeighted := true

    let props : GraphWidgetProps :=
      { readOnly := true
        «directed» := isDirected
        «weighted» := isWeighted
        initialMatrix := rows
        replaceRange := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩ }

    return Html.ofComponent graphWidget props #[]

import Lean.Meta.ExprLens
import ProofWidgets.Component.Basic
import ProofWidgets.Data.Html
import ProofWidgets.Component.OfRpcMethod
import ProofWidgets.Component.MakeEditLink
import ProofWidgets.Component.Panel.Basic

import FormalRamsey.G6

open ProofWidgets
open Lean Meta Server Elab Tactic

/-- Props for the graph widget. `kind` selects the payload shape:
    * "g6"        → `graph6` holds a graph6 string (simple, undirected, unweighted)
    * "directed"  → `matrix` holds an n×n 0/1 adjacency matrix (rows = from, cols = to)
    * "weighted"  → `matrix` holds an n×n weight matrix (0 = no edge; symmetric if also
                    undirected, asymmetric if also directed)
    * "subgraph"  → `matrix` holds the full graph, `selectedVertices` / `selectedEdges`
                    describe the chosen subgraph. Edges are [from, to] index pairs. -/
structure GraphWidgetProps where
  graph6 : String
  replaceRange : Lsp.Range
  deriving Server.RpcEncodable

structure GraphSendProps where
  kind : String
  graph6 : String
  matrix : Array (Array Float)
  selectedVertices : Array Nat
  selectedEdges : Array (Array Nat)
  replaceRange : Lsp.Range
  deriving Server.RpcEncodable

/-- Render one cell. Whole-number floats print as `1`, not `1.0`, so the
    resulting literal typechecks as either `Nat`/`Int` or `Float`. -/
private def cellToLean (x : Float) : String :=
  if x == x.floor && x.abs < 1e15 then toString x.toInt64 else toString x

private def matrixToLean (m : Array (Array Float)) : String :=
  let rows := m.map (fun row =>
    "#[" ++ String.intercalate ", " (row.toList.map cellToLean) ++ "]")
  "#[" ++ String.intercalate ", " rows.toList ++ "]"

private def natArrayToLean (a : Array Nat) : String :=
  "#[" ++ String.intercalate ", " (a.toList.map toString) ++ "]"

private def edgeArrayToLean (a : Array (Array Nat)) : String :=
  let pairs := a.map (fun e =>
    match e.toList with
    | [x, y] => s!"({x}, {y})"
    | _ => "(0, 0)")
  "#[" ++ String.intercalate ", " pairs.toList ++ "]"

open scoped Jsx in
/-- Legacy RPC method — graph6 only. Kept for backward compatibility. -/
@[server_rpc_method]
def graphWidget.updateGraph (props : GraphWidgetProps) : RequestM (RequestTask MakeEditLinkProps) :=
  RequestM.asTask do
    let doc : FileWorker.EditableDocument ← RequestM.readDoc

    let newLeanText := s!"let G := readG6 \"{props.graph6}\""

    let editLinkProps : MakeEditLinkProps := .ofReplaceRange doc.meta props.replaceRange newLeanText
    return editLinkProps

open scoped Jsx in
/-- RPC method that emits a Lean expression matching the widget's current mode.
    See `GraphSendProps` for the payload contract. -/
@[server_rpc_method]
def graphWidget.sendGraph (props : GraphSendProps) : RequestM (RequestTask MakeEditLinkProps) :=
  RequestM.asTask do
    let doc : FileWorker.EditableDocument ← RequestM.readDoc
    let newLeanText : String :=
      match props.kind with
      | "g6" => s!"let G := readG6 \"{props.graph6}\""
      | "directed" => s!"let G := {matrixToLean props.matrix}"
      | "weighted" => s!"let G := {matrixToLean props.matrix}"
      | "subgraph" =>
          let m := matrixToLean props.matrix
          let v := natArrayToLean props.selectedVertices
          let e := edgeArrayToLean props.selectedEdges
          s!"let G := \{ matrix := {m}, vertices := {v}, edges := {e} }"
      | _ => s!"let G := readG6 \"{props.graph6}\""
    let editLinkProps : MakeEditLinkProps :=
      .ofReplaceRange doc.meta props.replaceRange newLeanText
    return editLinkProps

@[widget_module]
def graphWidget : Component GraphWidgetProps where
  javascript := include_str ".." / "widget" / "widget_graph.js"

def lspRangeOfStx? (text : FileMap) (stx : Syntax) (canonicalOnly := false) : Option Lsp.Range :=
  text.utf8RangeToLspRange <$> stx.getRange? canonicalOnly

syntax (name := drawGraphTac) "draw_graph" : tactic

@[tactic drawGraphTac] def drawGraph : Tactic
  | `(tactic| draw_graph%$stx) => do
    let fm ← getFileMap
    let some replaceRange := (lspRangeOfStx? fm stx false) | return

    let props : GraphWidgetProps := { graph6 := "", replaceRange := replaceRange }

    Widget.savePanelWidgetInfo graphWidget.javascriptHash (rpcEncode props) stx
  | _ => throwUnsupportedSyntax

example : True := by
  --draw_graph
  trivial

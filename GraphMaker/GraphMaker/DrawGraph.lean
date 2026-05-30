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


/-- Props for the graph widget. -/
structure GraphWidgetProps where
  adjMatrix : String := ""
  directed : Bool := false
  weighted : Bool := false
  readOnly : Bool := false
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
      | false, false => "readAdjMatrix"
      | true,  false => "readDigraph"
      | false, true  => "readWeightedAdj"
      | true,  true  => "readWeightedDigraph"

    let newLeanText := s!"let G := {constructor} {props.adjMatrix}"

    let editLinkProps : MakeEditLinkProps := .ofReplaceRange doc.meta props.replaceRange newLeanText
    return editLinkProps

@[widget_module]
def graphWidget : Component GraphWidgetProps where
  javascript := include_str ".." / "widget" / "widget_graph.js"

def lspRangeOfStx? (text : FileMap) (stx : Syntax) (canonicalOnly := false) : Option Lsp.Range :=
  text.utf8RangeToLspRange <$> stx.getRange? canonicalOnly

/-! ## draw_graph: interactive graph construction widget -/

syntax (name := drawGraphTac) "draw_graph" : tactic

@[tactic drawGraphTac] def drawGraph : Tactic
  | `(tactic| draw_graph%$stx) => do
    let fm ← getFileMap
    let some replaceRange := (lspRangeOfStx? fm stx false) | return

    let props : GraphWidgetProps := { replaceRange := replaceRange }

    Widget.savePanelWidgetInfo graphWidget.javascriptHash (rpcEncode props) stx
  | _ => throwUnsupportedSyntax

/-! ## Graph expression presenter (shift-click to visualize) -/

/-- Infer directed/weighted flags from the type of a graph expression. -/
private def classifyGraphType (e : Expr) : MetaM (Bool × Bool) := do
  let t ← inferType e
  let name := t.getAppFn.constName?.getD .anonymous
  let isDirected := name == ``Digraph || name == ``Digraph.WeightedDigraph
  let isWeighted := name == ``WeightedSimpleGraph || name == ``Digraph.WeightedDigraph
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
    -- Otherwise look for a Matrix-typed argument with vecCons
    let args := e.getAppArgs
    for arg in args do
      let argT ← try inferType arg catch _ => pure (mkConst ``Unit)
      if isMatrixType argT then
        match findVecConsArg arg with
        | some vc =>
          let rows ← extractRows vc
          if rows.size > 0 then return rows
        | none => pure ()
    return #[]

/-- Check if an expression has a recognized graph type. -/
private def isGraphExpr (e : Expr) : MetaM Bool := do
  let t ← inferType e
  let name := t.getAppFn.constName?.getD .anonymous
  return name == ``SimpleGraph || name == ``Digraph || name == ``WeightedSimpleGraph
    || name == ``Digraph.WeightedDigraph

open scoped Jsx in
/-- Presenter that renders a graph expression as an interactive visualization. -/
@[expr_presenter]
def graphExprPresenter : ExprPresenter where
  userName := "Graph Visualizer"
  layoutKind := .block
  present e := do
    let isGraph ← isGraphExpr e
    if !isGraph then
      return Html.text "Select a graph expression (e.g. readAdjMatrix, readDigraph, readWeightedAdj, readWeightedDigraph, or readG6)."

    let (isDirected, isWeighted) ← classifyGraphType e
    let rows ← extractMatrixFromExpr e

    if rows.size == 0 then
      return Html.text "Could not extract matrix data from this expression."

    let props : GraphWidgetProps :=
      { readOnly := true
        «directed» := isDirected
        «weighted» := isWeighted
        initialMatrix := rows
        replaceRange := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩ }

    return Html.ofComponent graphWidget props #[]

example : True := by
  let G := readDigraph !![
      0, 1, 0;
      1, 0, 1;
      1, 1, 0]
  let G := readG6 "Dhc"
  with_panel_widgets [ProofWidgets.SelectionPanel]
  trivial

import Lean.Meta.ExprLens
import ProofWidgets.Component.Basic
import ProofWidgets.Data.Html
import ProofWidgets.Component.OfRpcMethod
import ProofWidgets.Component.MakeEditLink
import ProofWidgets.Component.Panel.Basic

import FormalRamsey.G6

open ProofWidgets
open Lean Meta Server Elab Tactic

/-- Props for the counter widget containing the current count. -/
structure GraphWidgetProps where
  graph6 : String
  replaceRange : Lsp.Range
  deriving Server.RpcEncodable

open scoped Jsx in
/-- RPC method that generates the edit request to replace the tactic with the string -/
@[server_rpc_method]
def graphWidget.updateGraph (props : GraphWidgetProps) : RequestM (RequestTask MakeEditLinkProps) :=
  RequestM.asTask do
    let doc : FileWorker.EditableDocument ← RequestM.readDoc

    let newLeanText := s!"let G := readG6 \"{props.graph6}\""

    let editLinkProps : MakeEditLinkProps := .ofReplaceRange doc.meta props.replaceRange newLeanText
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
  draw_graph
  trivial

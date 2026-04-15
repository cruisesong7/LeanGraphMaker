import ProofWidgets.Component.Basic
import ProofWidgets.Data.Html
import ProofWidgets.Component.Panel.Basic

import FormalRamsey.G6

open ProofWidgets
open Lean Elab Tactic

/-- Props for the read-only graph6 visualizer widget (Issue #9). -/
structure VisualizeGraphProps where
  graph6 : String
  deriving Server.RpcEncodable

@[widget_module]
def visualizeGraphWidget : Component VisualizeGraphProps where
  javascript := include_str ".." / "widget" / "widget_visualize.js"

/-- Visualize a graph6 string inline:
    `visualize_g6 "Dw"` renders the corresponding graph in the InfoView. -/
syntax (name := visualizeG6Tac) "visualize_g6" str : tactic

@[tactic visualizeG6Tac] def visualizeG6 : Tactic
  | `(tactic| visualize_g6%$stx $s:str) => do
    let props : VisualizeGraphProps := { graph6 := s.getString }
    Widget.savePanelWidgetInfo visualizeGraphWidget.javascriptHash (rpcEncode props) stx
  | _ => throwUnsupportedSyntax

example : True := by
  --visualize_g6 "Dw"
  trivial

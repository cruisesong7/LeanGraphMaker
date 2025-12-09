import Lean.Meta.ExprLens
import ProofWidgets.Component.Basic
import ProofWidgets.Data.Html
import ProofWidgets.Component.OfRpcMethod
import ProofWidgets.Component.MakeEditLink
import ProofWidgets.Component.Panel.Basic

open ProofWidgets
open Lean Meta Server Elab Tactic

/-- Props for the counter widget containing the current count. -/
structure CounterWidgetProps where
  count : Nat
  replaceRange : Lsp.Range
  deriving Server.RpcEncodable

/-- RPC method that increments the counter and returns the new count. -/
@[server_rpc_method]
def incrementCounter : CounterWidgetProps → RequestM (RequestTask CounterWidgetProps)
  | props =>
    RequestM.asTask (
      do return { count := props.count + 1, replaceRange := props.replaceRange }
    )

open scoped Jsx in
@[server_rpc_method]
def counterWidget.rpc (props : CounterWidgetProps) : RequestM (RequestTask Html) :=
  RequestM.asTask do
    let doc : FileWorker.EditableDocument ← RequestM.readDoc
    let inner : Html ← (do return (
      Html.ofComponent
      MakeEditLink
      (.ofReplaceRange doc.meta props.replaceRange s!"{props.count}")
      #[ .text s!"{props.count}" ])
    )
    return <details «open»={true}>
      <summary className="mv2 pointer">Hello </summary>
      <div className="ml1">{inner}</div>
    </details>

/-- React component that displays a button and current count. -/
@[widget_module]
def counterWidget : Component CounterWidgetProps where
  javascript := "
    import { RpcContext, mapRpcError } from '@leanprover/infoview'
    import * as React from 'react';
    const e = React.createElement;

    export default function(props) {
      const [count, setCount] = React.useState(props.count);
      const [range, _] = React.useState(props.replaceRange);
      const rs = React.useContext(RpcContext);
      const html = rs.call('counterWidget.rpc', { count: count, replaceRange: range }).then()

      return e('div', {}, [
        e('button', {
          onClick: () => {
            rs.call('incrementCounter', { count: count, replaceRange: range })
              .then(newProps => setCount(newProps.count))
              .catch(e => console.error(mapRpcError(e)))
          }
        }, 'Click me!'),
        e('span', { style: { marginLeft: '10px' } }, `Count: ${count}`),
        e('span', { style: { marginLeft: '10px' } },
          `HTML: ${html})`)
        // rs.call('counterWidget.rpc', { count: count, replaceRange: range })
      ])
    }
  "

/-- Tactic to create and display the counter widget. -/
syntax (name := makeCounterTac) "make_counter" : tactic

-- Not in this version of Lean; copied from newer version
def lspRangeOfStx? (text : FileMap) (stx : Syntax) (canonicalOnly := false) : Option Lsp.Range :=
  text.utf8RangeToLspRange <$> stx.getRange? canonicalOnly

@[tactic makeCounterTac] def makeCounter : Tactic
  | `(tactic| make_counter%$stx) => do
    let fm ← (do getFileMap)
    let some replaceRange := (lspRangeOfStx? fm stx false) | return
    let props : CounterWidgetProps := { count := 1, replaceRange := replaceRange }
    Widget.savePanelWidgetInfo counterWidget.javascriptHash (rpcEncode props) stx
  | _ => throwUnsupportedSyntax

/-- Example usage -/
example : True := by
  make_counter
  trivial

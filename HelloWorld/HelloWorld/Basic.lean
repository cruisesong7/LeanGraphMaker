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
def counterWidget.editLinkPropsRpc (props : CounterWidgetProps) : RequestM (RequestTask MakeEditLinkProps) :=
  RequestM.asTask do
    let doc : FileWorker.EditableDocument ← RequestM.readDoc
    let editLinkProps : MakeEditLinkProps := .ofReplaceRange doc.meta props.replaceRange s!"{props.count}"
    return editLinkProps

/-

import * as React from 'react'
import { EditorContext } from '@leanprover/infoview'
import { Range, TextDocumentEdit } from 'vscode-languageserver-protocol'

interface MakeEditLinkProps {
  edit : TextDocumentEdit
  newSelection? : Range
  title? : string
}

export default function(props: React.PropsWithChildren<MakeEditLinkProps>) {
  const ec = React.useContext(EditorContext)

  return <a className='link pointer dim ' title={props.title ?? ''}
      onClick={async () => {
        await ec.api.applyEdit({ documentChanges: [props.edit] })
        // TODO: https://github.com/leanprover/vscode-lean4/issues/225
        if (props.newSelection)
          await ec.revealLocation({ uri: props.edit.textDocument.uri, range: props.newSelection })
      }}
    >
      {props.children}
    </a>
}

-/

/-- React component that displays a button and current count. -/
@[widget_module]
def counterWidget : Component CounterWidgetProps where
  javascript := include_str ".." / "widget" / "widget.ts"

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

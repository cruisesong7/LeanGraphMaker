import { RpcContext, EditorContext, mapRpcError } from '@leanprover/infoview'
import * as React from 'react';

const e = React.createElement;

export default function(props) {
  const rs = React.useContext(RpcContext);
  const ec = React.useContext(EditorContext)

  const [count, setCount] = React.useState(props.count);
  const [range, _] = React.useState(props.replaceRange);
  const editLinkPropsPromise = rs.call('counterWidget.editLinkPropsRpc', { count: count, replaceRange: range });
  const linkOnClick =
    () => editLinkPropsPromise.then(editLinkProps => {
      ec.api.applyEdit({ documentChanges: [editLinkProps.edit] })
      if (editLinkProps.newSelection)
        ec.revealLocation({ uri: editLinkProps.edit.textDocument.uri, range: editLinkProps.newSelection })
    });

  return e('div', {}, [
    e('button', {
      onClick: () => {
        rs.call('incrementCounter', { count: count, replaceRange: range })
          .then(newProps => setCount(newProps.count))
          .catch(e => console.error(mapRpcError(e)))
      }
    }, 'Click me!'),
    e('span', { style: { marginLeft: '10px' } }, `Count: ${count}`),
    e('br'),
    e('br'),
    e('a', { className: 'link pointer dim', onClick: linkOnClick }, 'Insert counter')
  ])
}
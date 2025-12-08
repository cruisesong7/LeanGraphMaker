import Lake
open Lake DSL

package «GraphMaker»

lean_lib «GraphMaker» where

@[default_target]
lean_exe "graphmaker" where
  root := `Main

require proofwidgets from git "https://github.com/leanprover-community/ProofWidgets4"@"v0.0.64"
require formal_ramsey from git "https://github.com/cruisesong7/formal_ramsey"@"c1ec6fc"

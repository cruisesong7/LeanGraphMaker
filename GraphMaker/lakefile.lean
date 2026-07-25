import Lake
open Lake DSL

package «GraphMaker»

lean_lib «GraphMaker» where

require proofwidgets from git "https://github.com/leanprover-community/ProofWidgets4"@"v0.0.87"
require formal_ramsey from git "https://github.com/cruisesong7/formal_ramsey"@"9ecbb4f"
require verso from git "https://github.com/leanprover/verso"@"v4.28.0"

lean_lib GraphMakerBlog where
  srcDir := "Blog"

lean_exe blog where
  srcDir := "Blog"
  root := `BlogMain
  supportInterpreter := true

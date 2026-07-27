import GraphMaker.DrawGraph
import FormalRamsey.RamseyGraphs

namespace RamseyGraphExamples

/-!
# Lower Bounds for Small Ramsey Numbers

This file contains proofs establishing the lower bounds of various small Ramsey numbers
by providing explicit graph counterexamples.

In general, to prove a lower bound such as $R(s, t) > n$, we must demonstrate the
existence of a graph of order $n$ that lacks both a clique of size $s$ and an
independent set of size $t$. This is formalized by showing that a specific graph
does not satisfy `RamseyGraphProp n s t`.

### Example: $R(2,3) > 2$
To show that the Ramsey number $R(2,3)$ is strictly greater than 2, we find a
counterexample graph of order 2 that does not have the `RamseyGraphProp`—meaning
it has no clique of 2 nor an independent set of 3.

## Using the widget

Each proof binds its counterexample with `let G := …` and has a commented
`draw_graph` line beneath it. To draw/edit interactively, uncomment `draw_graph`
and comment out the `let G` binding, then put your cursor on `draw_graph` to open
the canvas. "Send to Lean" writes a fresh `let G := …` in its place. Recipe:

  * Click empty space to add a vertex; click one vertex then another to toggle the
    edge between them; drag to move; right-click a vertex to delete it; `Ctrl+Z` undo.
  * Click empty space again to deselect (it no longer adds a stray vertex).
  * Use the mode dropdown ("Select Subgraph" / "Select Walk") to highlight a
    sub-structure, then "Send to Lean" to write the drawn graph back into the proof.

To view a graph without any proof scaffolding, use the `#view_graph` command
instead (see `NamedGraphs.lean`).
-/

theorem R23 : ¬(RamseyGraphProp 2 2 3) := by
  simp only [RamseyGraphProp, not_forall]
  with_panel_widgets [ProofWidgets.SelectionPanel]
  -- TODO: to draw/edit interactively, uncomment `draw_graph` and comment out `let G`.
  let G := readG6 "A?"
  -- draw_graph
  use G
  simp [not_or]
  apply And.intro
  · intros S
    rw [← SimpleGraph.mem_cliqueFinset_iff]
    rw [show G.cliqueFinset 2 = Finset.empty by native_decide]
    exact Finset.notMem_empty S
  · intros T
    rw [← SimpleGraph.mem_indepSetFinset_iff]
    rw [show G.indepSetFinset 3 = Finset.empty by native_decide]
    exact Finset.notMem_empty T

theorem R33 : ¬(RamseyGraphProp 5 3 3) := by
  simp only [RamseyGraphProp, not_forall]
  with_panel_widgets [ProofWidgets.SelectionPanel]
  -- TODO: to draw/edit interactively, uncomment `draw_graph` and comment out `let G`.
  -- draw_graph
  let G := Matrix.toSimpleGraph !![
    0, 1, 0, 0, 1;
    1, 0, 1, 0, 0;
    0, 1, 0, 1, 0;
    0, 0, 1, 0, 1;
    1, 0, 0, 1, 0]
  use G
  simp [not_or]
  apply And.intro
  · intros S
    rw [← SimpleGraph.mem_cliqueFinset_iff]
    rw [show G.cliqueFinset 3 = Finset.empty by native_decide]
    exact Finset.notMem_empty S
  · intros T
    rw [← SimpleGraph.mem_indepSetFinset_iff]
    rw [show G.indepSetFinset 3 = Finset.empty by native_decide]
    exact Finset.notMem_empty T

theorem R34 : ¬(RamseyGraphProp 8 3 4) := by
  simp only [RamseyGraphProp, not_forall]
  -- TODO: to draw/edit interactively, uncomment `draw_graph` and comment out `let G`.
  -- draw_graph
  let G := readG6 "GhdHKc"
  use G
  simp [not_or]
  apply And.intro
  · intros S
    rw [← SimpleGraph.mem_cliqueFinset_iff]
    rw [show G.cliqueFinset 3 = Finset.empty by native_decide]
    exact Finset.notMem_empty S
  · intros T
    rw [← SimpleGraph.mem_indepSetFinset_iff]
    rw [show G.indepSetFinset 4 = Finset.empty by native_decide]
    exact Finset.notMem_empty T

end RamseyGraphExamples

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

To aid in visualizing these constructions, the concrete counterexamples can be
constructed directly in the Infoview by invoking the `draw_graph` command, or inspected using the `with_panel_widgets [ProofWidgets.SelectionPanel]`.
-/

theorem R23 : ¬(RamseyGraphProp 2 2 3) := by
  simp only [RamseyGraphProp, not_forall]
  -- draw_graph
  with_panel_widgets [ProofWidgets.SelectionPanel]
  let G := readG6 "A?"
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
  --draw_graph
  with_panel_widgets [ProofWidgets.SelectionPanel]
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
  --draw_graph
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

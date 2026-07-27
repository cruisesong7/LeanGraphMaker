import GraphMaker.GraphTypes
import GraphMaker.DrawGraph
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Spanning Trees

Defines spanning trees and minimum spanning trees for weighted graphs, with
interactive examples using `draw_graph` for subgraph selection.
-/

namespace WeightedSimpleGraph

variable {V : Type*} {W : Type*}

/-- Sums the weights of a given finite set of edges. -/
def weightSum [AddCommMonoid W] (G : WeightedSimpleGraph V W) (edges : Finset (Sym2 V)) : W :=
  edges.sum G.weight

/-- `T` is a spanning tree of the underlying graph `G`. -/
@[reducible] def IsSpanningTree (G : WeightedSimpleGraph V W) (T : G.toSimpleGraph.Subgraph) : Prop :=
  T.spanningCoe.IsTree

/-- `T` is a Minimum Spanning Tree of `G`. -/
def IsMST [Fintype V] [DecidableEq V] [AddCommMonoid W] [LinearOrder W]
    (G : WeightedSimpleGraph V W) (T : G.toSimpleGraph.Subgraph)
    [DecidableRel T.Adj] : Prop :=
  G.IsSpanningTree T ∧
  ∀ (T' : G.toSimpleGraph.Subgraph) [DecidableRel T'.Adj],
    G.IsSpanningTree T' →
    G.weightSum T.spanningCoe.edgeFinset ≤ G.weightSum T'.spanningCoe.edgeFinset

/-- There exists a spanning tree with weight less than `bound`. -/
def HasSpanningTreeLt [Fintype V] [DecidableEq V] [AddCommMonoid W] [Preorder W]
    (G : WeightedSimpleGraph V W) (bound : W) : Prop :=
  ∃ (T : G.toSimpleGraph.Subgraph) (_ : DecidableRel T.Adj),
    G.IsSpanningTree T ∧ G.weightSum T.spanningCoe.edgeFinset < bound

end WeightedSimpleGraph

/-! ## Example: find a spanning tree with weight < 10

Cursor on `draw_graph G` to visualize the graph. To pick the spanning tree
interactively: choose "Select Subgraph" from the mode dropdown, click the tree
edges — 0-1 (w=3), 1-2 (w=2), 2-3 (w=1), total = 6 < 10 — then "Send to Lean" to
fill in `G'`. Click empty space to deselect. -/

open WeightedSimpleGraph in
example : let G := (Matrix.toWeightedSimpleGraph !![0, 3, 5, 0;
    3, 0, 2, 4;
    5, 2, 0, 1;
    (0 : ℕ), 4, 1, 0])
  G.HasSpanningTreeLt 10 := by
  intro G
  -- TODO: uncomment `draw_graph G` to open the widget (leave the `let G'` below).
  -- draw_graph G
  let G' := G.subgraphOfMatrix !![
      0, 1, 0, 0;
      1, 0, 1, 0;
      0, 1, 0, 1;
      0, 0, 1, 0]
  exact ⟨G', inferInstance, by decide, by decide⟩

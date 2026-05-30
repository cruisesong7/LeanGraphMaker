import GraphMaker.GraphTypes
import GraphMaker.DrawGraph
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace WeightedSimpleGraph

example : WeightedSimpleGraph (Fin 3) ℕ :=
  WeightedSimpleGraph.fromMatrix !![
    0, 5, 8;
    5, 0, 3;
    8, 3, 0
  ] (by decide)

/-- Sums the weights of a given finite set of edges. -/
def weightSum [AddCommMonoid W] (G : WeightedSimpleGraph V W) (edges : Finset (Sym2 V)) : W :=
  edges.sum G.weight

/-- `T` is a spanning tree of the underlying graph `G`. -/
def IsSpanningTree (G : WeightedSimpleGraph V W) (T : SimpleGraph V) : Prop :=
  T ≤ G.toSimpleGraph ∧ T.IsTree

/-- `T` is a Minimum Spanning Tree of `G`. -/
def IsMST (G : WeightedSimpleGraph V W) (T : SimpleGraph V) [Fintype V] [AddCommMonoid W] [LinearOrder W][DecidableRel T.Adj] : Prop :=
  G.IsSpanningTree T ∧
  ∀ (T' : SimpleGraph V) [DecidableRel T'.Adj], G.IsSpanningTree T' →
    G.weightSum T.edgeFinset ≤ G.weightSum T'.edgeFinset

end WeightedSimpleGraph

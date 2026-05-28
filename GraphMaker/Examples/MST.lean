import Mathlib.Combinatorics.SimpleGraph.Basic
import GraphMaker.DrawGraph
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Acyclic

universe u

@[ext]
structure WeightedSimpleGraph (V : Type u) (W : Type v) extends SimpleGraph V where
  -- The weight function assigns a value to every possible pair of vertices.
  weight : Sym2 V → W

@[reducible]
def Matrix.IsWeightedAdjMatrix {V W : Type*} [Zero W] (M : Matrix V V W) : Prop :=
  M.IsSymm ∧ ∀ x, M x x = 0

namespace WeightedSimpleGraph

/-- Constructs a WeightedSimpleGraph from a adjMatrix. -/
def fromMatrix {V : Type u} {W : Type v} [Zero W] [LinearOrder W]
    (M : Matrix V V W) (_ : Matrix.IsWeightedAdjMatrix M) : WeightedSimpleGraph V W := {

  toSimpleGraph := SimpleGraph.fromRel (fun u v => M u v > 0)

  weight := Sym2.lift ⟨
    fun u v => max (M u v) (M v u),
    by
      intro a b
      dsimp
      exact max_comm (M a b) (M b a)
  ⟩
}

example : WeightedSimpleGraph (Fin 3) ℕ :=
  WeightedSimpleGraph.fromMatrix !![
    0, 5, 8;
    5, 0, 3;
    8, 3, 0
  ] (by native_decide)

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

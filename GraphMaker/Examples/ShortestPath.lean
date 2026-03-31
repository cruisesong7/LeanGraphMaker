import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.Digraph.Basic

universe u v

namespace Digraph

@[ext]
structure WeightedDigraph (V : Type u) (W : Type v) extends Digraph V where
  -- The weight function assigns a value to every possible pair of vertices.
  weight : V → V → W

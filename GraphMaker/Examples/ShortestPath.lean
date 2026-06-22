import GraphMaker.GraphTypes
import GraphMaker.DrawGraph
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Walks.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting

/-!
# Weighted Shortest Path

Defines weighted path cost, single-source shortest path (SSSP), and shortest
path tree properties for `WeightedSimpleGraph`, building on mathlib's
`SimpleGraph.Walk`.
-/

namespace WeightedSimpleGraph

variable {V : Type*} {W : Type*}

/-! ## Walk weight -/

/-- The weight of a walk: sum of edge weights along the path. -/
def walkWeight [AddCommMonoid W] (G : WeightedSimpleGraph V W) {u v : V}
    (p : G.toSimpleGraph.Walk u v) : W :=
  (p.edges.map G.weight).sum

theorem walkWeight_nil [AddCommMonoid W] (G : WeightedSimpleGraph V W) (u : V) :
    G.walkWeight (SimpleGraph.Walk.nil (u := u)) = 0 := by
  simp [walkWeight, SimpleGraph.Walk.edges]

theorem walkWeight_cons [AddCommMonoid W] (G : WeightedSimpleGraph V W) {u v w : V}
    (h : G.toSimpleGraph.Adj u v) (p : G.toSimpleGraph.Walk v w) :
    G.walkWeight (SimpleGraph.Walk.cons h p) = G.weight s(u, v) + G.walkWeight p := by
  simp [walkWeight, SimpleGraph.Walk.edges]

/-- There exists a path from `s` to `t` with weight less than `bound`. -/
@[reducible] def HasPathLt [Fintype V] [DecidableEq V] [AddCommMonoid W] [Preorder W]
    (G : WeightedSimpleGraph V W) [DecidableRel G.toSimpleGraph.Adj] (s t : V) (bound : W) : Prop :=
  ∃ (p : G.toSimpleGraph.Path s t), G.walkWeight p.val < bound

/-! ## Single-source shortest path (SSSP) -/

/-- A distance function `d` is a valid SSSP solution from source `s` if
    `d s = 0`, and for every reachable vertex `v`, `d v` is the minimum walk weight. -/
def IsSSSP [AddCommMonoid W] [Preorder W] (G : WeightedSimpleGraph V W) (s : V)
    (d : V → W) : Prop :=
  d s = 0 ∧
  ∀ v, G.toSimpleGraph.Reachable s v →
    (∀ (p : G.toSimpleGraph.Walk s v), d v ≤ G.walkWeight p) ∧
    (∃ (p : G.toSimpleGraph.Walk s v), d v = G.walkWeight p)

/-- A shortest path tree rooted at `s`: a subgraph `T ≤ G` that is acyclic, connected,
    and whose unique paths from `s` realize the shortest path distances. -/
def IsSPTree [AddCommMonoid W] [Preorder W] (G : WeightedSimpleGraph V W) (s : V)
    (T : SimpleGraph V) (hle : T ≤ G.toSimpleGraph) (d : V → W) : Prop :=
  T.Connected ∧
  T.IsAcyclic ∧
  G.IsSSSP s d ∧
  ∀ v, G.toSimpleGraph.Reachable s v →
    ∃ (p : T.Walk s v), d v = G.walkWeight (p.map (SimpleGraph.Hom.ofLE hle))

end WeightedSimpleGraph

/-! ## Directed weighted paths -/

namespace WeightedDigraph

variable {V : Type*} {W : Type*}

/-- A directed walk in a weighted digraph. -/
inductive Walk (G : WeightedDigraph V W) : V → V → Type _
  | nil {u : V} : Walk G u u
  | cons {u v w : V} (h : G.toDigraph.Adj u v) (p : Walk G v w) : Walk G u w

/-- The weight of a directed walk. -/
def Walk.weight [AddCommMonoid W] {G : WeightedDigraph V W} {u v : V} :
    G.Walk u v → W
  | .nil => 0
  | @Walk.cons _ _ _ u' v' _ _ p => G.weight u' v' + p.weight

/-- The length of a directed walk. -/
def Walk.length {G : WeightedDigraph V W} {u v : V} : G.Walk u v → ℕ
  | .nil => 0
  | .cons _ p => p.length + 1

/-- There exists a directed path from `s` to `t` with weight less than `bound`. -/
def HasPathLt [AddCommMonoid W] [Preorder W] [DecidableEq V]
    (G : WeightedDigraph V W) (s t : V) (bound : W) : Prop :=
  ∃ (p : G.Walk s t), p.weight < bound

end WeightedDigraph

/-! ## Example: find a directed path from 0 to 3 with weight < 8

Directed graph: 0→1 (w=3), 0→2 (w=5), 1→2 (w=2), 1→3 (w=4), 2→3 (w=1).
Path 0→1→2→3 has weight 3+2+1 = 6 < 8. -/

/-! ### Directed graph example -/

open WeightedDigraph in
example : let G := (Matrix.toWeightedDigraph !![0, 3, 5, 0;
    0, 0, 2, 4;
    0, 0, 0, 1;
    (0 : ℕ), 0, 0, 0])
  G.HasPathLt 0 3 8 := by
  intro G
  --draw_graph G
  let p : G.Walk 0 3 := Walk.cons (v := 1) (by decide) (Walk.cons (v := 2) (by decide)
    (Walk.cons (v := 3) (by decide) Walk.nil))
  exact ⟨p, by decide⟩

/-! ### Undirected graph example -/

open WeightedSimpleGraph in
example : let G := (Matrix.toWeightedSimpleGraph !![0, 3, 5, 0;
    3, 0, 2, 4;
    5, 2, 0, 1;
    (0 : ℕ), 4, 1, 0])
  ∃ (p : G.toSimpleGraph.Walk 0 3), G.walkWeight p < 7 := by
  intro G
  --draw_Graph G
  let p : G.toSimpleGraph.Walk 0 3 := SimpleGraph.Walk.cons (u := 0) (v := 1) (by decide) (SimpleGraph.Walk.cons (u := 1) (v := 2) (by decide) (SimpleGraph.Walk.cons (u := 2) (v := 3) (by decide) (SimpleGraph.Walk.nil)))
  exact ⟨p, by decide⟩

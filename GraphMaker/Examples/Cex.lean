import GraphMaker.CexGraph
import FormalRamsey.RamseyGraphs
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

namespace CexGraphExamples

-- "No graph on 3 vertices has an edge"
-- false: Plausible find a graph with an edge.
lemma no_edge : ∀ G : SimpleGraph (Fin 3), ¬G.Adj 0 1 := by
  cex_graph

-- "Every graph on 4 vertices is triangle-free"
-- false: Plausible finds K₃ as a subgraph.
theorem triangle_free :
    ∀ G : SimpleGraph (Fin 4),
      ∀ i j k : Fin 4, G.Adj i j → G.Adj j k → ¬G.Adj i k := by
  cex_graph

-- "R(3,3) ≤ 5" i.e. every graph on 5 vertices has a triangle or an independent set of size 3.
-- false: R(3,3) = 6, so there exists a graph on 5 vertices (the cycle C₅) avoiding both.
theorem ramsey_3_3_5 : RamseyGraphProp 5 3 3 := by
  unfold RamseyGraphProp
  cex_graph

-- "Every connected graph on 4 vertices is Hamiltonian"
-- false: the claw graph K₁,₃ is connected but has no Hamiltonian cycle.

instance {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableEq (Fin n)] [DecidableRel G.Adj]
    {a : Fin n} (p : G.Walk a a) : Decidable p.IsCycle :=
  decidable_of_iff (p.edges.Nodup ∧ p ≠ .nil ∧ p.support.tail.Nodup)
    ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨⟨h1⟩, h2⟩, h3⟩, fun h => ⟨h.isCircuit.isTrail.edges_nodup, h.isCircuit.ne_nil, h.support_nodup⟩⟩

instance {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableEq (Fin n)] [DecidableRel G.Adj]
    {a : Fin n} (p : G.Walk a a) : Decidable p.IsHamiltonianCycle :=
  decidable_of_iff (p.IsCycle ∧ p.length = Fintype.card (Fin n))
    SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.symm

instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableEq (Fin n)] [DecidableRel G.Adj] :
    Decidable G.IsHamiltonian :=
  decidable_of_iff
    (Fintype.card (Fin n) = 1 ∨
      ∃ a : Fin n, ∃ p : {p : G.Walk a a // p.length = n}, (p : G.Walk a a).IsHamiltonianCycle)
    ⟨fun h h1 => by
      rcases h with h | ⟨a, ⟨p, _⟩, hc⟩
      · exact absurd h h1
      · exact ⟨a, p, hc⟩,
     fun h => by
      by_cases h1 : Fintype.card (Fin n) = 1
      · exact Or.inl h1
      · obtain ⟨a, p, hp⟩ := h h1
        exact Or.inr ⟨a, ⟨p, hp.length_eq.trans (Fintype.card_fin n)⟩, hp⟩⟩

theorem connected_is_hamiltonian :
    ∀ G : SimpleGraph (Fin 4), G.Connected → G.IsHamiltonian := by
  cex_graph

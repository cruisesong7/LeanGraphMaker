import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

universe u v

variable {V : Type u} {W : Type v}

/-! ## Weighted graph structures -/

/-- A weighted simple graph: an irreflexive symmetric relation with edge weights. -/
@[ext]
structure WeightedSimpleGraph (V : Type u) (W : Type v) extends SimpleGraph V where
  weight : Sym2 V → W

/-- A weighted directed graph: a relation with edge weights. -/
@[ext]
structure WeightedDigraph (V : Type u) (W : Type v) extends Digraph V where
  weight : V → V → W

/-! ## Constructors: matrix → graph -/

variable {α : Type*}

/-- Construct a `SimpleGraph V` from a 0/1 adjacency matrix. -/
def Matrix.toSimpleGraph [MulZeroOneClass α] [Nontrivial α]
    (M : Matrix V V α) (h : M.IsAdjMatrix := by constructor <;> decide) : SimpleGraph V :=
  h.toGraph

/-- Construct a `Digraph V` from an adjacency matrix (nonzero = edge). -/
def Matrix.toDigraph [Zero W] (M : Matrix V V W) : Digraph V where
  Adj u v := M u v ≠ 0

/-- Construct a `WeightedSimpleGraph V W` from a symmetric zero-diagonal matrix. -/
def Matrix.toWeightedSimpleGraph [Zero W] [LinearOrder W]
    (M : Matrix V V W) (hsymm : M.IsSymm := by decide) (hdiag : ∀ x, M x x = 0 := by decide) :
    WeightedSimpleGraph V W where
  Adj u v := M u v ≠ 0
  symm u v h := by
    simp only [ne_eq] at h ⊢
    rwa [show M v u = M u v from hsymm.apply u v]
  loopless := ⟨fun v => by simp [hdiag v]⟩
  weight := Sym2.lift ⟨fun u v => M u v, fun a b => by simp [hsymm.apply b a]⟩

/-- Construct a `WeightedDigraph V W` from a matrix (nonzero = edge). -/
def Matrix.toWeightedDigraph [Zero W] (M : Matrix V V W) : WeightedDigraph V W where
  Adj u v := M u v ≠ 0
  weight u v := M u v

instance [MulZeroOneClass α] [Nontrivial α] [DecidableEq α] (M : Matrix V V α)
    (h : M.IsAdjMatrix := by constructor <;> decide) :
    DecidableRel (M.toSimpleGraph h).Adj :=
  inferInstanceAs (DecidableRel h.toGraph.Adj)

instance [Zero W] [DecidableEq W] (M : Matrix V V W) : DecidableRel (M.toDigraph).Adj :=
  fun u v => inferInstanceAs (Decidable (M u v ≠ 0))

instance [Zero W] [DecidableEq W] [LinearOrder W] (M : Matrix V V W)
    (hsymm : M.IsSymm) (hdiag : ∀ x, M x x = 0) :
    DecidableRel (M.toWeightedSimpleGraph hsymm hdiag).toSimpleGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (M u v ≠ 0))

instance SimpleGraph.decidableLE [Fintype V] [DecidableEq V] (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] : Decidable (G ≤ H) :=
  show Decidable (∀ ⦃v w⦄, G.Adj v w → H.Adj v w) from
    inferInstanceAs (Decidable (∀ v w, G.Adj v w → H.Adj v w))

/-! ## Export functions: graph → matrix -/

/-- The 0/1 adjacency matrix of a `Digraph V`. -/
def Digraph.adjMatrix (G : Digraph V) [DecidableRel G.Adj] : Matrix V V ℕ :=
  fun i j => if G.Adj i j then 1 else 0

/-- The weight matrix of a `WeightedDigraph V W`. -/
def WeightedDigraph.adjMatrix (G : WeightedDigraph V W) : Matrix V V W :=
  fun i j => G.weight i j

/-- The weight matrix of a `WeightedSimpleGraph V W`. -/
def WeightedSimpleGraph.adjMatrix (G : WeightedSimpleGraph V W) : Matrix V V W :=
  fun i j => G.weight s(i, j)

/-! ## Roundtrip theorems: matrix → graph → matrix = id -/

theorem Matrix.adjMatrix_toDigraph_eq (M : Matrix V V ℕ)
    (h01 : ∀ i j, M i j = 0 ∨ M i j = 1) :
    M.toDigraph.adjMatrix = M := by
  ext i j
  simp only [Digraph.adjMatrix, Matrix.toDigraph]
  rcases h01 i j with h0 | h1
  · simp [h0]
  · simp [h1]

theorem Matrix.adjMatrix_toWeightedDigraph_eq [Zero W] (M : Matrix V V W) :
    M.toWeightedDigraph.adjMatrix = M := by
  ext i j; rfl

theorem Matrix.adjMatrix_toWeightedSimpleGraph_eq [Zero W] [LinearOrder W] (M : Matrix V V W)
    (hsymm : M.IsSymm) (hdiag : ∀ x, M x x = 0) :
    (M.toWeightedSimpleGraph hsymm hdiag).adjMatrix = M := by
  ext i j
  simp [WeightedSimpleGraph.adjMatrix, Matrix.toWeightedSimpleGraph, Sym2.lift_mk]

/-! ## Subgraph constructors: matrix → subgraph -/

/-- Construct a `SimpleGraph.Subgraph` from a 0/1 subgraph matrix. -/
def SimpleGraph.subgraphOfMatrix [MulZeroOneClass α] [Nontrivial α]
    (G : SimpleGraph V) (M : Matrix V V α)
    (hAdj : M.IsAdjMatrix := by constructor <;> decide)
    (h : hAdj.toGraph ≤ G := by decide) : G.Subgraph :=
  SimpleGraph.toSubgraph hAdj.toGraph h

/-- Construct a sub-digraph from a matrix, bundled with the `≤` proof. -/
def Digraph.subgraphOfMatrix [Zero W] (G : Digraph V) (M : Matrix V V W)
    (h : M.toDigraph ≤ G := by decide) : { H : Digraph V // H ≤ G } :=
  ⟨M.toDigraph, h⟩

/-- Construct a `SimpleGraph.Subgraph` of the underlying graph of a `WeightedSimpleGraph`. -/
def WeightedSimpleGraph.subgraphOfMatrix [MulZeroOneClass α] [Nontrivial α]
    (G : WeightedSimpleGraph V W) (M : Matrix V V α)
    (hAdj : M.IsAdjMatrix := by constructor <;> decide)
    (h : hAdj.toGraph ≤ G.toSimpleGraph := by decide) : G.toSimpleGraph.Subgraph :=
  SimpleGraph.toSubgraph hAdj.toGraph h

/-- Construct a sub-digraph of the underlying `Digraph` of a `WeightedDigraph`. -/
def WeightedDigraph.subgraphOfMatrix [Zero α] (G : WeightedDigraph V W) (M : Matrix V V α)
    (h : M.toDigraph ≤ G.toDigraph := by decide) : { H : Digraph V // H ≤ G.toDigraph } :=
  ⟨M.toDigraph, h⟩

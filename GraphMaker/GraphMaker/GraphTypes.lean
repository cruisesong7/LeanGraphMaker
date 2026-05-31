import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

universe u v

/-! ## Weighted graph structures -/

/-- A weighted simple graph: an irreflexive symmetric relation with edge weights. -/
@[ext]
structure WeightedSimpleGraph (V : Type u) (W : Type v) extends SimpleGraph V where
  weight : Sym2 V → W

/-- A weighted directed graph: a relation with edge weights. -/
@[ext]
structure WeightedDigraph (V : Type u) (W : Type v) extends Digraph V where
  weight : V → V → W

/-! ## Constructors from matrices -/

namespace WeightedSimpleGraph

/-- Construct a `WeightedSimpleGraph` from a symmetric zero-diagonal matrix. -/
def ofMatrix {V : Type u} {W : Type v} [Zero W] [LinearOrder W]
    (M : Matrix V V W) (hsymm : M.IsSymm) (hdiag : ∀ x, M x x = 0) :
    WeightedSimpleGraph V W where
  Adj u v := M u v ≠ 0
  symm u v h := by
    simp only [ne_eq] at h ⊢
    rwa [show M v u = M u v from hsymm.apply u v]
  loopless := ⟨fun v => by simp [hdiag v]⟩
  weight := Sym2.lift ⟨fun u v => M u v, fun a b => by simp [hsymm.apply b a]⟩

end WeightedSimpleGraph

namespace WeightedDigraph

/-- Construct a `WeightedDigraph` from any matrix (zero entries mean no edge). -/
def ofMatrix {V : Type u} {W : Type v} [Zero W]
    (M : Matrix V V W) : WeightedDigraph V W where
  Adj u v := M u v ≠ 0
  weight u v := M u v

end WeightedDigraph

/-! ## Convenience constructors for `Fin n` over `ℕ` (used by the widget) -/

/-- Construct a `SimpleGraph (Fin n)` from a 0/1 adjacency matrix. -/
def readAdjMatrix {n : ℕ} (M : Matrix (Fin n) (Fin n) ℕ)
    (h : M.IsAdjMatrix := by decide) : SimpleGraph (Fin n) :=
  h.toGraph

/-- Construct a `Digraph (Fin n)` from an adjacency matrix. -/
def readDigraph {n : ℕ} (M : Matrix (Fin n) (Fin n) ℕ) : Digraph (Fin n) where
  Adj u v := M u v ≠ 0

/-- Construct a `WeightedSimpleGraph (Fin n) ℕ` from a symmetric weighted adjacency matrix. -/
def readWeightedAdj {n : ℕ} (M : Matrix (Fin n) (Fin n) ℕ)
    (hsymm : M.IsSymm := by decide) (hdiag : ∀ x, M x x = 0 := by decide) :
    WeightedSimpleGraph (Fin n) ℕ :=
  WeightedSimpleGraph.ofMatrix M hsymm hdiag

/-- Construct a `WeightedDigraph (Fin n) ℕ` from a weighted adjacency matrix. -/
def readWeightedDigraph {n : ℕ} (M : Matrix (Fin n) (Fin n) ℕ) :
    WeightedDigraph (Fin n) ℕ :=
  WeightedDigraph.ofMatrix M

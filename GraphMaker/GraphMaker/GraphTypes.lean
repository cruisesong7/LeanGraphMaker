import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

universe u v

@[ext]
structure WeightedSimpleGraph (V : Type u) (W : Type v) extends SimpleGraph V where
  weight : Sym2 V → W

@[reducible]
def Matrix.IsWeightedAdjMatrix {V W : Type*} [Zero W] (M : Matrix V V W) : Prop :=
  M.IsSymm ∧ ∀ x, M x x = 0

namespace WeightedSimpleGraph

def fromMatrix {V : Type u} {W : Type v} [Zero W] [LinearOrder W]
    (M : Matrix V V W) (_ : Matrix.IsWeightedAdjMatrix M) : WeightedSimpleGraph V W := {
  toSimpleGraph := SimpleGraph.fromRel (fun u v => M u v > 0)
  weight := Sym2.lift ⟨
    fun u v => max (M u v) (M v u),
    by intro a b; dsimp; exact max_comm (M a b) (M b a)
  ⟩
}

end WeightedSimpleGraph

namespace Digraph

@[ext]
structure WeightedDigraph (V : Type u) (W : Type v) extends Digraph V where
  weight : V → V → W

end Digraph

/-- Construct a `SimpleGraph (Fin n)` from a 0/1 adjacency matrix. -/
def readAdjMatrix {n : ℕ} (M : Matrix (Fin n) (Fin n) ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun u v => M u v ≠ 0)

/-- Construct a `Digraph (Fin n)` from a 0/1 adjacency matrix. -/
def readDigraph {n : ℕ} (M : Matrix (Fin n) (Fin n) ℕ) : Digraph (Fin n) :=
  { Adj := fun u v => M u v ≠ 0 }

/-- Construct a `WeightedSimpleGraph (Fin n) ℕ` from a symmetric weighted adjacency matrix. -/
def readWeightedAdj {n : ℕ} (M : Matrix (Fin n) (Fin n) ℕ)
    (h : Matrix.IsWeightedAdjMatrix M := by decide) : WeightedSimpleGraph (Fin n) ℕ :=
  WeightedSimpleGraph.fromMatrix M h

/-- Construct a `WeightedDigraph (Fin n) ℕ` from a weighted adjacency matrix. -/
def readWeightedDigraph {n : ℕ} (M : Matrix (Fin n) (Fin n) ℕ) :
    Digraph.WeightedDigraph (Fin n) ℕ :=
  { toDigraph := { Adj := fun u v => M u v ≠ 0 }
    weight := fun u v => M u v }

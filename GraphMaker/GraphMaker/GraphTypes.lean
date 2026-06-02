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

/-! ## Constructors: matrix → graph (following mathlib's `.toGraph` convention) -/

/-- Construct a `SimpleGraph V` from a 0/1 adjacency matrix. -/
def Matrix.toSimpleGraph {V : Type u} {α : Type*} [MulZeroOneClass α] [Nontrivial α]
    (M : Matrix V V α) (h : M.IsAdjMatrix := by constructor <;> decide) : SimpleGraph V :=
  h.toGraph

/-- Construct a `Digraph V` from an adjacency matrix (nonzero = edge). -/
def Matrix.toDigraph {V : Type u} {W : Type v} [Zero W]
    (M : Matrix V V W) : Digraph V where
  Adj u v := M u v ≠ 0

/-- Construct a `WeightedSimpleGraph V W` from a symmetric zero-diagonal matrix. -/
def Matrix.toWeightedSimpleGraph {V : Type u} {W : Type v} [Zero W] [LinearOrder W]
    (M : Matrix V V W) (hsymm : M.IsSymm := by decide) (hdiag : ∀ x, M x x = 0 := by decide) :
    WeightedSimpleGraph V W where
  Adj u v := M u v ≠ 0
  symm u v h := by
    simp only [ne_eq] at h ⊢
    rwa [show M v u = M u v from hsymm.apply u v]
  loopless := ⟨fun v => by simp [hdiag v]⟩
  weight := Sym2.lift ⟨fun u v => M u v, fun a b => by simp [hsymm.apply b a]⟩

/-- Construct a `WeightedDigraph V W` from a matrix (nonzero = edge). -/
def Matrix.toWeightedDigraph {V : Type u} {W : Type v} [Zero W]
    (M : Matrix V V W) : WeightedDigraph V W where
  Adj u v := M u v ≠ 0
  weight u v := M u v

/-! ## Export functions: graph → matrix -/

/-- The 0/1 adjacency matrix of a `Digraph (Fin n)`. -/
def Digraph.adjMatrix {n : ℕ} (G : Digraph (Fin n)) [DecidableRel G.Adj] :
    Matrix (Fin n) (Fin n) ℕ :=
  fun i j => if G.Adj i j then 1 else 0

/-- The weight matrix of a `WeightedDigraph (Fin n) ℕ`. -/
def WeightedDigraph.adjMatrix {n : ℕ} (G : WeightedDigraph (Fin n) ℕ) :
    Matrix (Fin n) (Fin n) ℕ :=
  fun i j => G.weight i j

/-- The weight matrix of a `WeightedSimpleGraph (Fin n) ℕ`. -/
def WeightedSimpleGraph.adjMatrix {n : ℕ} (G : WeightedSimpleGraph (Fin n) ℕ) :
    Matrix (Fin n) (Fin n) ℕ :=
  fun i j => G.weight s(i, j)

/-! ## Roundtrip theorems: matrix → graph → matrix = id -/

instance {n : ℕ} (M : Matrix (Fin n) (Fin n) ℕ) : DecidableRel (M.toDigraph).Adj := by
  unfold Matrix.toDigraph; infer_instance

/-- Roundtrip: `toDigraph` then `adjMatrix` recovers the original 0/1 matrix. -/
theorem Matrix.adjMatrix_toDigraph_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℕ)
    (h01 : ∀ i j, M i j = 0 ∨ M i j = 1) :
    M.toDigraph.adjMatrix = M := by
  ext i j
  simp only [Digraph.adjMatrix, Matrix.toDigraph]
  rcases h01 i j with h0 | h1
  · simp [h0]
  · simp [h1]

/-- Roundtrip: `toWeightedDigraph` then `adjMatrix` recovers the original matrix. -/
theorem Matrix.adjMatrix_toWeightedDigraph_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℕ) :
    M.toWeightedDigraph.adjMatrix = M := by
  ext i j
  simp [WeightedDigraph.adjMatrix, Matrix.toWeightedDigraph]

/-- Roundtrip: `toWeightedSimpleGraph` then `adjMatrix` recovers the original matrix. -/
theorem Matrix.adjMatrix_toWeightedSimpleGraph_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℕ)
    (hsymm : M.IsSymm) (hdiag : ∀ x, M x x = 0) :
    (M.toWeightedSimpleGraph hsymm hdiag).adjMatrix = M := by
  ext i j
  simp [WeightedSimpleGraph.adjMatrix, Matrix.toWeightedSimpleGraph, Sym2.lift_mk]

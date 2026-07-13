import GraphMaker.DrawGraph
import Mathlib.Combinatorics.SimpleGraph.Circulant

/-!
# Named Graphs

Standard graphs that mathlib does not define, constructed as adjacency matrices
over `Fin n` so they carry `DecidableRel` instances and can be visualized with
`draw_graph` and verified with `decide`.

`draw_graph` also renders mathlib's own decidable families directly (e.g.
`cycleGraph n`, `completeGraph`/`⊤`, `circulantGraph s`, graph complements) by
evaluating the adjacency relation — see the examples at the bottom.
-/

namespace NamedGraphs

/-- The generalized Petersen graph `GP(n, k)` on `2n` vertices: an outer `n`-cycle
    (`0..n-1`), an inner circulant (vertex `n+i` adjacent to `n+((i+k) mod n)`), and
    spokes (`i` adjacent to `n+i`). The standard Petersen graph is `petersenGraph 5 2`.

    Built via `SimpleGraph.fromRel`, which symmetrizes the relation and removes loops,
    and provides a `DecidableRel` instance for visualization/`decide`. -/
@[graph_layout "concentric"]
def petersenGraph (n k : ℕ) : SimpleGraph (Fin (2 * n)) :=
  SimpleGraph.fromRel fun u v =>
    let a := u.val; let b := v.val
    (a < n ∧ b < n ∧ (a + 1) % n = b) ∨          -- outer cycle
    (a < n ∧ b = a + n) ∨                          -- spoke
    (n ≤ a ∧ n ≤ b ∧ ((a - n) + k) % n = b - n)   -- inner circulant

/-- The wheel graph `Wₙ` on `n + 1` vertices: a hub (`0`) joined to every vertex of
    an `n`-cycle (`1..n`). -/
@[graph_layout "hub"]
def wheelGraph (n : ℕ) : SimpleGraph (Fin (n + 1)) :=
  SimpleGraph.fromRel fun u v =>
    let a := u.val; let b := v.val
    (a = 0 ∧ b ≠ 0) ∨                              -- hub → rim
    (a ≠ 0 ∧ b ≠ 0 ∧ (a % n) + 1 = b)             -- rim cycle

/-- The 3-dimensional hypercube `Q₃` on 8 vertices: vertices are 3-bit strings,
    adjacent iff they differ in exactly one bit (their XOR is a power of two). -/
@[graph_layout "cube"]
def hypercube₃ : SimpleGraph (Fin 8) :=
  SimpleGraph.fromRel fun u v =>
    let x := u.val ^^^ v.val
    x ≠ 0 ∧ (x &&& (x - 1)) = 0                    -- XOR is a power of two

end NamedGraphs

/-! ## Examples: visualization

Place the cursor on `draw_graph` (or shift-click the graph in the infoview). -/

open NamedGraphs in
example : True := by
  let G := petersenGraph 5 2   -- standard Petersen graph
  draw_graph G
  trivial

open NamedGraphs in
example : True := by
  let G := wheelGraph 5         -- W₅
  draw_graph G
  trivial

open NamedGraphs in
example : True := by
  draw_graph hypercube₃       -- Q₃
  trivial

/-! ## Examples: mathlib's decidable families render directly -/

-- Cycle graph C₅ (from mathlib's Circulant)
example : True := by
  let G := SimpleGraph.cycleGraph 5
  draw_graph G
  trivial

-- Complete graph K₄ (⊤ on Fin 4)
example : True := by
  let G : SimpleGraph (Fin 4) := ⊤
  draw_graph G
  trivial

-- Complement of the cycle C₅
example : True := by
  let G := (SimpleGraph.cycleGraph 5)ᶜ
  draw_graph G
  trivial

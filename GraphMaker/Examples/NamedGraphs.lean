import GraphMaker.DrawGraph
import Mathlib.Combinatorics.SimpleGraph.Circulant

/-!
# Named Graphs

Standard graphs that mathlib does not define, constructed as adjacency matrices
over `Fin n` so they carry `DecidableRel` instances and can be visualized with
`#view_graph` / `draw_graph` and verified with `decide`.

To *view* a graph, use the top-level `#view_graph` command — no proof context
needed. It renders mathlib's own decidable families directly too (e.g.
`cycleGraph n`, `completeGraph`/`⊤`, `circulantGraph s`, graph complements) by
evaluating the adjacency relation. Put the cursor on the command to see the
widget. Use the `draw_graph` tactic instead when you want to construct or edit a
graph inside a proof.
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

Place the cursor on a `#view_graph` command to render it in the infoview. -/

open NamedGraphs

#view_graph petersenGraph 5 2   -- standard Petersen graph
#view_graph wheelGraph 5         -- W₅
#view_graph hypercube₃           -- Q₃

/-! ## Examples: mathlib's decidable families render directly -/

#view_graph SimpleGraph.cycleGraph 5          -- cycle graph C₅
#view_graph (⊤ : SimpleGraph (Fin 4))         -- complete graph K₄
#view_graph (SimpleGraph.cycleGraph 5)ᶜ       -- complement of C₅

import VersoBlog
import GraphMaker.DrawGraph
import Mathlib.Combinatorics.SimpleGraph.Circulant
open Verso Genre Blog

set_option pp.rawOnError true

#doc (Page) "GraphMaker: Interactive Graph Theory in Lean 4" =>

Formal graph theory has a bootstrapping problem: before you can prove anything
about a concrete graph, you have to *write it down* — as an adjacency matrix, an
edge list, or a relation — and then convince Lean it is the graph you meant.
GraphMaker closes that loop with an interactive widget: draw the graph, and the
tactic writes the Lean for you. Point it the other way, and any decidable graph
renders as a picture in the infoview.

```leanInit gm
```

# Drawing graphs with `draw_graph`

Invoking the `draw_graph` tactic opens a canvas in the infoview. Click to place
vertices, click two vertices to connect them, and press *Send to Lean* — the
widget replaces the tactic invocation with a `let` binding for the graph you drew.
The result is ordinary, checkable Lean:

```lean gm
example : True := by
  let G := Matrix.toSimpleGraph !![
    0, 1, 0, 0, 1;
    1, 0, 1, 0, 0;
    0, 1, 0, 1, 0;
    0, 0, 1, 0, 1;
    1, 0, 0, 1, 0]
  trivial
```

The constructor `Matrix.toSimpleGraph` carries its well-formedness proof by
`decide`, so the resulting `SimpleGraph (Fin 5)` is kernel-checked — no trust in
the widget is required. The same canvas handles directed graphs
(`Matrix.toDigraph`), and weighted variants; walks and subgraphs selected on the
canvas are emitted as `Walk.cons … (by decide)` chains and
`subgraphOfMatrix` bindings, all closed by `decide`.

(GIF placeholder: drawing C5 on the canvas and sending it to Lean)

# Rendering any decidable graph

`draw_graph G` also works in reverse. If `G : SimpleGraph (Fin n)` has a
`DecidableRel` adjacency instance, the tactic evaluates the adjacency relation
and renders it — including graphs mathlib defines abstractly:

```lean gm
example : True := by
  let G := (SimpleGraph.cycleGraph 5)ᶜ
  draw_graph G   -- renders the complement of C₅
  trivial
```

Named graphs can register a preferred layout with an attribute; the Petersen
graph declares `@[graph_layout "concentric"]` and renders with its conventional
outer/inner rings.

# Refuting conjectures with `cex_graph`

The `cex_graph` tactic refutes false universal statements about graphs by
property-based testing (via Plausible), then *shows you* the counterexample it
found. The classic demonstration is the Ramsey lower bound R(3,3) > 5: the
5-cycle contains no triangle and no independent set of size 3, and `cex_graph`
finds it (or a graph like it) automatically, shrinks it edge-by-edge to a minimal
witness, and renders it in the infoview.

(GIF placeholder: the counterexample search finding and displaying the C5 witness)

The restriction is the same as Plausible's: the property under the quantifier
must be decidable, or you must supply a `Decidable` instance.

# Trying it live

The widget needs a running Lean server, so the canvas cannot run inside this
static page. To try it, open the repository in a Lean-enabled editor — or in a
lean4web instance with GraphMaker preloaded — and put your cursor on any
`draw_graph` in the `Examples/` directory.

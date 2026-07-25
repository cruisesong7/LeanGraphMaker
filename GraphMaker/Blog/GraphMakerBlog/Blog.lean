import VersoBlog
open Verso Genre Blog

#doc (Page) "GraphMaker" =>

GraphMaker is a Lean 4 library for *interactive graph theory*: draw a graph on a
canvas in the infoview and get a formal `SimpleGraph` back, or point the widget at
any decidable graph and see it rendered. Every artifact it produces — adjacency
matrices, walks, subgraphs — is checked by the Lean kernel via `decide`.

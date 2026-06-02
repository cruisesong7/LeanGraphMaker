import GraphMaker.DrawGraph
import Plausible

open Lean Meta Server Elab Tactic Term
open ProofWidgets
open Plausible

/-!
# `cex_graph`: random graph counterexample finder with visualization

Uses `Plausible` (property-based testing) as the backend to randomly sample
simple graphs, find counterexamples with shrinking, and display them via the
graph widget.

## Notes

The same decidability requirements as `Plausible` apply: the property under the
universal quantifier must be decidable (i.e., built from decidable relations like
`G.Adj`, boolean functions, `Fin` equality, and standard logical connectives
`∧ ∨ ¬ → ∃ ∀` over finite types). Properties involving `Nonempty`, `Set`
membership, or noncomputable definitions (e.g. `SimpleGraph.Colorable`,
`SimpleGraph.chromaticNumber`) cannot be tested directly unless supply the relevant `DecidableEq`/`DecidableRel` instances.
-/

/-! ## AdjVec: sampleable proxy for SimpleGraph (Fin n) -/

/-- A graph on `Fin n` represented as a flat Bool array (upper triangle).
    This is what Plausible samples and shrinks. -/
structure AdjVec (n : Nat) where
  entries : Array Bool
  deriving Repr

namespace AdjVec

abbrev numEntries (n : Nat) : Nat := n * (n - 1) / 2

/-- Check adjacency (symmetric by construction via min/max). -/
def getAdj (p : AdjVec n) (i j : Nat) : Bool :=
  if i == j then false
  else
    let l := min i j
    let h := max i j
    p.entries.getD (l * (2 * n - l - 1) / 2 + (h - l - 1)) false

theorem getAdj_comm {n : Nat} (p : AdjVec n) (i j : Nat) :
    p.getAdj i j = p.getAdj j i := by
  simp [getAdj, Nat.min_comm, Nat.max_comm, BEq.comm]

/-- Convert to a SimpleGraph (Fin n). -/
def toSimpleGraph (p : AdjVec n) : SimpleGraph (Fin n) where
  Adj i j := p.getAdj i.val j.val = true
  symm := fun {i j} h => by
    show p.getAdj j.val i.val = true
    rw [getAdj_comm]; exact h
  loopless := ⟨fun i => by simp [getAdj]⟩

/-- Convert to a full n×n adjacency matrix. -/
def toMatrix (p : AdjVec n) : Array (Array Nat) := Id.run do
  let mut m := Array.replicate n (Array.replicate n 0)
  let mut idx := 0
  for i in [:n] do
    for j in [i+1:n] do
      if h : idx < p.entries.size then
        if p.entries[idx] then
          m := m.modify i (·.set! j 1)
          m := m.modify j (·.set! i 1)
      idx := idx + 1
  return m

end AdjVec

instance {n : Nat} (p : AdjVec n) (i j : Fin n) :
    Decidable ((AdjVec.toSimpleGraph p).Adj i j) :=
  inferInstanceAs (Decidable (p.getAdj i.val j.val = true))

instance (n : Nat) : Shrinkable (AdjVec n) where
  shrink p :=
    (List.range p.entries.size).filterMap fun idx =>
      if h : idx < p.entries.size then
        if p.entries[idx] then some { entries := p.entries.set idx false }
        else none
      else none

instance (n : Nat) : Arbitrary (AdjVec n) where
  arbitrary := do
    let size := AdjVec.numEntries n
    let mut entries := Array.mkEmpty size
    for _ in [:size] do
      let b ← Gen.chooseAny Bool
      entries := entries.push b
    return ⟨entries⟩

/-! ## Plausible wrapper -/

/-- Run Plausible and return counterexample variable strings if found. -/
def Plausible.checkForStrings (p : Prop) [Testable p] (cfg : Configuration := {}) :
    IO (Option (List String)) := do
  match ← Testable.checkIO p cfg with
  | .failure _ xs _ => return some xs
  | _ => return none

/-! ## The cex_graph tactic -/

/-- Format a matrix as Lean `!![...]` notation. -/
private def formatMatrix (m : Array (Array Nat)) : String :=
  let rows := m.map fun row =>
    String.intercalate ", " (row.toList.map toString)
  "!![" ++ String.intercalate ";\n    " rows.toList ++ "]"

/-- Parse Plausible's counterexample output to extract the adjacency matrix.
    Output format: `"G := { entries := #[true, false, true] }"` -/
private def parseCounterexample (strs : List String) (n : Nat) :
    Option (Array (Array Nat)) := Id.run do
  for s in strs do
    let parts := s.splitOn "#["
    if parts.length < 2 then continue
    let rest := (parts[1]!.splitOn "]").head!
    let boolStrs := rest.splitOn ","
    let bools := boolStrs.map fun b => decide ((b.splitOn "true").length > 1)
    let proxy : AdjVec n := ⟨bools.toArray⟩
    return some proxy.toMatrix
  return none

syntax (name := cexGraphTac) "cex_graph" : tactic

@[tactic cexGraphTac] def cexGraph : Tactic := fun stx => do
  let fm ← getFileMap
  let some replaceRange := lspRangeOfStx? fm stx false | return

  -- Read the goal: expect `∀ G : SimpleGraph (Fin n), P G`
  let goal ← getMainGoal
  let goalType ← goal.getType
  let goalType ← instantiateMVars goalType
  unless goalType.isForall do
    throwError "cex_graph: goal must be of the form `∀ G : SimpleGraph (Fin n), P G`"

  let domainType := goalType.bindingDomain!
  -- Extract n from `SimpleGraph (Fin n)`
  let fn := domainType.getAppFn
  let args := domainType.getAppArgs
  unless fn.isConstOf ``SimpleGraph && args.size == 1 do
    throwError "cex_graph: goal must quantify over `SimpleGraph (Fin n)` for a concrete `n`"
  let finExpr := args[0]!
  unless finExpr.getAppFn.isConstOf ``Fin do
    throwError "cex_graph: goal must quantify over `SimpleGraph (Fin n)` for a concrete `n`"
  let nExpr ← whnf finExpr.getAppArgs[0]!
  let n ← match nExpr.rawNatLit? with
    | some v => pure v
    | none => throwError "cex_graph: could not determine `n` from the goal (must be a literal)"

  -- Build the proxy proposition: ∀ p : AdjVec n, P (AdjVec.toSimpleGraph p)
  -- We substitute the proxy graph, then synthesize any trailing instance binders
  -- (e.g. [DecidableRel G.Adj]) against the concrete proxy type.
  let proxyType := mkApp (Lean.mkConst ``AdjVec) (mkNatLit n)
  let toGraph := mkApp (Lean.mkConst ``AdjVec.toSimpleGraph) (mkNatLit n)

  let prop ← withLocalDeclD `p proxyType fun p => do
    let graphExpr := mkApp toGraph p
    let mut body := goalType.bindingBody!.instantiate1 graphExpr
    -- Strip instance binders (e.g. [DecidableRel G.Adj]), synthesizing against the proxy graph
    let mut done := false
    while !done do
      match body with
      | .forallE _ instType restBody .instImplicit =>
        let instOpt ← try pure (some (← synthInstance instType)) catch _ => pure none
        match instOpt with
        | some inst => body := restBody.instantiate1 inst
        | none => done := true
      | _ => done := true
    mkForallFVars #[p] body
  let prop ← instantiateMVars prop

  -- Decorate for Plausible's NamedBinder pattern
  let prop' ← Decorations.addDecorations prop
  let testableInst ← try
    synthInstance (← mkAppM ``Testable #[prop'])
  catch e => throwError
    "cex_graph: failed to synthesize `Testable` instance.\n\
     Make sure the predicate is decidable.\n{← e.toMessageData.format}"

  let cfg : Configuration := { numInst := 200 }
  let checkExpr ← mkAppOptM ``Plausible.checkForStrings
    #[prop', testableInst, toExpr cfg]
  let resultType := mkApp (Lean.mkConst ``IO)
    (mkApp (Lean.mkConst ``Option [.zero])
      (mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``String)))

  -- Natively evaluate the plausible check (fast, with shrinking!)
  let ioAction ← unsafe evalExpr (IO (Option (List String))) resultType checkExpr
  let result ← ioAction

  match result with
  | none =>
    logWarning s!"cex_graph: no counterexample found (n = {n})"
    admitGoal (← getMainGoal)
  | some counterStrs =>
    let mat := (parseCounterexample counterStrs n).getD #[]
    if mat.size == 0 then
      logInfo s!"Found counterexample but could not parse:\n{counterStrs}"
      admitGoal (← getMainGoal)
    else
      let matStr := formatMatrix mat
      showGraphWidget stx replaceRange mat
      logInfo s!"Found counterexample!\n  let G := Matrix.toSimpleGraph {matStr}"
      admitGoal (← getMainGoal)

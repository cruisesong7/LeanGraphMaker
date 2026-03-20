import FormalRamsey.RamseyGraphs
import GraphMaker.DrawGraph

theorem R33 : ¬(RamseyGraphProp 5 3 3) := by
  simp only [RamseyGraphProp, not_forall]
  let G := readG6 "DeS"
  use G
  simp [not_or]
  apply And.intro
  · intros S
    rw [← SimpleGraph.mem_cliqueFinset_iff]
    have cliqueFree : (readG6 "DeS").cliqueFinset 3 = Finset.empty := by native_decide
    rw [cliqueFree]
    exact Finset.notMem_empty S
  · intros T
    rw [← SimpleGraph.mem_indepSetFinset_iff]
    have cliqueFree : (readG6 "GhdGKC").indepSetFinset 3 = Finset.empty := by native_decide
    rw [cliqueFree]
    exact Finset.notMem_empty T

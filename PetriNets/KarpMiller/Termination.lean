/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.KarpMiller.LTS
import PetriNets.CoveringGraph.Finiteness
public import Mathlib.Data.FinEnum

/-!
# Termination of Karp–Miller DFS branches

Provides termination of the Karp–Miller DFS. Each DFS step translates to
a covering-LTS step with the same marking and history. Since the covering
LTS has no infinite execution, the DFS recursive-call relation is well-founded.

## References

* W. Reisig, *Understanding Petri Nets: Modeling Techniques, Analysis Methods,
  Case Studies*, Springer, 2013, Chapter 14.
  DOI: 10.1007/978-3-642-33278-4.
-/

@[expose] public section

namespace PetriNet

namespace KarpMiller

variable {P T : Type*}
variable {net : WeightedNet P T}

section FinitePlaces

variable [FinEnum P] [FinEnum T]

/-- One recursive call follows an edge in the executable successor list.
The child comes first in the well-founded relation. -/
def DfsCall (net : WeightedNet P T)
    (next current : Branch P) : Prop :=
  ∃ t, (t, next) ∈ successors net current

/-- An infinite chain of recursive calls would give an infinite covering-LTS
execution. -/
theorem dfsCall_wellFounded : WellFounded (DfsCall net) := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  constructor
  rintro ⟨nodes, hchildren⟩
  apply CoveringGraph.no_OmegaExecution (net := net)
    (nodes := fun n => nodeOfBranch (nodes n))
    (labels := fun n => Classical.choose (hchildren n))
  intro n
  exact mem_successors_iff_coveringLTS_tr.mp (Classical.choose_spec (hchildren n))

end FinitePlaces

end KarpMiller

end PetriNet

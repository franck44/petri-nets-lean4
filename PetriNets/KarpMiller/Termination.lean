/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.KarpMiller.LTS
import PetriNets.CoveringGraphV2.Finiteness
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

/-- Every infinite DFS execution would translate to an infinite covering-LTS
execution with the same labels, which covering-LTS finiteness rules out. -/
theorem not_omegaExecution
    {nodes : Cslib.ωSequence (Branch P)}
    {labels : Cslib.ωSequence T} :
    ¬ (dfsLTS net).OmegaExecution nodes labels := by
  intro hexec
  let toNode (b : Branch P) : CoveringGraphV2.Node P :=
    ⟨b.marking, b.ancestors⟩
  apply CoveringGraphV2.no_OmegaExecution (net := net)
    (nodes := fun n => toNode (nodes n)) (labels := labels)
  intro n
  obtain ⟨hfirst, henabled, hnext⟩ := mem_dfsSuccessors_iff.mp (hexec n)
  exact CoveringGraphV2.coveringLTS_tr_iff.mpr
    ⟨hfirst, henabled, (congrArg toNode hnext).symm⟩

/-- `DfsCall net next current` means that computing the Karp–Miller DFS at
`current` makes an immediate recursive call at `next`.

Such a call occurs exactly when `dfsLTS net` has a transition from `current`
to `next`, with some label. The recursive argument is placed first so that
`DfsCall net` has the orientation expected of a well-founded relation:
`next` is smaller than `current`. -/
def DfsCall (net : WeightedNet P T)
    (next current : Branch P) : Prop :=
  ∃ t, (dfsLTS net).Tr current t next

/-- The recursive-call relation of the Karp–Miller DFS is well-founded.

An infinite descending chain for `DfsCall net` would select a transition
label at every position and therefore form an infinite execution of
`dfsLTS net`, contradicting `not_omegaExecution`. -/
theorem dfsCall_wellFounded : WellFounded (DfsCall net) := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  constructor
  rintro ⟨nodes, hchildren⟩
  let nodeSequence : Cslib.ωSequence (Branch P) := nodes
  let labels : Cslib.ωSequence T := fun n =>
    Classical.choose (hchildren n)
  apply not_omegaExecution (nodes := nodeSequence) (labels := labels)
  intro n
  change (dfsLTS net).Tr (nodes n) (Classical.choose (hchildren n))
    (nodes (n + 1))
  exact Classical.choose_spec (hchildren n)

end FinitePlaces

end KarpMiller

end PetriNet

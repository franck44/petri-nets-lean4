/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.CoveringGraph.Completeness
public import PetriNets.CoveringGraph.Soundness
public import PetriNets.MarkingGraph.Properties

/-!
# Dead transitions in the covering LTS

Provides a characterisation of dead transitions by enabledness at reachable
covering-LTS nodes.
-/

public section

namespace PetriNet.CoveringGraph

variable {P T : Type*} [FinEnum P]

/-- A transition is dead from `m₀` exactly when no reachable covering-LTS node
enables it. Completeness lifts concrete enabledness to a covering node.
Soundness gives a reachable cover of the transition's input marking whenever
a covering node enables it. -/
theorem transitionDeadFrom_iff_no_enabled_covering_node
    (net : WeightedNet P T) (m₀ : Marking P) (t : T) :
    net.TransitionDeadFrom m₀ t ↔
      ¬ ∃ node, (coveringLTS net).CanReach (Node.initial m₀) node ∧
        net.OmegaEnabled node.marking t := by
  constructor
  · rintro hdead ⟨node, hnode, henabled⟩
    let input : Marking P := fun p => net.pre p t
    have hcoverable :=
      omegaCoverableFrom_of_coveringLTS_canReach hnode input henabled
    obtain ⟨reached, hreach, hcover⟩ := hcoverable
    exact hdead reached hreach hcover
  · intro hnone m hreach henabled
    obtain ⟨label, hnode, hcover⟩ := coveringLTS_covers_of_reachable net hreach
    exact hnone ⟨label, hnode, fun p =>
      (ENat.natCast_le_natCast.mpr (henabled p)).trans (hcover p)⟩

end PetriNet.CoveringGraph

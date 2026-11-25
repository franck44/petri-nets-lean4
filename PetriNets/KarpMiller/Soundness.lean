/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.KarpMiller
import PetriNets.CoveringGraphV2.Soundness

/-!
# Soundness of the Karp–Miller construction

Provides soundness of the executable Karp–Miller tree. Every concrete
marking below a tree label is coverable from the initial marking. The
marking equivalence transfers soundness from the covering LTS to the tree.
-/

@[expose] public section

namespace PetriNet

namespace KarpMiller

variable {P T : Type*}

/-- **Soundness of the Karp–Miller tree.** Every ω-marking stored in the tree
generated from `m₀` is omega coverable from `m₀`.

The marking equivalence supplies a reachable covering-LTS node carrying
the stored marking, and covering-LTS soundness gives its coverability. -/
theorem karpMillerDFS_omegaCoverableFrom_of_hasNode
    [FinEnum P] [FinEnum T] (net : WeightedNet P T) (m₀ : Marking P)
    {mω : OmegaMarking P}
    (hnode :
      (karpMillerDFS net (Branch.initial m₀)).HasNode mω) :
    net.OmegaCoverableFrom m₀ mω := by
  obtain ⟨node, hreach, hmarking⟩ :=
    (karpMillerDFS_hasNode_iff_exists_coveringLTS_canReach net m₀ mω).mp hnode
  rw [← hmarking]
  exact CoveringGraphV2.omegaCoverableFrom_of_coveringLTS_canReach hreach

end KarpMiller

end PetriNet

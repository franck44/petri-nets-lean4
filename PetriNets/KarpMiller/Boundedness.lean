/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.KarpMiller.Finiteness
public import PetriNets.KarpMiller.Tree
public import PetriNets.CoveringGraph.Boundedness

/-!
# Deciding place boundedness

Provides an executable decision for place boundedness by collecting the
Karp–Miller tree markings and checking for ω at the given place.
-/

public section

namespace PetriNet

/-- Decide boundedness at `p` by checking the list of Karp–Miller node markings
for ω at that place. -/
def WeightedNet.decidablePlaceBoundedFrom {P T : Type*} [FinEnum P] [FinEnum T]
    (net : WeightedNet P T) (m₀ : Marking P) (p : P) :
    Decidable (net.PlaceBoundedFrom m₀ p) :=
  let tree := KarpMiller.karpMillerDFS net (KarpMiller.Branch.initial m₀)
  decidable_of_iff (¬ tree.collectNodes.any (fun m => decide (m p = ⊤)) = true) (by
    classical
    have hplace : net.PlaceUnboundedFrom m₀ p ↔
        ∃ m, tree.HasNode m ∧ m p = ⊤ := by
      rw [CoveringGraph.placeUnboundedFrom_iff_exists_omega (net := net) m₀ p]
      simp only [tree, KarpMiller.karpMillerDFS_hasNode_iff_exists_coveringLTS_canReach]
      aesop
    simp only [List.any_eq_true, decide_eq_true_eq, KarpMiller.KarpMillerTree.mem_collectNodes_iff]
    rw [← hplace, net.placeUnboundedFrom_iff_not_placeBoundedFrom, not_not])

end PetriNet

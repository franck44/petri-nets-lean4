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
# Place boundedness and simultaneous unboundedness

Provides a tree characterisation of simultaneous unboundedness and an
executable decision for boundedness at a single place.
-/

public section

namespace PetriNet

open KarpMiller

variable {P T : Type*} [FinEnum P] [FinEnum T]

/-- A set of places is simultaneously unbounded exactly when one Karp–Miller
tree marking has ω at every place in the set. -/
theorem WeightedNet.simultaneouslyUnboundedFrom_iff_exists_tree_marking
    (net : WeightedNet P T) (m₀ : Marking P) (places : Set P) :
    net.SimultaneouslyUnboundedFrom m₀ places ↔
      ∃ label, (karpMillerDFS net (Branch.initial m₀)).HasNode label ∧
        ∀ p ∈ places, label p = ⊤ := by
  rw [CoveringGraph.simultaneouslyUnboundedFrom_iff_exists_omega (net := net) m₀ places]
  simp only [karpMillerDFS_hasNode_iff_exists_coveringLTS_canReach]
  aesop

/-- Decide boundedness at `p` by checking the list of Karp–Miller node markings
for ω at that place. -/
def WeightedNet.decidablePlaceBoundedFrom
    (net : WeightedNet P T) (m₀ : Marking P) (p : P) :
    Decidable (net.PlaceBoundedFrom m₀ p) :=
  let tree := KarpMiller.karpMillerDFS net (KarpMiller.Branch.initial m₀)
  decidable_of_iff (¬ tree.collectNodes.any (fun m => decide (m p = ⊤)) = true) (by
    classical
    have hplace : net.PlaceUnboundedFrom m₀ p ↔
        ∃ m, tree.HasNode m ∧ m p = ⊤ := by
      simpa [tree, WeightedNet.simultaneouslyUnboundedFrom_singleton] using
        net.simultaneouslyUnboundedFrom_iff_exists_tree_marking m₀ ({p} : Set P)
    simp only [List.any_eq_true, decide_eq_true_eq, KarpMiller.KarpMillerTree.mem_collectNodes_iff]
    rw [← hplace, net.placeUnboundedFrom_iff_not_placeBoundedFrom, not_not])

end PetriNet

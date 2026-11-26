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

Provides executable decisions for place boundedness, simultaneous
unboundedness, and finiteness of the reachable markings using the
Karp–Miller tree.
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

/-- Decide whether the places in `places` can all accumulate arbitrarily
many tokens together. Search for one tree marking with ω at every given place. -/
def WeightedNet.decidableSimultaneouslyUnboundedFrom
    (net : WeightedNet P T) (m₀ : Marking P) (places : Finset P) :
    Decidable (net.SimultaneouslyUnboundedFrom m₀ (places : Set P)) :=
  let tree := karpMillerDFS net (Branch.initial m₀)
  decidable_of_iff
    (tree.collectNodes.any (fun m => decide (∀ p ∈ places, m p = ⊤)) = true) (by
      simp only [List.any_eq_true, decide_eq_true_eq,
        KarpMillerTree.mem_collectNodes_iff]
      exact (net.simultaneouslyUnboundedFrom_iff_exists_tree_marking
        m₀ (places : Set P)).symm)

/-- Decide boundedness at `p` by checking the list of Karp–Miller node markings
for ω at that place. -/
def WeightedNet.decidablePlaceBoundedFrom
    (net : WeightedNet P T) (m₀ : Marking P) (p : P) :
    Decidable (net.PlaceBoundedFrom m₀ p) :=
  letI := net.decidableSimultaneouslyUnboundedFrom m₀ ({p} : Finset P)
  decidable_of_iff (¬ net.SimultaneouslyUnboundedFrom m₀ (({p} : Finset P) : Set P)) (by
    classical
    simp only [Finset.coe_singleton, WeightedNet.simultaneouslyUnboundedFrom_singleton,
      net.placeUnboundedFrom_iff_not_placeBoundedFrom, not_not])

/-- Decide whether finitely many markings are reachable from `m₀` by
searching the Karp–Miller tree for a marking that contains ω. -/
def WeightedNet.decidableFiniteReachable
    (net : WeightedNet P T) (m₀ : Marking P) :
    Decidable (Finite {m : Marking P // net.Reachable m₀ m}) :=
  let tree := karpMillerDFS net (Branch.initial m₀)
  decidable_of_iff
    (¬ tree.collectNodes.any (fun m => decide (∃ p, m p = ⊤)) = true) (by
      simp only [List.any_eq_true, decide_eq_true_eq, KarpMillerTree.mem_collectNodes_iff]
      rw [CoveringGraph.finite_reachable_iff_no_omega (net := net) m₀]
      simp only [tree, karpMillerDFS_hasNode_iff_exists_coveringLTS_canReach]
      aesop)

end PetriNet

/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.KarpMiller.Tree
public import PetriNets.CoveringGraph.TransitionDead

/-!
# Deciding whether a transition is dead

Provides an executable decision that checks whether the transition is enabled
at any marking in the Karp–Miller tree.
-/

public section

namespace PetriNet

open KarpMiller

variable {P T : Type*} [FinEnum P] [FinEnum T]

/-- A transition is dead from `m₀` exactly when no Karp–Miller tree marking
enables it. -/
theorem WeightedNet.transitionDeadFrom_iff_no_enabled_tree_marking
    (net : WeightedNet P T) (m₀ : Marking P) (t : T) :
    net.TransitionDeadFrom m₀ t ↔
      ¬ ∃ m, (karpMillerDFS net (Branch.initial m₀)).HasNode m ∧
        net.OmegaEnabled m t := by
  rw [CoveringGraph.transitionDeadFrom_iff_no_enabled_covering_node net m₀ t]
  simp only [karpMillerDFS_hasNode_iff_exists_coveringLTS_canReach]
  aesop

/-- Decide whether `t` is dead from `m₀` by searching the collected tree
markings for one that enables `t`. -/
def WeightedNet.decidableTransitionDeadFrom
    (net : WeightedNet P T) (m₀ : Marking P) (t : T) :
    Decidable (net.TransitionDeadFrom m₀ t) :=
  let tree := karpMillerDFS net (Branch.initial m₀)
  decidable_of_iff
    (¬ tree.collectNodes.any (fun m => decide (∀ p, (net.pre p t : ℕ∞) ≤ m p)) = true) (by
      simp only [List.any_eq_true, decide_eq_true_eq, KarpMillerTree.mem_collectNodes_iff]
      exact (net.transitionDeadFrom_iff_no_enabled_tree_marking m₀ t).symm)

end PetriNet

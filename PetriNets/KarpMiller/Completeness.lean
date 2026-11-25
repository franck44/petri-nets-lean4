/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.KarpMiller
import PetriNets.CoveringGraphV2.Completeness

/-!
# Completeness of the Karp–Miller construction

Provides completeness of the executable Karp–Miller tree. Every reachable
concrete marking is covered by a tree label. Covering-LTS completeness
supplies the label, and the marking equivalence puts it in the tree.
-/

@[expose] public section

namespace PetriNet.KarpMiller

variable {P T : Type*}
variable [FinEnum P] [FinEnum T]
variable (net : WeightedNet P T)

/-- **Karp–Miller over-approximation for reachability.**

For every marking `tgt` reachable from `m₀`, there exists an ω-marking `mω` occurring in the
finite Karp–Miller tree such that `tgt ≤ mω`.
Covering-LTS completeness supplies a covering marking and the marking
equivalence puts it in the tree. -/
theorem karpMillerDFS_covers_of_reachable
    {m₀ tgt : Marking P}
    (hreach : net.Reachable m₀ tgt) :
    ∃ mω,
      (karpMillerDFS net (Branch.initial m₀)).HasNode mω ∧
      tgt ≤ mω := by
  obtain ⟨node, hnode, hcover⟩ := CoveringGraphV2.coveringLTS_covers_of_reachable net hreach
  exact ⟨node.marking,
    (karpMillerDFS_hasNode_iff_exists_coveringLTS_canReach net m₀ node.marking).mpr
      ⟨node, hnode, rfl⟩, hcover⟩

end PetriNet.KarpMiller

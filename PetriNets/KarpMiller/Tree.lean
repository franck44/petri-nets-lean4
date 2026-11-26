/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.KarpMiller

/-!
# Traversing Karp–Miller trees

Provides a list of the node markings and relates list membership to `HasNode`.
-/

public section

namespace PetriNet.KarpMiller

variable {P T : Type*}

/-- Collect the root marking, followed by the markings of each child subtree
in child-list order. Each node contributes one entry. -/
def KarpMillerTree.collectNodes (tree : KarpMillerTree P T) : List (OmegaMarking P) :=
  match tree with
  | .node root children =>
    root :: children.attach.flatMap (fun child => child.val.2.collectNodes)
termination_by sizeOf tree
decreasing_by
  obtain ⟨⟨t, subtree⟩, hmem⟩ := child
  have hchild := List.sizeOf_lt_of_mem hmem
  simp_wf
  simp at hchild
  omega

/-- A marking is in the collected list exactly when it labels a tree node. -/
theorem KarpMillerTree.mem_collectNodes_iff (m : OmegaMarking P)
    (tree : KarpMillerTree P T) : m ∈ tree.collectNodes ↔ tree.HasNode m := by
  cases tree with
  | node root children =>
    have hnode : (KarpMillerTree.node root children).HasNode m ↔
        m = root ∨ ∃ child ∈ children, child.2.HasNode m := by
      constructor
      · intro hm
        cases hm with
        | root => exact Or.inl rfl
        | child hc hn => exact Or.inr ⟨_, hc, hn⟩
      · rintro (rfl | ⟨child, hc, hm⟩)
        · exact .root
        · exact .child hc hm
    rw [KarpMillerTree.collectNodes.eq_1, List.mem_cons, List.mem_flatMap, hnode]
    apply or_congr_right
    constructor
    · rintro ⟨child, _, hm⟩
      exact ⟨child.val, child.property, (mem_collectNodes_iff m child.val.2).mp hm⟩
    · rintro ⟨child, hc, hm⟩
      exact ⟨⟨child, hc⟩, List.mem_attach .., (mem_collectNodes_iff m child.2).mpr hm⟩
termination_by sizeOf tree
decreasing_by all_goals
  first | have h := List.sizeOf_lt_of_mem child.property; obtain ⟨⟨_, _⟩, _⟩ := child
        | have h := List.sizeOf_lt_of_mem hc; cases child
  simp_wf
  simp at h
  omega

end PetriNet.KarpMiller

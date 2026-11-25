/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.KarpMiller.Successor
public import PetriNets.CoveringGraph.LTS

/-!
# Karp–Miller successor enumeration

Provides the executable successor list and its correspondence with the
covering LTS.
-/

@[expose] public section

namespace PetriNet

namespace KarpMiller

variable {P T : Type*}
variable {net : WeightedNet P T}

section FinitePlaces

variable [FinEnum P] [FinEnum T]

/-! ## Executable DFS transitions -/

/-- Compute the labelled successor branches explored by the Karp–Miller DFS.

The first-occurrence check belongs to the DFS algorithm. For a
first-occurrence branch, `succMarkings` enumerates the enabled transitions and their successor
markings; `succBranch` then accelerates each marking with respect to the branch
history and extends the branch. A branch that is not a first occurrence has no DFS
successors. -/
def successors (net : WeightedNet P T) (src : Branch P) :
    List (T × Branch P) :=
  if src.marking ∈ src.ancestors then []
  else
    (succMarkings net src.marking).map fun candidate =>
      (candidate.1, succBranch net src candidate.1)

/-- Membership in `successors` is characterised by first-occurrence
status, enabledness, and construction of the target branch. -/
theorem mem_successors_iff {src tgt : Branch P} {t : T} :
    (t, tgt) ∈ successors net src ↔
      src.IsFirstOccurrence ∧ net.OmegaEnabled src.marking t ∧
        succBranch net src t = tgt := by
  constructor
  · intro h
    unfold successors at h
    split at h
    · simp at h
    · rename_i hfirst
      simp only [List.mem_map] at h
      obtain ⟨candidate, hcandidate, hpair⟩ := h
      rcases candidate with ⟨u, m⟩
      simp only at hpair
      obtain ⟨rfl, rfl⟩ := hpair
      have henabled :=
        (enabled_and_eq_of_mem_succMarkings hcandidate).1
      exact ⟨by simpa [Branch.IsFirstOccurrence], henabled, rfl⟩
  · rintro ⟨hfirst, henabled, rfl⟩
    have hnotmem : src.marking ∉ src.ancestors := hfirst
    unfold successors
    simp only [hnotmem, ↓reduceIte, List.mem_map]
    refine ⟨(t, succMarking net src.marking t),
      mem_succMarkings_of_enabled henabled, ?_⟩
    simp

/-- View a branch as a covering node with the same marking and history. -/
def nodeOfBranch (branch : Branch P) : CoveringGraph.Node P :=
  ⟨branch.marking, branch.ancestors⟩

/-- View a covering node as a branch with the same marking and history. -/
def branchOfNode (node : CoveringGraph.Node P) : Branch P :=
  ⟨node.marking, node.ancestors⟩

/-- The executable successor list enumerates exactly the covering edges. -/
theorem mem_successors_iff_coveringLTS_tr {src tgt : Branch P} {t : T} :
    (t, tgt) ∈ successors net src ↔
      (CoveringGraph.coveringLTS net).Tr (nodeOfBranch src) t (nodeOfBranch tgt) := by
  rw [mem_successors_iff, CoveringGraph.coveringLTS_tr_iff]
  constructor
  · rintro ⟨hfirst, henabled, rfl⟩
    exact ⟨hfirst, henabled, rfl⟩
  · rintro ⟨hfirst, henabled, heq⟩
    exact ⟨hfirst, henabled, (congrArg branchOfNode heq).symm⟩

end FinitePlaces

end KarpMiller

end PetriNet

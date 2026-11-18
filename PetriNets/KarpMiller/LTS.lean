/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.KarpMiller.Successor

/-!
# The Karp–Miller DFS transition system

This module defines the executable successor list explored by the
Karp–Miller DFS and exposes that list as a labelled transition system. A DFS
edge is exactly membership in the computed successor list, so openness and
enabledness have a single executable source of truth.
-/

@[expose] public section

namespace PetriNet

namespace KarpMiller

variable {P T : Type*}
variable {net : WeightedNet P T}

section FinitePlaces

variable [FinEnum P] [FinEnum T]

/-- Compute the labelled successor branches explored by the Karp–Miller DFS.

The openness check belongs to the DFS algorithm. For an open branch,
`succMarkings` enumerates the enabled transitions and their successor
markings; `succBranch` then accelerates each marking with respect to the branch
history and extends the branch. A branch that is not open has no DFS
successors. -/
def dfsSuccessors (net : WeightedNet P T) (src : Branch P) :
    List (T × Branch P) :=
  if src.marking ∈ src.ancestors then []
  else
    (succMarkings net src.marking).map fun candidate =>
      (candidate.1, succBranch net src candidate.1)

/-- Membership in `dfsSuccessors` is characterised by openness, enabledness,
and construction of the target branch. -/
theorem mem_dfsSuccessors_iff {src tgt : Branch P} {t : T} :
    (t, tgt) ∈ dfsSuccessors net src ↔
      src.IsOpen ∧ net.OmegaEnabled src.marking t ∧
        succBranch net src t = tgt := by
  constructor
  · intro h
    unfold dfsSuccessors at h
    split at h
    · simp at h
    · rename_i hopen
      simp only [List.mem_map] at h
      obtain ⟨candidate, hcandidate, hpair⟩ := h
      rcases candidate with ⟨u, m⟩
      simp only at hpair
      obtain ⟨rfl, rfl⟩ := hpair
      have henabled :=
        (enabled_and_eq_of_mem_succMarkings hcandidate).1
      exact ⟨by simpa [Branch.IsOpen], henabled, rfl⟩
  · rintro ⟨hopen, henabled, rfl⟩
    have hnotmem : src.marking ∉ src.ancestors := hopen
    unfold dfsSuccessors
    simp only [hnotmem, ↓reduceIte, List.mem_map]
    refine ⟨(t, succMarking net src.marking t),
      mem_succMarkings_of_enabled henabled, ?_⟩
    simp

/-- The labelled transition system explored by the Karp–Miller DFS. -/
def dfsLTS (net : WeightedNet P T) : Cslib.LTS (Branch P) T where
  Tr src t tgt := (t, tgt) ∈ dfsSuccessors net src

/-- A DFS edge is exactly membership in the computed successor list. -/
theorem dfsLTS_tr_iff {src tgt : Branch P} {t : T} :
    (dfsLTS net).Tr src t tgt ↔ (t, tgt) ∈ dfsSuccessors net src :=
  Iff.rfl

/-- Along a DFS edge, the set of places equal to `ω` can only grow. -/
theorem omegaPlaces_mono_of_tr {src tgt : Branch P} {t : T}
    (htr : (dfsLTS net).Tr src t tgt) :
    OmegaMarking.omegaPlaces src.marking ⊆
      OmegaMarking.omegaPlaces tgt.marking := by
  change (t, tgt) ∈ dfsSuccessors net src at htr
  rw [mem_dfsSuccessors_iff] at htr
  rw [← htr.2.2]
  exact omegaPlaces_mono_of_succBranch src t

/-- The Karp–Miller DFS LTS is deterministic. Registering this fact as an
instance allows CSLib results for deterministic LTSs to apply directly. -/
instance (net : WeightedNet P T) :
    (dfsLTS net).Deterministic := by
  constructor
  intro src t tgt₁ tgt₂ h₁ h₂
  change (t, tgt₁) ∈ dfsSuccessors net src at h₁
  change (t, tgt₂) ∈ dfsSuccessors net src at h₂
  rw [mem_dfsSuccessors_iff] at h₁ h₂
  exact h₁.2.2.symm.trans h₂.2.2

/-- A branch has no DFS successor exactly when it is not open or its current
marking enables no transition. -/
theorem no_tr_iff_not_open_or_terminal {src : Branch P} :
    (∀ t tgt, ¬ (dfsLTS net).Tr src t tgt) ↔
      ¬ src.IsOpen ∨ ∀ t, ¬ net.OmegaEnabled src.marking t := by
  classical
  by_cases hopen : src.IsOpen <;>
    simp [dfsLTS, mem_dfsSuccessors_iff, hopen]

end FinitePlaces

end KarpMiller

end PetriNet


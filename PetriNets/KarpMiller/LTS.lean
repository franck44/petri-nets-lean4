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

/-- Along a finite Karp–Miller execution, the set of places equal to `ω` can
only grow. This extends `omegaPlaces_mono_of_tr` from one transition to a
sequence of transitions. -/
theorem omegaPlaces_mono_of_mTr {src tgt : Branch P} {labels : List T}
    (hexec : (dfsLTS net).MTr src labels tgt) :
    OmegaMarking.omegaPlaces src.marking ⊆
      OmegaMarking.omegaPlaces tgt.marking := by
  induction hexec with
  | refl => exact Finset.Subset.rfl
  | stepL htr _ ih =>
      exact (omegaPlaces_mono_of_tr htr).trans ih

/-- If the source and target of a finite Karp–Miller execution have the same
set of `ω`-places, then every intermediate branch has that same set.

Here `mid` is any intermediate branch, witnessed by an execution from `src`
to `mid` followed by an execution from `mid` to `tgt`. Monotonicity gives
`omegaPlaces src ⊆ omegaPlaces mid ⊆ omegaPlaces tgt`; equality of the
endpoint sets therefore forces equality at `mid`. -/
theorem omegaPlaces_eq_of_between_mTr
    {src mid tgt : Branch P} {left right : List T}
    (hleft : (dfsLTS net).MTr src left mid)
    (hright : (dfsLTS net).MTr mid right tgt)
    (homega : OmegaMarking.omegaPlaces src.marking =
      OmegaMarking.omegaPlaces tgt.marking) :
    OmegaMarking.omegaPlaces mid.marking =
      OmegaMarking.omegaPlaces tgt.marking := by
  apply Finset.Subset.antisymm
  · exact omegaPlaces_mono_of_mTr hright
  · intro p hp
    rw [← homega] at hp
    exact omegaPlaces_mono_of_mTr hleft hp

/-- Along an infinite Karp–Miller execution, the set of places equal to `ω`
can only grow. This extends `omegaPlaces_mono_of_mTr` from finite executions
to finite prefixes of an infinite execution. -/
theorem omegaPlaces_mono_of_omegaExecution {nodes : Cslib.ωSequence (Branch P)}
    {labels : Cslib.ωSequence T}
    (hexec : (dfsLTS net).OmegaExecution nodes labels)
    {i j : ℕ} (hij : i ≤ j) :
    OmegaMarking.omegaPlaces (nodes i).marking ⊆
      OmegaMarking.omegaPlaces (nodes j).marking := by
  exact omegaPlaces_mono_of_mTr (hexec.extract_mTr hij)

/-- If a DFS step introduces no new `ω`-place, its target marking is the
unaccelerated successor marking. -/
theorem marking_eq_succMarking_of_tr_of_omegaPlaces_eq
    {src tgt : Branch P} {t : T}
    (htr : (dfsLTS net).Tr src t tgt)
    (homega : OmegaMarking.omegaPlaces src.marking =
      OmegaMarking.omegaPlaces tgt.marking) :
    tgt.marking = succMarking net src.marking t := by
  obtain ⟨_, _, rfl⟩ := mem_dfsSuccessors_iff.mp htr
  exact succBranch_marking_eq_succMarking_of_omegaPlaces_eq src t homega

/-- A Karp–Miller DFS step preserves every existing ancestor of the source
branch in the target branch. -/
theorem ancestors_mono_of_tr {src tgt : Branch P} {t : T}
    (htr : (dfsLTS net).Tr src t tgt) :
    src.ancestors ⊆ tgt.ancestors := by
  obtain ⟨_, _, rfl⟩ := mem_dfsSuccessors_iff.mp htr
  simp [succBranch, Branch.history]

/-- Along a finite Karp–Miller execution, every ancestor of the initial branch
remains an ancestor of the final branch. This extends `ancestors_mono_of_tr`
from one transition to a sequence of transitions. -/
theorem ancestors_mono_of_mTr {src tgt : Branch P} {labels : List T}
    (hexec : (dfsLTS net).MTr src labels tgt) :
    src.ancestors ⊆ tgt.ancestors := by
  induction hexec with
  | refl => exact List.Subset.refl _
  | stepL htr _ ih =>
      exact List.Subset.trans (ancestors_mono_of_tr htr) ih

/-- Along an infinite Karp–Miller execution, every ancestor at an earlier
position remains an ancestor at every later position. This extends
`ancestors_mono_of_mTr` from finite executions to finite prefixes of an
infinite execution. -/
theorem ancestors_mono_of_omegaExecution
    {nodes : Cslib.ωSequence (Branch P)}
    {labels : Cslib.ωSequence T}
    (hexec : (dfsLTS net).OmegaExecution nodes labels)
    {i j : ℕ} (hij : i ≤ j) :
    (nodes i).ancestors ⊆ (nodes j).ancestors := by
  exact ancestors_mono_of_mTr (hexec.extract_mTr hij)

/-- The source marking of a DFS step is stored among the ancestors of its
target branch. -/
theorem marking_mem_ancestors_of_tr {src tgt : Branch P} {t : T}
    (htr : (dfsLTS net).Tr src t tgt) :
    src.marking ∈ tgt.ancestors := by
  obtain ⟨_, _, rfl⟩ := mem_dfsSuccessors_iff.mp htr
  simp [succBranch, Branch.history]

/-- The initial marking of a finite Karp–Miller execution belongs to the
complete history of its final branch. -/
theorem marking_mem_history_of_mTr {src tgt : Branch P} {labels : List T}
    (hexec : (dfsLTS net).MTr src labels tgt) :
    src.marking ∈ tgt.history := by
  induction hexec with
  | refl => simp [Branch.history]
  | stepL htr htail _ =>
      rw [Branch.history, List.mem_append]
      exact Or.inl (ancestors_mono_of_mTr htail
        (marking_mem_ancestors_of_tr htr))

/-- If the initial marking of a finite execution is below a prospective raw
successor marking `m`, and is strictly smaller at place `p`, then `p` is
selected for acceleration.

The execution makes `src.marking` an already-seen marking in `pred.history`.
The remaining two hypotheses are exactly the non-strict and strict parts of
the Karp–Miller acceleration criterion. In particular, strictness implies that
`p` was not already equal to `ω` in `src.marking`. -/
theorem mem_acceleratedPlaces_of_mTr
    {src pred : Branch P} {labels : List T} {m : OmegaMarking P} {p : P}
    (hexec : (dfsLTS net).MTr src labels pred)
    (hle : src.marking ≤ m) (hlt : src.marking p < m p) :
    p ∈ Branch.acceleratedPlaces m pred := by
  exact Branch.mem_acceleratedPlaces
    (marking_mem_history_of_mTr hexec) hle hlt

/-- Every marking occurring earlier on an infinite Karp–Miller execution is
stored in the ancestor list of every later node.

For consecutive nodes this follows because a step places the source marking
at the head of the target history. For a more distant node, the existing
ancestor membership is carried forward by each subsequent step. -/
theorem marking_mem_ancestors_of_omegaExecution
    {nodes : Cslib.ωSequence (Branch P)}
    {labels : Cslib.ωSequence T}
    (hexec : (dfsLTS net).OmegaExecution nodes labels)
    {i j : ℕ} (hij : i < j) :
    (nodes i).marking ∈ (nodes j).ancestors := by
  have hnext : (nodes i).marking ∈ (nodes (i + 1)).ancestors := by
    exact marking_mem_ancestors_of_tr (hexec i)
  exact ancestors_mono_of_omegaExecution hexec hij hnext

/-- Every marking is contained in the complete history of every node at the
same or a later position of an infinite Karp–Miller execution. -/
theorem marking_mem_history_of_omegaExecution
    {nodes : Cslib.ωSequence (Branch P)}
    {labels : Cslib.ωSequence T}
    (hexec : (dfsLTS net).OmegaExecution nodes labels)
    {i j : ℕ} (hij : i ≤ j) :
    (nodes i).marking ∈ (nodes j).history := by
  rcases Nat.eq_or_lt_of_le hij with (rfl | hij')
  · simp [Branch.history]
  · rw [Branch.history, List.mem_append]
    exact Or.inl
      (marking_mem_ancestors_of_omegaExecution hexec hij')

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


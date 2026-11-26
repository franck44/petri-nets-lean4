/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.CoveringGraph.LTS
public import Cslib.Foundations.Semantics.LTS.OmegaExecution

/-!
# Properties of the covering transition system

Provides the main structural properties of covering-LTS executions:

* existing `ω`-places are preserved;
* ancestor histories grow along executions;
* the history of a node contains the markings visited before it; and
* strict growth from a marking in the history selects the growing place for
  acceleration.
-/

@[expose] public section

namespace PetriNet.CoveringGraph

variable {P T : Type*} [FinEnum P]
variable {net : WeightedNet P T}

/-! ## ω-place monotonicity -/

/-- Along a `coveringLTS` edge, the set of places equal to `ω` can only
grow. -/
theorem omegaPlaces_mono_of_tr {src tgt : Node P} {t : T}
    (htr : (coveringLTS net).Tr src t tgt) :
    OmegaMarking.omegaPlaces src.marking ⊆
      OmegaMarking.omegaPlaces tgt.marking := by
  intro p hp
  rw [OmegaMarking.mem_omegaPlaces] at hp ⊢
  rw [htr.2.2]
  exact successor_preserves_top src t hp

/-- Along a `coveringLTS` execution, the set of `ω`-places can only grow. -/
theorem omegaPlaces_mono_of_mTr {src tgt : Node P} {labels : List T}
    (hexec : (coveringLTS net).MTr src labels tgt) :
    OmegaMarking.omegaPlaces src.marking ⊆
      OmegaMarking.omegaPlaces tgt.marking := by
  induction hexec with
  | refl => exact Finset.Subset.rfl
  | stepL htr _ ih =>
      exact (omegaPlaces_mono_of_tr htr).trans ih

/-- If the endpoints of a finite execution have the same `ω`-places, then
every intermediate node has that same set of `ω`-places. -/
theorem omegaPlaces_eq_of_between_mTr
    {src mid tgt : Node P} {left right : List T}
    (hleft : (coveringLTS net).MTr src left mid)
    (hright : (coveringLTS net).MTr mid right tgt)
    (homega : OmegaMarking.omegaPlaces src.marking =
      OmegaMarking.omegaPlaces tgt.marking) :
    OmegaMarking.omegaPlaces mid.marking =
      OmegaMarking.omegaPlaces tgt.marking := by
  apply Finset.Subset.antisymm
  · exact omegaPlaces_mono_of_mTr hright
  · intro p hp
    rw [← homega] at hp
    exact omegaPlaces_mono_of_mTr hleft hp

/-- Along a `coveringLTS` execution, every earlier set of `ω`-places is
contained in every later one. -/
theorem omegaPlaces_mono_of_omegaExecution
    {nodes : Cslib.ωSequence (Node P)} {labels : Cslib.ωSequence T}
    (hexec : (coveringLTS net).OmegaExecution nodes labels)
    {i j : ℕ} (hij : i ≤ j) :
    OmegaMarking.omegaPlaces (nodes i).marking ⊆
      OmegaMarking.omegaPlaces (nodes j).marking := by
  exact omegaPlaces_mono_of_mTr (hexec.extract_mTr hij)

/-! ## Node histories -/

/-- Every ancestor of the source of an edge remains an ancestor of its
target. -/
theorem ancestors_mono_of_tr {src tgt : Node P} {t : T}
    (htr : (coveringLTS net).Tr src t tgt) :
    src.ancestors ⊆ tgt.ancestors := by
  rw [htr.2.2]
  simp [successor, Node.history]

/-- Along a `coveringLTS` execution, every ancestor of the source remains an
ancestor of the target. -/
theorem ancestors_mono_of_mTr {src tgt : Node P} {labels : List T}
    (hexec : (coveringLTS net).MTr src labels tgt) :
    src.ancestors ⊆ tgt.ancestors := by
  induction hexec with
  | refl => exact List.Subset.refl _
  | stepL htr _ ih =>
      exact List.Subset.trans (ancestors_mono_of_tr htr) ih

/-- Along a `coveringLTS` execution, every ancestor at an earlier position
remains an ancestor at every later position. -/
theorem ancestors_mono_of_omegaExecution
    {nodes : Cslib.ωSequence (Node P)} {labels : Cslib.ωSequence T}
    (hexec : (coveringLTS net).OmegaExecution nodes labels)
    {i j : ℕ} (hij : i ≤ j) :
    (nodes i).ancestors ⊆ (nodes j).ancestors := by
  exact ancestors_mono_of_mTr (hexec.extract_mTr hij)

/-- The source marking of a `coveringLTS` edge belongs to the
ancestor list of its target. -/
theorem marking_mem_ancestors_of_tr {src tgt : Node P} {t : T}
    (htr : (coveringLTS net).Tr src t tgt) :
    src.marking ∈ tgt.ancestors := by
  rw [htr.2.2]
  simp [successor, Node.history]

/-- Every marking occurring earlier on a `coveringLTS` infinite execution is stored
among the ancestors of every later node. -/
theorem marking_mem_ancestors_of_omegaExecution
    {nodes : Cslib.ωSequence (Node P)} {labels : Cslib.ωSequence T}
    (hexec : (coveringLTS net).OmegaExecution nodes labels)
    {i j : ℕ} (hij : i < j) :
    (nodes i).marking ∈ (nodes j).ancestors := by
  have hnext : (nodes i).marking ∈ (nodes (i + 1)).ancestors :=
    marking_mem_ancestors_of_tr (hexec i)
  exact ancestors_mono_of_omegaExecution hexec hij hnext

/-- The source marking of a nonempty `coveringLTS` execution belongs to the
ancestor list of its target. -/
theorem marking_mem_ancestors_of_mTr_cons
    {src tgt : Node P} {t : T} {labels : List T}
    (hexec : (coveringLTS net).MTr src (t :: labels) tgt) :
    src.marking ∈ tgt.ancestors := by
  cases hexec with
  | stepL htr htail =>
      exact ancestors_mono_of_mTr htail
        (marking_mem_ancestors_of_tr htr)

/-- The source marking of any `coveringLTS` execution belongs to the complete
history of its target. For the empty execution it is the current marking; for
a nonempty execution it is an ancestor. -/
theorem marking_mem_history_of_mTr {src tgt : Node P} {labels : List T}
    (hexec : (coveringLTS net).MTr src labels tgt) :
    src.marking ∈ tgt.history := by
  cases labels with
  | nil =>
      cases hexec
      simp [Node.history]
  | cons t labels =>
      rw [Node.history, List.mem_append]
      exact Or.inl (marking_mem_ancestors_of_mTr_cons hexec)

/-! ## First occurrences -/

/-- An ancestor of the target of a finite covering-LTS execution is either
already an ancestor of the source or is the marking of an earlier
first-occurrence node on that execution.

In the second case the labels split around that earlier node:

```text
src ──pre──▶ mid ──rest──▶ tgt
              mid.marking = a
              mid.IsFirstOccurrence
```

The first-occurrence property follows from the outgoing edge that originally
extended `mid`. -/
theorem ancestor_eq_predecessor_of_mTr
    {src tgt : Node P} {labels : List T} {a : OmegaMarking P}
    (hexec : (coveringLTS net).MTr src labels tgt)
    (ha : a ∈ tgt.ancestors) :
    a ∈ src.ancestors ∨
      ∃ pre mid rest,
        labels = pre ++ rest ∧
        (coveringLTS net).MTr src pre mid ∧
        (coveringLTS net).MTr mid rest tgt ∧
        mid.IsFirstOccurrence ∧
        mid.marking = a := by
  induction hexec with
  | refl => exact Or.inl ha
  | @stepL src t next labels tgt htr htail ih =>
      rcases ih ha with hsrc | ⟨pre, mid, rest, hlabels,
          hpre, hrest, hfirst, hmarking⟩
      · rw [ancestors_eq_history_of_tr htr] at hsrc
        rw [Node.history, List.mem_append, List.mem_singleton] at hsrc
        rcases hsrc with hancestor | hcurrent
        · exact Or.inl hancestor
        · exact Or.inr ⟨[], src, t :: labels, rfl,
            Cslib.LTS.MTr.refl, htail.stepL htr,
            htr.1, hcurrent.symm⟩
      · exact Or.inr ⟨t :: pre, mid, rest,
          by simp [hlabels], hpre.stepL htr, hrest, hfirst, hmarking⟩

/-- Every node reachable from an initial node has a reachable
first-occurrence node carrying the same marking.

If the node is already a first occurrence, it is its own witness. Otherwise,
its marking occurs among its ancestors, and
`ancestor_eq_predecessor_of_mTr` locates the earlier first occurrence. -/
theorem exists_first_occurrence_of_canReach
    {m₀ : Marking P} {src : Node P}
    (hreach : (coveringLTS net).CanReach (Node.initial m₀) src) :
    ∃ first,
      (coveringLTS net).CanReach (Node.initial m₀) first ∧
      first.IsFirstOccurrence ∧ first.marking = src.marking := by
  by_cases hfirst : src.IsFirstOccurrence
  · exact ⟨src, hreach, hfirst, rfl⟩
  · obtain ⟨labels, hexec⟩ := hreach
    have hmem : src.marking ∈ src.ancestors := by
      simpa [Node.IsFirstOccurrence] using hfirst
    rcases ancestor_eq_predecessor_of_mTr hexec hmem with hroot |
        ⟨pre, first, _, _, hpre, _, hfirst, hmarking⟩
    · simp [Node.initial, Node.root] at hroot
    · exact ⟨first, ⟨pre, hpre⟩, hfirst, hmarking⟩

end PetriNet.CoveringGraph

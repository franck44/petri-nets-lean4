/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.KarpMiller.LTS
public import PetriNets.OmegaMarking.Sequence
public import Mathlib.Data.FinEnum

/-!
# Termination of Karp–Miller DFS branches

This module proves that the Karp–Miller DFS has no infinite branch. Along an
execution, the set of places equal to `ω` grows monotonically and earlier
markings are retained in branch histories. Dickson's lemma then forces a
repeated marking, which closes the branch. The absence of infinite executions
is finally expressed as well-foundedness of the child relation.

## References

* W. Reisig, *Understanding Petri Nets: Modeling Techniques, Analysis Methods,
  Case Studies*, Springer, 2013, Chapter 14.
  DOI: 10.1007/978-3-642-33278-4.
-/

@[expose] public section

namespace PetriNet

namespace KarpMiller

variable {P T : Type*}
variable {net : WeightedNet P T}

section FinitePlaces

variable [FinEnum P] [FinEnum T]

/-- If the source marking of a finite prefix is strictly below the target of
the next step, stable `ω`-place sets across that step force the strict
component to be accelerated to a new `ω`-place. -/
private theorem exists_new_omegaPlace_of_mTr_lt_tr
    {src pred tgt : Branch P} {labels : List T} {t : T}
    (hprefix : (dfsLTS net).MTr src labels pred)
    (htr : (dfsLTS net).Tr pred t tgt)
    (hlt : src.marking < tgt.marking)
    (homegaPred : OmegaMarking.omegaPlaces pred.marking =
      OmegaMarking.omegaPlaces tgt.marking) :
    ∃ p, p ∉ OmegaMarking.omegaPlaces src.marking ∧
      p ∈ OmegaMarking.omegaPlaces tgt.marking := by
  -- Since the final step introduces no new `ω`-place, its acceleration does
  -- not change the raw successor marking.
  have hraw : tgt.marking = succMarking net pred.marking t :=
    marking_eq_succMarking_of_tr_of_omegaPlaces_eq htr homegaPred

  -- Strict growth from `src` to `tgt` is witnessed at some place `p`.
  obtain ⟨p, hp⟩ : ∃ p,
      src.marking p < tgt.marking p := by
    exact OmegaMarking.exists_place_lt_of_le_of_ne hlt.le hlt.ne

  -- The source marking occurs in the history of `pred`. After replacing the
  -- raw successor by `tgt.marking`, `hlt` and `hp` are exactly the two
  -- inequalities required to select `p` for acceleration.
  have hpAccelerated : p ∈ Branch.acceleratedPlaces
      (succMarking net pred.marking t) pred := by
    apply mem_acceleratedPlaces_of_mTr hprefix
    · rw [← hraw]
      exact hlt.le
    · rwa [← hraw]

  -- Every selected place has value `ω` in the accelerated target.
  have hpTop : tgt.marking p = ⊤ := by
    have htgt := (mem_dfsSuccessors_iff.mp htr).2.2
    rw [← htgt]
    exact succBranch_eq_top_of_mem_acceleratedPlaces
      pred t hpAccelerated

  -- The place is new: it cannot already have been `ω` in `src`, because
  -- `hp` says that its value increases strictly.
  refine ⟨p, ?_, ?_⟩
  · rw [OmegaMarking.mem_omegaPlaces]
    intro hpOldTop
    rw [hpOldTop, hpTop] at hp
    exact (lt_self_iff_false ⊤).mp hp
  · rw [OmegaMarking.mem_omegaPlaces]
    exact hpTop

/-- **Strict growth is incompatible with a stable set of `ω`-places.**

The source marking of the finite prefix occurs in the predecessor's history.
Endpoint stability propagates to the final step, where
`exists_new_omegaPlace_of_mTr_lt_tr` applies. -/
private theorem exists_new_omegaPlace_of_lt_of_omegaPlaces_eq
    {src pred tgt : Branch P} {labels : List T} {t : T}
    (hprefix : (dfsLTS net).MTr src labels pred)
    (htr : (dfsLTS net).Tr pred t tgt)
    (hlt : src.marking < tgt.marking)
    (homega : OmegaMarking.omegaPlaces src.marking =
      OmegaMarking.omegaPlaces tgt.marking) :
    ∃ p, p ∉ OmegaMarking.omegaPlaces src.marking ∧
      p ∈ OmegaMarking.omegaPlaces tgt.marking := by
  exact exists_new_omegaPlace_of_mTr_lt_tr
    hprefix htr hlt
    (omegaPlaces_eq_of_between_mTr hprefix
      (Cslib.LTS.MTr.single (dfsLTS net) htr) homega)

/-- **Strict growth along a finite Karp–Miller execution strictly increases
the set of `ω`-places.**

If `src` reaches `tgt` and `src.marking < tgt.marking`, then some place that
is finite in `src` is equal to `ω` in `tgt`.

There are two cases. If the endpoint sets of `ω`-places differ, their
monotonicity along the execution immediately gives such a place. If the sets
are equal, `exists_new_omegaPlace_of_lt_of_omegaPlaces_eq` shows that the
strict increase activates the acceleration rule and produces such a place
anyway, contradicting their equality.

Thus a strict increase between comparable markings on one branch always
consumes at least one previously finite place by changing it to `ω`. Since the
place type is finite, this is the progress property used to rule out infinite
Karp–Miller branches. -/
theorem omegaPlaces_ssubset_of_lt_mTr
    {src tgt : Branch P} {labels : List T}
    (hexec : (dfsLTS net).MTr src labels tgt)
    (hlt : src.marking < tgt.marking) :
    OmegaMarking.omegaPlaces src.marking ⊂
      OmegaMarking.omegaPlaces tgt.marking := by
  have hsubset := omegaPlaces_mono_of_mTr hexec
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨hsubset, ?_⟩
  intro homega
  rcases labels.eq_nil_or_concat with rfl | ⟨labels, t, rfl⟩
  · have : src = tgt := Cslib.LTS.MTr.nil_eq (dfsLTS net) hexec
    subst tgt
    exact (lt_irrefl _ hlt).elim
  · rw [List.concat_eq_append] at hexec
    rw [Cslib.LTS.MTr.append_iff] at hexec
    obtain ⟨pred, hprefix, hlast⟩ := hexec
    have htr : (dfsLTS net).Tr pred t tgt := by simpa using hlast
    obtain ⟨p, hpEarlier, hpLater⟩ :=
      exists_new_omegaPlace_of_lt_of_omegaPlaces_eq
        hprefix htr hlt homega
    exact hpEarlier (homega.symm ▸ hpLater)

/-- A strict increase along a finite Karp–Miller execution introduces a new
`ω`-place. This is the witness form of
`omegaPlaces_ssubset_of_lt_mTr`. -/
theorem exists_new_omegaPlace_of_lt_mTr
    {src tgt : Branch P} {labels : List T}
    (hexec : (dfsLTS net).MTr src labels tgt)
    (hlt : src.marking < tgt.marking) :
    ∃ p, p ∉ OmegaMarking.omegaPlaces src.marking ∧
      p ∈ OmegaMarking.omegaPlaces tgt.marking := by
  have hstrict := omegaPlaces_ssubset_of_lt_mTr hexec hlt
  rw [Finset.ssubset_iff_of_subset hstrict.le] at hstrict
  obtain ⟨p, hpLater, hpEarlier⟩ := hstrict
  exact ⟨p, hpEarlier, hpLater⟩

/-- A strict increase across one Karp–Miller DFS step introduces a new
`ω`-place in the target marking. This is the singleton case of
`exists_new_omegaPlace_of_lt_mTr`. -/
theorem exists_new_omegaPlace_of_lt_tr
    {src tgt : Branch P} {t : T}
    (htr : (dfsLTS net).Tr src t tgt)
    (hlt : src.marking < tgt.marking) :
    ∃ p, p ∉ OmegaMarking.omegaPlaces src.marking ∧
      p ∈ OmegaMarking.omegaPlaces tgt.marking := by
  exact exists_new_omegaPlace_of_lt_mTr
    (Cslib.LTS.MTr.single (dfsLTS net) htr) hlt

/-- Strict growth between two positions of an infinite Karp–Miller execution
introduces a new `ω`-place. This is the finite-execution theorem
`exists_new_omegaPlace_of_lt_mTr` applied to the prefix between the two
positions. -/
theorem exists_new_omegaPlace_of_lt_omegaExecution
    {nodes : Cslib.ωSequence (Branch P)}
    {labels : Cslib.ωSequence T}
    (hexec : (dfsLTS net).OmegaExecution nodes labels)
    {i j : ℕ} (hij : i < j)
    (hlt : (nodes i).marking < (nodes j).marking) :
    ∃ p, p ∉ OmegaMarking.omegaPlaces (nodes i).marking ∧
      p ∈ OmegaMarking.omegaPlaces (nodes j).marking := by
  exact exists_new_omegaPlace_of_lt_mTr
    (hexec.extract_mTr hij.le) hlt

/-- The Karp–Miller LTS has no infinite execution.

Assume that an infinite execution exists. Along this execution, the set of
`ω`-places grows monotonically. Moreover, whenever an earlier marking is
strictly below a later one, `exists_new_omegaPlace_of_lt_omegaExecution`
shows that the later marking has acquired a new `ω`-place. The generic
Dickson argument `OmegaMarking.exists_eq_pair_of_omegaPlaces_mono` therefore
provides positions `i < j` carrying equal markings.

The marking at position `i` is stored among the ancestors of the branch at
position `j`. Since the two current markings are equal, the current marking
at `j` also occurs among its own ancestors. Thus the branch at `j` is not
fresh and the DFS gives it no successor. This contradicts the transition from
position `j` to position `j + 1` supplied by the assumed infinite
execution. -/
theorem not_omegaExecution
    {nodes : Cslib.ωSequence (Branch P)}
    {labels : Cslib.ωSequence T} :
    ¬ (dfsLTS net).OmegaExecution nodes labels := by
  intro hexec
  /- prove that if we have an infinite execution we can conclude False. -/
  obtain ⟨i, j, hij, heq⟩ :=
    /- Apply the Dickson argument to find two positions with equal markings. -/
    OmegaMarking.exists_eq_pair_of_omegaPlaces_mono
      (fun n => (nodes n).marking)
      (fun hij => omegaPlaces_mono_of_omegaExecution hexec hij)
      (fun hij hle homega hne =>
        exists_new_omegaPlace_of_lt_omegaExecution
          hexec hij (lt_of_le_of_ne hle hne))
  /- At this point, we have found two positions `i < j` with equal markings. -/

  /- The marking at position `i` is among the ancestors of the branch at
  position `j`. -/
  have hancestor :=
    marking_mem_ancestors_of_omegaExecution hexec hij
  /- This implies that the branch at position j is not fresh,
  since it has a duplicate marking among its ancestors. -/
  have hnotfresh : ¬ (nodes j).IsFresh := by
    simp only [Branch.IsFresh, not_not]
    rw [← heq]
    exact hancestor
  /- Finally, a non-fresh branch has no DFS successor, contradicting the next
  step of the infinite execution. -/
  exact hnotfresh (mem_dfsSuccessors_iff.mp (hexec j)).1

/-- `DfsCall net next current` means that computing the Karp–Miller DFS at
`current` makes an immediate recursive call at `next`.

Such a call occurs exactly when `dfsLTS net` has a transition from `current`
to `next`, with some label. The recursive argument is placed first so that
`DfsCall net` has the orientation expected of a well-founded relation:
`next` is smaller than `current`. -/
def DfsCall (net : WeightedNet P T)
    (next current : Branch P) : Prop :=
  ∃ t, (dfsLTS net).Tr current t next

/-- The recursive-call relation of the Karp–Miller DFS is well-founded.

An infinite descending chain for `DfsCall net` would select a transition
label at every position and therefore form an infinite execution of
`dfsLTS net`, contradicting `not_omegaExecution`. -/
theorem dfsCall_wellFounded : WellFounded (DfsCall net) := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  constructor
  rintro ⟨nodes, hchildren⟩
  let nodeSequence : Cslib.ωSequence (Branch P) := nodes
  let labels : Cslib.ωSequence T := fun n =>
    Classical.choose (hchildren n)
  apply not_omegaExecution (nodes := nodeSequence) (labels := labels)
  intro n
  change (dfsLTS net).Tr (nodes n) (Classical.choose (hchildren n))
    (nodes (n + 1))
  exact Classical.choose_spec (hchildren n)

end FinitePlaces

end KarpMiller

end PetriNet

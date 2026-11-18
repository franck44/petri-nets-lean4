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

/-- Along an infinite Karp–Miller execution, the set of `ω`-places at an
earlier position is contained in the set at every later position. -/
theorem omegaPlaces_mono_of_omegaExecution {nodes : Cslib.ωSequence (Branch P)}
    {labels : Cslib.ωSequence T}
    (hexec : (dfsLTS net).OmegaExecution nodes labels)
    {i j : ℕ} (hij : i ≤ j) :
    OmegaMarking.omegaPlaces (nodes i).marking ⊆
      OmegaMarking.omegaPlaces (nodes j).marking := by
  induction j with
  | zero =>
      have : i = 0 := by omega
      subst i
      exact Finset.Subset.rfl
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with (rfl | hij')
      · exact Finset.Subset.rfl
      · exact (ih (Nat.le_of_lt_succ hij')).trans
          (omegaPlaces_mono_of_tr (hexec j))

end FinitePlaces

section FinitePlaces

variable [FinEnum P] [FinEnum T]


/-- The ancestors of the target of a Karp–Miller DFS edge `src t tgt`
are exactly the complete history of `src`. -/
theorem ancestors_eq_history_of_tr {src tgt : Branch P} {t : T}
    (htr : (dfsLTS net).Tr src t tgt) :
    tgt.ancestors = src.history := by
  change (t, tgt) ∈ dfsSuccessors net src at htr
  rw [mem_dfsSuccessors_iff] at htr
  rw [← htr.2.2]
  rfl

/-- Every marking occurring earlier on an infinite Karp–Miller execution is
stored in the ancestor list of every later node.

For consecutive nodes this follows because a step places the source marking
at the head of the target history. For a more distant node, the existing
ancestor membership is carried forward by each subsequent step. -/
theorem marking_mem_ancestors_of_omegaExecution {nodes : Cslib.ωSequence (Branch P)}
    {labels : Cslib.ωSequence T}
    (hexec : (dfsLTS net).OmegaExecution nodes labels)
    {i j : ℕ} (hij : i < j) :
    (nodes i).marking ∈ (nodes j).ancestors := by
  induction j with
  | zero => omega
  | succ j ih =>
      rw [ancestors_eq_history_of_tr (hexec j)]
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hij) with (rfl | hij')
      · simp [Branch.history]
      · simp [Branch.history, ih hij']

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
  · simp [Branch.history,
      marking_mem_ancestors_of_omegaExecution hexec hij']

/-- On an infinite Karp–Miller execution, two distinct comparable markings
with the same ω-places would force a new ω-place in the later marking.

The earlier marking occurs in the history of the predecessor of the later
node. Stability of the ω-place set makes the later marking equal to its raw
firing result. Hence any strict component increase satisfies the acceleration
condition and is replaced by `ω`. -/
theorem exists_new_omegaPlace_of_lt_of_le_omegaExecution
    {nodes : Cslib.ωSequence (Branch P)}
    {labels : Cslib.ωSequence T}
    (hexec : (dfsLTS net).OmegaExecution nodes labels)
    {i j : ℕ} (hij : i < j)
    (hle : (nodes i).marking ≤ (nodes j).marking)
    (homega : OmegaMarking.omegaPlaces (nodes i).marking =
      OmegaMarking.omegaPlaces (nodes j).marking)
    (hne : (nodes i).marking ≠ (nodes j).marking) :
    ∃ p, p ∉ OmegaMarking.omegaPlaces (nodes i).marking ∧
      p ∈ OmegaMarking.omegaPlaces (nodes j).marking := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := by
    use j - 1
    omega
  have hik : i ≤ k := by omega
  have hhistory : (nodes i).marking ∈ (nodes k).history :=
    marking_mem_history_of_omegaExecution hexec hik
  have homegaPred : OmegaMarking.omegaPlaces (nodes k).marking =
      OmegaMarking.omegaPlaces (nodes (k + 1)).marking := by
    apply Finset.Subset.antisymm
    · exact omegaPlaces_mono_of_tr (hexec k)
    · intro p hp
      have hpEarlier : p ∈ OmegaMarking.omegaPlaces (nodes i).marking := by
        rw [homega]
        exact hp
      exact omegaPlaces_mono_of_omegaExecution hexec hik hpEarlier
  have htr := mem_dfsSuccessors_iff.mp (hexec k)
  have homegaSucc : OmegaMarking.omegaPlaces (nodes k).marking =
      OmegaMarking.omegaPlaces
        (succBranch net (nodes k) (labels k)).marking := by
    rw [htr.2.2]
    exact homegaPred
  have hraw : (nodes (k + 1)).marking =
      succMarking net (nodes k).marking (labels k) := by
    rw [← htr.2.2]
    exact succBranch_marking_eq_succMarking_of_omegaPlaces_eq
      (nodes k) (labels k) homegaSucc
  obtain ⟨p, hp⟩ : ∃ p,
      (nodes i).marking p < (nodes (k + 1)).marking p := by
    by_contra h
    push Not at h
    apply hne
    funext p
    exact le_antisymm (hle p) (h p)
  have hpAccelerated : p ∈ Branch.acceleratedPlaces
      (succMarking net (nodes k).marking (labels k)) (nodes k) := by
    simp only [Branch.acceleratedPlaces, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine ⟨(nodes i).marking, hhistory, ?_, ?_⟩
    · rw [← hraw]
      exact hle
    · rw [← hraw]
      exact hp
  have hpTop : (nodes (k + 1)).marking p = ⊤ := by
    rw [← htr.2.2]
    exact succBranch_eq_top_of_mem_acceleratedPlaces
      (nodes k) (labels k) hpAccelerated
  refine ⟨p, ?_, ?_⟩
  · rw [OmegaMarking.mem_omegaPlaces]
    intro hpOldTop
    rw [hpOldTop, hpTop] at hp
    exact (lt_self_iff_false ⊤).mp hp
  · rw [OmegaMarking.mem_omegaPlaces]
    exact hpTop

/-- The Karp–Miller LTS has no infinite execution.

The generic ω-marking sequence lemma supplies two equal markings on any
hypothetical infinite execution. The earlier marking is stored among the
ancestors of the later node, so that node is a duplicate. But every step has
an open source, contradicting the next step of the infinite execution. -/
theorem not_omegaExecution
    {nodes : Cslib.ωSequence (Branch P)}
    {labels : Cslib.ωSequence T} :
    ¬ (dfsLTS net).OmegaExecution nodes labels := by
  intro hexec
  obtain ⟨i, j, hij, heq⟩ :=
    OmegaMarking.exists_eq_pair_of_omegaPlaces_mono
      (fun n => (nodes n).marking)
      (fun hij => omegaPlaces_mono_of_omegaExecution hexec hij)
      (fun hij hle homega hne =>
        exists_new_omegaPlace_of_lt_of_le_omegaExecution
          hexec hij hle homega hne)
  have hancestor :=
    marking_mem_ancestors_of_omegaExecution hexec hij
  have hnotopen : ¬ (nodes j).IsOpen := by
    simp only [Branch.IsOpen, not_not]
    rw [← heq]
    exact hancestor
  exact hnotopen (mem_dfsSuccessors_iff.mp (hexec j)).1

/-- `Child net tgt src` means that `tgt` is an immediate Karp–Miller
successor of `src`, for some transition label. The argument order is chosen
for well-founded recursion: children are smaller than their parents. -/
def Child (net : WeightedNet P T)
    (tgt src : Branch P) : Prop :=
  ∃ t, (dfsLTS net).Tr src t tgt

/-- The Karp–Miller child relation is well-founded.

An infinite descending chain for `Child net` would select a transition label
at every position and therefore form an infinite execution of `dfsLTS net`,
contradicting `not_omegaExecution`. -/
theorem child_wellFounded : WellFounded (Child net) := by
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


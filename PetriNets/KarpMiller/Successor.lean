/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.KarpMiller.Branch

/-!
# Karp–Miller successors

The Karp–Miller algorithm expands a branch by choosing a transition enabled
at its current marking. Firing the transition produces a successor
marking. This marking is accelerated with respect to the history of the
branch, and the accelerated marking is appended to form the successor branch.
A branch that is not a first occurrence is not expanded.

This idea is represented by the following definitions:

* `succMarking` computes the successor marking;
* `succBranch` accelerates that marking and appends it to the branch;
* `succMarkings` computes the successors for all enabled transitions; and
* `succBranch` accelerates one of these markings and extends a branch.
-/

@[expose] public section

namespace PetriNet

namespace KarpMiller

variable {P T : Type*}
variable {net : WeightedNet P T}

/-- The marking obtained by applying the firing arithmetic for `t` at `m`.
When `t` is enabled, this is its unique ω-firing result. -/
def succMarking (net : WeightedNet P T)
    (m : OmegaMarking P) (t : T) : OmegaMarking P :=
  fun p => m p - net.pre p t + net.post p t

section FinitePlaces

variable [FinEnum P]

/-- Compute the Karp–Miller successor of `src` for transition `t`.

This function performs the firing arithmetic, accelerates the resulting
marking with respect to the history of `src`, and appends it to the branch.
The caller is responsible for ensuring that `src` is a first occurrence and `t` is
enabled. -/
def succBranch (net : WeightedNet P T) (src : Branch P) (t : T) : Branch P :=
  let m := succMarking net src.marking t
  src ++ OmegaMarking.accelerateFinset (Branch.acceleratedPlaces m src) m

variable [FinEnum T]

/-- Compute the labelled successor markings for all transitions enabled at
`m`. This function extends `succMarking` from one transition to every enabled
transition and is independent of Karp–Miller branches and acceleration. -/
def succMarkings (net : WeightedNet P T) (m : OmegaMarking P) :
    List (T × OmegaMarking P) :=
  let enabled := (FinEnum.toList T).filter fun t =>
    ∀ p, (net.pre p t : ℕ∞) ≤ m p
  enabled.map fun t => (t, succMarking net m t)

/-- Every pair returned by `succMarkings` consists of an enabled transition
and its successor marking.

This is needed becauase we do not use OmegaEnabled in the definition of `succMarkings` itself,
so we need to explicitly relate membership in the list to enabledness and the corresponding
successor marking.
Note that we don't use `OmegaEnabled` because OmegaEnabled is not neccesarily computable. -/
theorem enabled_and_eq_of_mem_succMarkings
    {m m' : OmegaMarking P} {t : T}
    (h : (t, m') ∈ succMarkings net m) :
    net.OmegaEnabled m t ∧ succMarking net m t = m' := by
  unfold succMarkings at h
  simp only [List.mem_map] at h
  obtain ⟨u, hu, hpair⟩ := h
  obtain ⟨_, henabled⟩ := List.mem_filter.mp hu
  obtain ⟨rfl, rfl⟩ := hpair
  have hEnabled : ∀ p, (net.pre p t : ℕ∞) ≤ m p :=
    of_decide_eq_true henabled
  exact ⟨hEnabled, rfl⟩

/-- Every enabled transition and its successor marking occur in
`succMarkings`. -/
theorem mem_succMarkings_of_enabled {m : OmegaMarking P} {t : T}
    (h : net.OmegaEnabled m t) :
    (t, succMarking net m t) ∈ succMarkings net m := by
  unfold succMarkings
  simp only [List.mem_map]
  refine ⟨t, List.mem_filter.mpr
    ⟨FinEnum.mem_toList t, decide_eq_true h⟩, rfl⟩

end FinitePlaces

end KarpMiller

end PetriNet

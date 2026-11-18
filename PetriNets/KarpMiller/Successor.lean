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
A branch that is not open is not expanded.

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
The caller is responsible for ensuring that `src` is open and `t` is
enabled. -/
def succBranch (net : WeightedNet P T) (src : Branch P) (t : T) : Branch P :=
  let m := succMarking net src.marking t
  src ++ OmegaMarking.accelerateFinset (Branch.acceleratedPlaces m src) m

/-- `succBranch` preserves every place already equal to `ω`. -/
theorem succBranch_preserves_top (src : Branch P) (t : T) {p : P}
    (hp : src.marking p = ⊤) :
    (succBranch net src t).marking p = ⊤ := by
  simp [succBranch, OmegaMarking.accelerateFinset,
    succMarking, hp]

/-- A place selected by the acceleration rule has value `ω` in the successor
branch. -/
theorem succBranch_eq_top_of_mem_acceleratedPlaces
    (src : Branch P) (t : T) {p : P}
    (hp : p ∈ Branch.acceleratedPlaces
      (succMarking net src.marking t) src) :
    (succBranch net src t).marking p = ⊤ := by
  simp [succBranch, OmegaMarking.accelerateFinset, hp]

/-- Constructing a successor branch can only increase the set of places equal
to `ω`. -/
theorem omegaPlaces_mono_of_succBranch (src : Branch P) (t : T) :
    OmegaMarking.omegaPlaces src.marking ⊆
      OmegaMarking.omegaPlaces (succBranch net src t).marking := by
  intro p hp
  rw [OmegaMarking.mem_omegaPlaces] at hp ⊢
  exact succBranch_preserves_top src t hp

/-- If a Karp–Miller step does not introduce a new `ω`-place, acceleration
does not change its successor marking.

A place selected for acceleration has value `ω` in the target. Equality of
the source and target ω-place sets implies that it was already `ω` in the
source, and firing preserves that value. Every unselected place retains its
successor value by definition. -/
theorem succBranch_marking_eq_succMarking_of_omegaPlaces_eq
    (src : Branch P) (t : T)
    (homega : OmegaMarking.omegaPlaces src.marking =
      OmegaMarking.omegaPlaces (succBranch net src t).marking) :
    (succBranch net src t).marking = succMarking net src.marking t := by
  funext p
  by_cases hp : p ∈ Branch.acceleratedPlaces
      (succMarking net src.marking t) src
  · have htgtTop : (succBranch net src t).marking p = ⊤ := by
      simp [succBranch, OmegaMarking.accelerateFinset, hp]
    have hpTgt : p ∈ OmegaMarking.omegaPlaces
        (succBranch net src t).marking := by
      rw [OmegaMarking.mem_omegaPlaces]
      exact htgtTop
    rw [← homega, OmegaMarking.mem_omegaPlaces] at hpTgt
    simp [succBranch, OmegaMarking.accelerateFinset,
      succMarking, hp, hpTgt]
  · simp [succBranch, OmegaMarking.accelerateFinset, hp]

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

/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.MarkingGraph
public import PetriNets.PlaceInvariant.Boundedness

/-!
# Boundedness and finite marking graphs

This module defines unboundedness of an individual place and simultaneous
unboundedness of a set of places. It also proves Reisig's marking-graph
characterisation of boundedness. The marking graph is finite-state when its
generated state type has a `Finite` instance, following CSLib's convention
for finite-state labelled transition systems.

For a finite place type, a finite marking graph implies boundedness: the
finitely many graph states and places provide only finitely many token counts.
Conversely, if one bound applies to all places, each place has only finitely
many possible token counts, so there are only finitely many possible markings.

## References

* W. Reisig, *Understanding Petri Nets: Modeling Techniques, Analysis Methods,
  Case Studies*, Springer, 2013, Section 14.1, pp. 151–152.
  DOI: 10.1007/978-3-642-33278-4.
-/

@[expose] public section

namespace PetriNet

/-- Place `p` is unbounded from `m₀` when, for every proposed bound `B`,
there is a marking reachable from `m₀` that contains more than `B` tokens
in `p`. -/
def WeightedNet.PlaceUnboundedFrom {P T : Type*} (net : WeightedNet P T)
    (m₀ : Marking P) (p : P) : Prop :=
  ∀ B : ℕ, ∃ m, net.Reachable m₀ m ∧ B < m p

/-- The places in `places` are simultaneously unbounded from `m₀` when,
for every proposed common bound `B`, one reachable marking contains more
than `B` tokens at every place in `places` simultaneously.

This is stronger than requiring each place in `places` to be individually
unbounded: the same reachable marking must witness growth at all of them. -/
def WeightedNet.SimultaneouslyUnboundedFrom {P T : Type*}
    (net : WeightedNet P T) (m₀ : Marking P) (places : Set P) : Prop :=
  ∀ B : ℕ, ∃ m, net.Reachable m₀ m ∧ ∀ p ∈ places, B < m p

/-- A place is unbounded exactly when it is not bounded. -/
theorem WeightedNet.placeUnboundedFrom_iff_not_placeBoundedFrom
    {P T : Type*} (net : WeightedNet P T) (m₀ : Marking P) (p : P) :
    net.PlaceUnboundedFrom m₀ p ↔ ¬ net.PlaceBoundedFrom m₀ p := by
  classical
  simp [WeightedNet.PlaceUnboundedFrom, WeightedNet.PlaceBoundedFrom]

/-- Simultaneous unboundedness of a singleton is precisely unboundedness of
its only place. -/
theorem WeightedNet.simultaneouslyUnboundedFrom_singleton
    {P T : Type*} (net : WeightedNet P T) (m₀ : Marking P) (p : P) :
    net.SimultaneouslyUnboundedFrom m₀ {p} ↔
      net.PlaceUnboundedFrom m₀ p := by
  simp [WeightedNet.SimultaneouslyUnboundedFrom,
    WeightedNet.PlaceUnboundedFrom]

/-- If the place type and the state type of the marking graph from `m₀` are
finite, then the net is bounded from `m₀`. -/
theorem WeightedNet.boundedFrom_of_finite_markingGraph
    {P T : Type*} [Fintype P] {net : WeightedNet P T} {m₀ : Marking P}
    (hfinite : Finite {m : Marking P // net.markingLTS.CanReach m₀ m}) :
    net.BoundedFrom m₀ := by
  let _ := hfinite
  /- The finite set of graph states and places yields finitely many token
     counts, so those counts have an upper bound. -/
  obtain ⟨B, hB⟩ :=
    Finite.bddAbove_range
      (fun mp : {m : Marking P // net.markingLTS.CanReach m₀ m} × P =>
        mp.1.1 mp.2)
  use B
  intro m hmReachable p
  let state : {m : Marking P // net.markingLTS.CanReach m₀ m} :=
    ⟨m, net.markingLTS_canReach_iff.mpr hmReachable⟩
  exact hB ⟨(state, p), rfl⟩

/-- If `P` is finite and the net is bounded from `m₀`, then the set of states
of the marking graph from `m₀` is finite. -/
theorem WeightedNet.finite_markingGraph_of_boundedFrom
    {P T : Type*} [Fintype P] {net : WeightedNet P T} {m₀ : Marking P}
    (hbounded : net.BoundedFrom m₀) :
    Finite {m : Marking P // net.markingLTS.CanReach m₀ m} := by
  obtain ⟨B, hB⟩ := hbounded
  /- The interval from the zero marking to the constant marking
     `(B, ..., B)` is a finite box of markings. -/
  let boundedMarkings : Set (Marking P) := Set.Icc 0 (fun _ => B)
  have hboundedMarkings : boundedMarkings.Finite := by
    have hbox : boundedMarkings = {m | ∀ p, m p ≤ B} := by
      ext m
      simp [boundedMarkings, Pi.le_def]
    rw [hbox]
    have hpi := Set.Finite.pi'
      (t := fun _ : P => Set.Iic B) (fun _ => Set.finite_Iic B)
    simpa using hpi
  /- Every marking in the marking graph belongs to `boundedMarkings`. -/
  have hstateBounded
      (state : {m : Marking P // net.markingLTS.CanReach m₀ m}) :
      state.1 ∈ boundedMarkings := by
    constructor
    · simp
    · exact hB state.1 (WeightedNet.markingGraph_state_reachable state)
  let _ : Finite boundedMarkings := Set.finite_coe_iff.mpr hboundedMarkings
  /- The map from marking graph states to bounded markings is injective, so
     the finiteness of bounded markings implies the finiteness of the marking
     graph states. -/
  let toBoundedMarking :
      {m : Marking P // net.markingLTS.CanReach m₀ m} → boundedMarkings :=
    fun state => ⟨state.1, hstateBounded state⟩
  /- The map merely forgets the reachability proof, so it is injective. -/
  apply Finite.of_injective toBoundedMarking
  intro src tgt h
  apply Subtype.ext
  exact congrArg (fun m : boundedMarkings => m.1) h

/-- For a finite place type, a net is bounded from `m₀` if and only if the
state type of its marking graph from `m₀` is finite. -/
theorem WeightedNet.boundedFrom_iff_finite_markingGraph
    {P T : Type*} [Fintype P] (net : WeightedNet P T) (m₀ : Marking P) :
    net.BoundedFrom m₀ ↔
      Finite {m : Marking P // net.markingLTS.CanReach m₀ m} :=
  ⟨WeightedNet.finite_markingGraph_of_boundedFrom,
    WeightedNet.boundedFrom_of_finite_markingGraph⟩

end PetriNet

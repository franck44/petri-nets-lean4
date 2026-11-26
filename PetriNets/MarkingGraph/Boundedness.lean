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

Provides individual and simultaneous place-unboundedness notions and proves
Reisig's marking-graph characterisation of boundedness: for a weighted P/T net
with finitely many places, the net is bounded from an initial marking if and
only if its marking graph from that marking is finite.

For a finite set of places, a finite marking graph implies boundedness: the
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

/-! ## Place unboundedness -/

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

/-! ## Boundedness and finite marking graphs -/

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
of the marking graph from `m₀` is finite. A common bound `B` lets us encode
every reachable marking as an element of the finite vector type
`P → Fin (B + 1)`. -/
theorem WeightedNet.finite_markingGraph_of_boundedFrom
    {P T : Type*} [Fintype P] {net : WeightedNet P T} {m₀ : Marking P}
    (hbounded : net.BoundedFrom m₀) :
    Finite {m : Marking P // net.markingLTS.CanReach m₀ m} := by
  obtain ⟨B, hB⟩ := hbounded
  /- Encode each reachable marking as a vector of values in `Fin (B + 1)`. -/
  let toBoundedVector :
      {m : Marking P // net.markingLTS.CanReach m₀ m} → P → Fin (B + 1) :=
    fun state p =>
      ⟨state.1 p, Nat.lt_succ_of_le
        (hB state.1 (WeightedNet.markingGraph_state_reachable state) p)⟩
  /- The vector type is finite, and the encoding forgets only the reachability
     proof, so it is injective. -/
  apply Finite.of_injective toBoundedVector
  intro src tgt h
  apply Subtype.ext
  funext p
  exact congrArg (fun m => (m p).val) h

/-- For a finite place type, a net is bounded from `m₀` if and only if the
state type of its marking graph from `m₀` is finite. -/
theorem WeightedNet.boundedFrom_iff_finite_markingGraph
    {P T : Type*} [Fintype P] (net : WeightedNet P T) (m₀ : Marking P) :
    net.BoundedFrom m₀ ↔
      Finite {m : Marking P // net.markingLTS.CanReach m₀ m} :=
  ⟨WeightedNet.finite_markingGraph_of_boundedFrom,
    WeightedNet.boundedFrom_of_finite_markingGraph⟩

/-- For finitely many places, individual place bounds give a common bound. -/
theorem WeightedNet.boundedFrom_iff_forall_placeBoundedFrom
    {P T : Type*} [Finite P] (net : WeightedNet P T) (m₀ : Marking P) :
    net.BoundedFrom m₀ ↔ ∀ p, net.PlaceBoundedFrom m₀ p := by
  constructor
  · rintro ⟨B, hB⟩ p
    exact ⟨B, fun m hm => hB m hm p⟩
  · intro h
    choose bound hbound using h
    obtain ⟨B, hB⟩ := Finite.bddAbove_range bound
    exact ⟨B, fun m hm p => (hbound p m hm).trans (hB ⟨p, rfl⟩)⟩

/-- For a finite place type, finitely many markings are reachable from `m₀`
exactly when the net is bounded from `m₀`. -/
theorem WeightedNet.finite_reachable_iff_boundedFrom
    {P T : Type*} [Fintype P] (net : WeightedNet P T) (m₀ : Marking P) :
    Finite {m : Marking P // net.Reachable m₀ m} ↔ net.BoundedFrom m₀ := by
  simpa only [net.markingLTS_canReach_iff] using
    (net.boundedFrom_iff_finite_markingGraph m₀).symm

end PetriNet

/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.MarkingGraph

/-!
# Behavioural properties represented by marking graphs

This module defines four standard behavioural properties of a weighted P/T
net relative to an initial marking: deadlock freedom, liveness, weak liveness,
and reversibility. It then relates these Petri-net properties to properties of
the marking graph, following Reisig's characterisations.

The initial marking is an explicit parameter because `WeightedNet` describes
only the static net structure. It does not include an initial marking.

## Main definitions

* `WeightedNet.IsTerminal`: a marking that enables no transition.
* `WeightedNet.DeadlockFreeFrom`: every reachable marking enables a
  transition.
* `WeightedNet.LiveFrom`: every transition can eventually become enabled from
  every reachable marking.
* `WeightedNet.WeaklyLiveFrom`: every transition is enabled at some reachable
  marking.
* `WeightedNet.ReversibleFrom`: the initial marking is reachable from every
  reachable marking.

## Main results

* `WeightedNet.isTerminal_iff_markingGraph_isTerminal`: terminal markings are
  exactly the terminal states of the marking graph.
* `WeightedNet.deadlockFreeFrom_iff_markingGraph_has_outgoing`: a net is
  deadlock-free from its initial marking exactly when every state of its
  marking graph has an outgoing edge.
* `WeightedNet.deadlockFreeFrom_iff_markingGraph_no_terminal`: equivalently,
  the marking graph has no terminal state.

Termination and boundedness are treated separately: their marking-graph
characterisations require finiteness assumptions on the place or transition
types.

## References

* W. Reisig, *Understanding Petri Nets: Modeling Techniques, Analysis Methods,
  Case Studies*, Springer, 2013, Section 14.1, pp. 151–152.
  DOI: 10.1007/978-3-642-33278-4.
-/

@[expose] public section

namespace PetriNet

/-- A net is deadlock-free from `m₀` when every marking reachable from `m₀`
enables at least one transition. -/
def WeightedNet.DeadlockFreeFrom {P T : Type*} (net : WeightedNet P T)
    (m₀ : Marking P) : Prop :=
  ∀ m, net.Reachable m₀ m → ∃ t, net.Enabled m t

/-- A net is live from `m₀` when, from every marking reachable from `m₀`,
each transition can eventually become enabled. -/
def WeightedNet.LiveFrom {P T : Type*} (net : WeightedNet P T)
    (m₀ : Marking P) : Prop :=
  ∀ m, net.Reachable m₀ m → ∀ t, ∃ m', net.Reachable m m' ∧ net.Enabled m' t

/-- A net is weakly live from `m₀` when every transition is enabled at some
marking reachable from `m₀`. -/
def WeightedNet.WeaklyLiveFrom {P T : Type*} (net : WeightedNet P T)
    (m₀ : Marking P) : Prop :=
  ∀ t, ∃ m, net.Reachable m₀ m ∧ net.Enabled m t

/-- A net is reversible from `m₀` when the initial marking can be reached
again from every marking reachable from it. -/
def WeightedNet.ReversibleFrom {P T : Type*} (net : WeightedNet P T)
    (m₀ : Marking P) : Prop :=
  ∀ m, net.Reachable m₀ m → net.Reachable m m₀

/-- A net is deadlock-free from `m₀` if and only if every state of its
marking graph has an outgoing edge. This is Reisig's marking-graph
characterisation of deadlock freedom. -/
theorem WeightedNet.deadlockFreeFrom_iff_markingGraph_has_outgoing
    {P T : Type*} (net : WeightedNet P T) (m₀ : Marking P) :
    net.DeadlockFreeFrom m₀ ↔
      ∀ src, ∃ t tgt, (net.markingGraph m₀).Tr src t tgt := by
  constructor
  · intro hdeadlockFree src
    have hsrcReachable : net.Reachable m₀ src.1 :=
      net.markingLTS_canReach_iff.mp src.2
    obtain ⟨t, henabled⟩ := hdeadlockFree src.1 hsrcReachable
    obtain ⟨m', hfires⟩ := (net.enabled_iff_exists_fires src.1 t).mp henabled
    have hm'Reachable : net.Reachable m₀ m' :=
      hsrcReachable.trans ⟨[t], WeightedNet.FiresSequence.singleton hfires⟩
    let tgt : {m : Marking P // net.markingLTS.CanReach m₀ m} :=
      ⟨m', net.markingLTS_canReach_iff.mpr hm'Reachable⟩
    exact ⟨t, tgt, src.2, tgt.2, hfires⟩
  · intro houtgoing m hmReachable
    let src : {m : Marking P // net.markingLTS.CanReach m₀ m} :=
      ⟨m, net.markingLTS_canReach_iff.mpr hmReachable⟩
    obtain ⟨t, _, htr⟩ := houtgoing src
    exact ⟨t, htr.2.2.1⟩

/-- A net is deadlock-free from `m₀` if and only if its marking graph has no
terminal state. The equivalent outgoing-edge formulation is given by
`deadlockFreeFrom_iff_markingGraph_has_outgoing`. -/
theorem WeightedNet.deadlockFreeFrom_iff_markingGraph_no_terminal
    {P T : Type*} (net : WeightedNet P T) (m₀ : Marking P) :
    net.DeadlockFreeFrom m₀ ↔
      ∀ m, ¬(net.markingGraph m₀).IsTerminal m := by
  rw [net.deadlockFreeFrom_iff_markingGraph_has_outgoing m₀]
  constructor
  · intro houtgoing m hterminal
    obtain ⟨t, m', htr⟩ := houtgoing m
    exact hterminal t m' htr
  · intro hnoTerminal m
    by_contra hnoOutgoing
    push Not at hnoOutgoing
    exact hnoTerminal m hnoOutgoing

end PetriNet

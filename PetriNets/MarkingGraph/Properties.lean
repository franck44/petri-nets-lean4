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
* `WeightedNet.liveFrom_iff_markingGraph_path_to_label`: a net is live exactly
  when, from every state, there is a path to an edge carrying any chosen
  transition label.
* `WeightedNet.weaklyLiveFrom_iff_markingGraph_has_label`: a net is weakly
  live exactly when every transition labels an edge of the marking graph.
* `WeightedNet.LiveFrom.weaklyLiveFrom`: liveness implies weak liveness.

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

/-- Every net that is live from `m₀` is weakly live from `m₀`. Apply
liveness at `m₀`, which is reachable from itself by the empty firing
sequence. -/
theorem WeightedNet.LiveFrom.weaklyLiveFrom {P T : Type*}
    {net : WeightedNet P T} {m₀ : Marking P}
    (hlive : net.LiveFrom m₀) : net.WeaklyLiveFrom m₀ := by
  exact hlive m₀ (WeightedNet.Reachable.refl net m₀)

/-- A net is deadlock-free from `m₀` if and only if every state of its
marking graph has an outgoing edge. This is Reisig's marking-graph
characterisation of deadlock freedom. -/
theorem WeightedNet.deadlockFreeFrom_iff_markingGraph_has_outgoing
    {P T : Type*} (net : WeightedNet P T) (m₀ : Marking P) :
    net.DeadlockFreeFrom m₀ ↔
      ∀ src, ∃ t tgt, (net.markingGraph m₀).Tr src t tgt := by
  constructor
  · intro hdeadlockFree src
    obtain ⟨t, henabled⟩ :=
      hdeadlockFree src.1 (WeightedNet.markingGraph_state_reachable src)
    obtain ⟨tgt, htr⟩ := (net.markingGraph_enabled_iff_exists_tr src t).mp henabled
    exact ⟨t, tgt, htr⟩
  · intro houtgoing m hmReachable
    let src : {m : Marking P // net.markingLTS.CanReach m₀ m} :=
      ⟨m, net.markingLTS_canReach_iff.mpr hmReachable⟩
    obtain ⟨t, tgt, htr⟩ := houtgoing src
    exact ⟨t, (net.markingGraph_enabled_iff_exists_tr src t).mpr ⟨tgt, htr⟩⟩

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

/-- A net is live from `m₀` if and only if, from every state of its marking
graph and for every transition `t`, there is a finite path to a state with an
outgoing edge labelled by `t`. This is Reisig's marking-graph characterisation
of liveness. -/
theorem WeightedNet.liveFrom_iff_markingGraph_path_to_label
    {P T : Type*} (net : WeightedNet P T) (m₀ : Marking P) :
    net.LiveFrom m₀ ↔
      ∀ src t, ∃ ts mid tgt,
        (net.markingGraph m₀).MTr src ts mid ∧
          (net.markingGraph m₀).Tr mid t tgt := by
  constructor
  · intro hlive src t
    obtain ⟨m, hmReachable, henabled⟩ :=
      hlive src.1 (WeightedNet.markingGraph_state_reachable src) t
    obtain ⟨ts, hseq⟩ := hmReachable
    have hm₀m : net.Reachable m₀ m :=
      (WeightedNet.markingGraph_state_reachable src).trans ⟨ts, hseq⟩
    let mid : {m : Marking P // net.markingLTS.CanReach m₀ m} :=
      ⟨m, net.markingLTS_canReach_iff.mpr hm₀m⟩
    obtain ⟨tgt, htr⟩ := (net.markingGraph_enabled_iff_exists_tr mid t).mp henabled
    exact ⟨ts, mid, tgt, (net.markingGraph_mTr_iff src mid).mpr hseq,
      htr⟩
  · intro hpath m hmReachable t
    let src : {m : Marking P // net.markingLTS.CanReach m₀ m} :=
      ⟨m, net.markingLTS_canReach_iff.mpr hmReachable⟩
    obtain ⟨ts, mid, tgt, hmtr, htr⟩ := hpath src t
    exact ⟨mid.1, ⟨ts, (net.markingGraph_mTr_iff src mid).mp hmtr⟩,
      (net.markingGraph_enabled_iff_exists_tr mid t).mpr ⟨tgt, htr⟩⟩

/-- A net is weakly live from `m₀` if and only if every transition labels at
least one edge of its marking graph. This is Reisig's marking-graph
characterisation of weak liveness. -/
theorem WeightedNet.weaklyLiveFrom_iff_markingGraph_has_label
    {P T : Type*} (net : WeightedNet P T) (m₀ : Marking P) :
    net.WeaklyLiveFrom m₀ ↔
      ∀ t, ∃ src tgt, (net.markingGraph m₀).Tr src t tgt := by
  constructor
  · intro hweaklyLive t
    obtain ⟨m, hmReachable, henabled⟩ := hweaklyLive t
    let src : {m : Marking P // net.markingLTS.CanReach m₀ m} :=
      ⟨m, net.markingLTS_canReach_iff.mpr hmReachable⟩
    obtain ⟨tgt, htr⟩ := (net.markingGraph_enabled_iff_exists_tr src t).mp henabled
    exact ⟨src, tgt, htr⟩
  · intro hlabel t
    obtain ⟨src, tgt, htr⟩ := hlabel t
    exact ⟨src.1, WeightedNet.markingGraph_state_reachable src,
      (net.markingGraph_enabled_iff_exists_tr src t).mpr ⟨tgt, htr⟩⟩

end PetriNet

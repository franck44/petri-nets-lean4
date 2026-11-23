/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.CoveringGraphV2.Node
public import PetriNets.CoveringGraph.Acceleration
public import PetriNets.Monotonicity

/-!
# Covering-graph successors

Provides the successor of a covering-graph node when firing a transition.

A successor ω-marking is obtained by first computing the raw firing result
and then accelerating it with respect to the complete history of the source
node.
-/

@[expose] public section

namespace PetriNet.CoveringGraphV2

variable {P T : Type*}
variable {net : WeightedNet P T}

instance instDecidableGrowsAt {P α : Type*} [LE α] [LT α]
    (src tgt : P → α) (p : P)
    [Decidable (src ≤ tgt)] [Decidable (src p < tgt p)] :
    Decidable (src <[p] tgt) := by
  unfold Marking.GrowsAt
  infer_instance

namespace Node

section FinitePlaces

variable [FinEnum P]

/-- The places that should be accelerated when `raw` is reached from `node`.
A place belongs to this set when some marking in the complete node history is
smaller than `raw` and is strictly smaller at that place. -/
def acceleratedPlaces (raw : OmegaMarking P) (node : Node P) : Finset P :=
  Finset.univ.filter fun p =>
    ∃ a ∈ node.history, a <[p] raw

/-- A history marking witnessing pointwise growth at `p` selects `p` for
acceleration. -/
theorem mem_acceleratedPlaces {raw a : OmegaMarking P} {node : Node P}
    {p : P} (ha : a ∈ node.history) (hgrows : a <[p] raw) :
    p ∈ acceleratedPlaces raw node := by
  simp only [acceleratedPlaces, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨a, ha, hgrows⟩

end FinitePlaces

end Node

/-- The raw marking obtained by applying the firing arithmetic for `t` at
`m`. When `t` is enabled, this is its unique ω-firing result. -/
def rawSuccessor (net : WeightedNet P T) (m : OmegaMarking P)
    (t : T) : OmegaMarking P :=
  fun p => m p - net.pre p t + net.post p t

/-- Applying firing arithmetic does not change which places are equal to
`ω`. -/
theorem omegaPlaces_rawSuccessor [Fintype P]
    (m : OmegaMarking P) (t : T) :
    OmegaMarking.omegaPlaces (rawSuccessor net m t) =
      OmegaMarking.omegaPlaces m := by
  ext p
  simp [OmegaMarking.mem_omegaPlaces, rawSuccessor]

/-- The covering successor of `src` for transition `t`.

The raw firing result is accelerated with respect to the complete history of
`src`, then appended to that history. -/
def successor [FinEnum P] (net : WeightedNet P T) (src : Node P)
    (t : T) : Node P :=
  let raw := rawSuccessor net src.marking t
  src ++ OmegaMarking.accelerateFinset (Node.acceleratedPlaces raw src) raw

@[simp]
theorem successor_marking [FinEnum P] (net : WeightedNet P T)
    (src : Node P) (t : T) :
    (successor net src t).marking =
      OmegaMarking.accelerateFinset
        (Node.acceleratedPlaces (rawSuccessor net src.marking t) src)
        (rawSuccessor net src.marking t) :=
  rfl

@[simp]
theorem successor_ancestors [FinEnum P] (net : WeightedNet P T)
    (src : Node P) (t : T) :
    (successor net src t).ancestors = src.history :=
  rfl

/-- Every place already equal to `ω` remains equal to `ω` in the
successor. -/
theorem successor_preserves_top [FinEnum P] (src : Node P) (t : T) {p : P}
    (hp : src.marking p = ⊤) :
    (successor net src t).marking p = ⊤ := by
  simp [successor, OmegaMarking.accelerateFinset, rawSuccessor, hp]

/-- Every place selected by the acceleration rule is `ω` in the successor. -/
theorem successor_eq_top_of_mem_acceleratedPlaces [FinEnum P]
    (src : Node P) (t : T) {p : P}
    (hp : p ∈ Node.acceleratedPlaces
      (rawSuccessor net src.marking t) src) :
    (successor net src t).marking p = ⊤ := by
  simp [successor, OmegaMarking.accelerateFinset, hp]

/-- A covering successor over-approximates an ordinary firing step.

If `src.marking` covers the concrete marking `m` and `m` fires `t` to `m'`,
then `t` is enabled at `src.marking` and the accelerated successor covers
`m'`:

```text
          Fires t
    m --------------> m'
    |                  |
    | ≤                | ≤
    v                  v
src.marking ----t----> successor.marking
```
-/
theorem fires_le_successor [FinEnum P]
    {m m' : Marking P} {src : Node P} {t : T}
    (hcover : m.toOmega ≤ src.marking) (hfires : net.Fires m t m') :
    net.OmegaEnabled src.marking t ∧
      m'.toOmega ≤ (successor net src t).marking := by
  have homegaFires : net.OmegaFires m.toOmega t m'.toOmega :=
    (net.fires_iff_omegaFires_toOmega m m' t).mp hfires
  obtain ⟨tgt, htgt, hle⟩ := homegaFires.mono hcover
  have htgtEq : tgt = rawSuccessor net src.marking t := by
    funext p
    exact htgt.2 p
  constructor
  · exact htgt.1
  · calc
      m'.toOmega ≤ tgt := hle
      _ = rawSuccessor net src.marking t := htgtEq
      _ ≤ (successor net src t).marking := by
        intro p
        by_cases hp : p ∈ Node.acceleratedPlaces
            (rawSuccessor net src.marking t) src
        · simp [successor, OmegaMarking.accelerateFinset, hp]
        · simp [successor, OmegaMarking.accelerateFinset, hp]

/-- If a successor introduces no new `ω`-place, acceleration did not change
the raw firing result. -/
theorem successor_marking_eq_rawSuccessor_of_omegaPlaces_eq [FinEnum P]
    (src : Node P) (t : T)
    (homega : OmegaMarking.omegaPlaces src.marking =
      OmegaMarking.omegaPlaces (successor net src t).marking) :
    (successor net src t).marking = rawSuccessor net src.marking t := by
  funext p
  by_cases hp : p ∈ Node.acceleratedPlaces
      (rawSuccessor net src.marking t) src
  · have htgtTop : (successor net src t).marking p = ⊤ :=
      successor_eq_top_of_mem_acceleratedPlaces src t hp
    have hpTgt : p ∈ OmegaMarking.omegaPlaces
        (successor net src t).marking := by
      rw [OmegaMarking.mem_omegaPlaces]
      exact htgtTop
    have hpSrc : p ∈ OmegaMarking.omegaPlaces src.marking := by
      rwa [homega]
    have hpRaw : p ∈ OmegaMarking.omegaPlaces
        (rawSuccessor net src.marking t) := by
      rw [omegaPlaces_rawSuccessor]
      exact hpSrc
    rw [OmegaMarking.mem_omegaPlaces] at hpRaw
    exact htgtTop.trans hpRaw.symm
  · simp [successor, OmegaMarking.accelerateFinset, hp]

/-- An earlier marking in `src.history` cannot grow strictly at a place of
`successor net src t` when all three relevant markings have the same
`ω`-places:

```text
earlier ∈ src.history       src ──t──▶ successor net src t
```

The two equality assumptions have distinct roles:

* `homegaEarlier` says that the earlier history marking and the successor have
  the same `ω`-places;
* `homegaSrc` says that the source node and its successor have the same
  `ω`-places, so acceleration leaves the raw firing result unchanged.

Consequently, if `earlier <[p] successor.marking`, then `earlier` witnesses
that `p` must be accelerated. This makes the successor value at `p` equal to
`ω`; `homegaEarlier` then makes the earlier value equal to `ω` as well,
contradicting strict growth at `p`. -/
theorem not_growsAt_successor_of_mem_history_of_omegaPlaces_eq [FinEnum P]
    {earlier : OmegaMarking P} {src : Node P} {t : T} {p : P}
    (hmem : earlier ∈ src.history)
    (homegaEarlier : OmegaMarking.omegaPlaces earlier =
      OmegaMarking.omegaPlaces (successor net src t).marking)
    (homegaSrc : OmegaMarking.omegaPlaces src.marking =
      OmegaMarking.omegaPlaces (successor net src t).marking) :
    ¬ earlier <[p] (successor net src t).marking := by
  intro hgrows
  have hraw : (successor net src t).marking =
      rawSuccessor net src.marking t :=
    successor_marking_eq_rawSuccessor_of_omegaPlaces_eq src t homegaSrc
  have hpAccelerated : p ∈ Node.acceleratedPlaces
      (rawSuccessor net src.marking t) src := by
    apply Node.mem_acceleratedPlaces hmem
    rwa [← hraw]
  have hpTgtTop : (successor net src t).marking p = ⊤ :=
    successor_eq_top_of_mem_acceleratedPlaces src t hpAccelerated
  have hpEarlierTop : earlier p = ⊤ := by
    rw [← OmegaMarking.mem_omegaPlaces, homegaEarlier,
      OmegaMarking.mem_omegaPlaces]
    exact hpTgtTop
  have hp := hgrows.2
  rw [hpEarlierTop, hpTgtTop] at hp
  exact (lt_irrefl _ hp).elim

end PetriNet.CoveringGraphV2

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

A succesor ω-marking of a transition is obtained by first computing the raw ω-successor
and then accelerating it with respect to the complete history of the source node.
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

end PetriNet.CoveringGraphV2

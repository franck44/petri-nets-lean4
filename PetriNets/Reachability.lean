module

public import PetriNets.Basic

/-!
# Firing sequences and reachability

This module defines executions of transition sequences and the resulting
reachability relation for weighted P/T nets.
-/

@[expose] public section

namespace PetriNet


/-- `net.FiresSequence src transitions tgt` builds a proof that firing the sequence of transitions `transitions` starting from marking `src` leads to marking `tgt`.
In other words, it shows that executing the  transitions in order takes the net state from `src` to `tgt`. -/
inductive WeightedNet.FiresSequence {P T : Type*} (net : WeightedNet P T) :
    Marking P → List T → Marking P → Prop where
    /- `src` is the initial marking, `tgt` is the final marking -/
    /- the empty sequence is valid if it leaves the marking unchanged -/
  | nil (m) : net.FiresSequence m [] m
  /- a non-empty sequence is valid if the first transition fires and the remaining sequence is valid -/
  | cons {ts: List T} {src i tgt : Marking P} {t : T}
      (head : net.Fires src t i)
      (tail : net.FiresSequence i ts tgt) :
      net.FiresSequence src (t :: ts) tgt

/-- A marking is reachable from another marking when some transition sequence
takes the first marking to the second. -/
def WeightedNet.Reachable {P T : Type*} (net : PetriNet.WeightedNet P T)
    (m m' : Marking P) : Prop :=
  ∃ ts : List T, net.FiresSequence m ts m'

end PetriNet

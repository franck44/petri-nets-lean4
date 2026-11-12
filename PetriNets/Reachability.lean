module

public import PetriNets.Basic

/-!
# Firing sequences and reachability

This module defines executions of transition sequences and the resulting
reachability relation for weighted P/T nets.

## References

* W. Reisig, *Understanding Petri Nets: Modeling Techniques, Analysis Methods,
  Case Studies*, Springer, 2013, especially "Sequential and Distributed Runs",
  pp. 35–49, and "Reachability in Elementary System Nets", pp. 141–145.
  DOI: 10.1007/978-3-642-33278-4.
* T. Murata, "Petri Nets: Properties, Analysis and Applications",
  *Proceedings of the IEEE* 77(4), 1989, Section IV-A, p. 547.
  DOI: 10.1109/5.24143.
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

/-- Lift a standard firing to a singleton firing sequence. -/
theorem WeightedNet.FiresSequence.singleton {P T : Type*}
    {net : WeightedNet P T} {src tgt : Marking P} {t : T}
    (h : net.Fires src t tgt) : net.FiresSequence src [t] tgt := by
  exact WeightedNet.FiresSequence.cons h (WeightedNet.FiresSequence.nil tgt)

/-- A firing sequence h_1 ending at a marking `i` can be extended by another firing
sequence h_2 starting at `i`. The resulting proof uses the fact that the transition list is the concatenation of the two sequences. -/
theorem WeightedNet.FiresSequence.append {P T : Type*}
    {net : WeightedNet P T} {src i tgt : Marking P} {ts₁ ts₂ : List T}
    (h₁ : net.FiresSequence src ts₁ i)
    (h₂ : net.FiresSequence i ts₂ tgt) :
    net.FiresSequence src (ts₁ ++ ts₂) tgt := by
  induction h₁ with
  | nil => exact h₂
  | cons head tail ih =>
  /- h1 is head :: tail and the induction hypothesis holds for tail and h2 -/
      exact WeightedNet.FiresSequence.cons head (ih h₂)

/-- A transition sequence has a unique target marking when fired from a
 source marking. -/
theorem WeightedNet.FiresSequence.deterministic {P T : Type*}
    {net : WeightedNet P T} {src tgt₁ tgt₂ : Marking P} {ts : List T}
    (h₁ : net.FiresSequence src ts tgt₁)
    (h₂ : net.FiresSequence src ts tgt₂) : tgt₁ = tgt₂ := by
    /- induction on h₁ treating tgt₂ as arbitrary -/
  induction h₁ generalizing tgt₂ with
  | nil =>
      cases h₂
      rfl
  | cons head₁ tail₁ ih =>
      cases h₂ with
      | cons head₂ tail₂ =>
          cases WeightedNet.fires_is_deterministic head₁ head₂
          /- the two target after head₁ and head₂ must be the same -/
          exact ih tail₂

/-- A marking is reachable from another marking when some transition sequence
takes the first marking to the second. -/
def WeightedNet.Reachable {P T : Type*} (net : PetriNet.WeightedNet P T)
    (m m' : Marking P) : Prop :=
  ∃ ts : List T, net.FiresSequence m ts m'

/-- Every marking is reachable from itself by the empty firing sequence. -/
@[refl]
theorem WeightedNet.Reachable.refl {P T : Type*} (net : WeightedNet P T)
    (m : Marking P) : net.Reachable m m := by
  exact ⟨[], WeightedNet.FiresSequence.nil m⟩

/-- Reachability is transitive: consecutive witnessing firing sequences can be
concatenated. -/
@[trans]
theorem WeightedNet.Reachable.trans {P T : Type*} {net : WeightedNet P T}
    {m₁ m₂ m₃ : Marking P} (h₁ : net.Reachable m₁ m₂)
    (h₂ : net.Reachable m₂ m₃) : net.Reachable m₁ m₃ := by
  rcases h₁ with ⟨ts₁, hts₁⟩
  rcases h₂ with ⟨ts₂, hts₂⟩
  exact ⟨ts₁ ++ ts₂, WeightedNet.FiresSequence.append hts₁ hts₂⟩

-- TODO: Provide `IsRefl` and `IsTrans` instances if generic relation APIs need them.

end PetriNet

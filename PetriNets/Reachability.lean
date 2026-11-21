/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

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

/-- `net.FiresSequence src ts tgt` means that firing the transitions in `ts`
from left to right takes marking `src` to marking `tgt`. -/
inductive WeightedNet.FiresSequence {P T : Type*} (net : WeightedNet P T) :
    Marking P → List T → Marking P → Prop where
  /-- The empty sequence leaves a marking unchanged. -/
  | nil (m) : net.FiresSequence m [] m
  /-- A nonempty sequence fires its head transition, then its tail. -/
  | cons {ts : List T} {src i tgt : Marking P} {t : T}
      (head : net.Fires src t i)
      (tail : net.FiresSequence i ts tgt) :
      net.FiresSequence src (t :: ts) tgt

/-- The marking obtained by applying the token updates of a transition list
from left to right.

Like `firingResult`, this is a total function: it computes a marking even if
some transition in the list is not enabled. A proof of `FiresSequence`
additionally establishes that every transition is enabled when it is applied.
-/
def WeightedNet.firingSequenceResult {P T : Type*}
    (net : WeightedNet P T) (src : Marking P) : List T → Marking P
  | [] => src
  | t :: ts => net.firingSequenceResult (net.firingResult src t) ts

@[simp]
theorem WeightedNet.firingSequenceResult_nil {P T : Type*}
    (net : WeightedNet P T) (src : Marking P) :
    net.firingSequenceResult src [] = src :=
  rfl

@[simp]
theorem WeightedNet.firingSequenceResult_cons {P T : Type*}
    (net : WeightedNet P T) (src : Marking P) (t : T) (ts : List T) :
    net.firingSequenceResult src (t :: ts) =
      net.firingSequenceResult (net.firingResult src t) ts :=
  rfl

/-- Lift a standard firing to a singleton firing sequence. -/
theorem WeightedNet.FiresSequence.singleton {P T : Type*}
    {net : WeightedNet P T} {src tgt : Marking P} {t : T}
    (h : net.Fires src t tgt) : net.FiresSequence src [t] tgt := by
  exact WeightedNet.FiresSequence.cons h (WeightedNet.FiresSequence.nil tgt)

/-- Concatenate two firing sequences whose intermediate markings agree. -/
theorem WeightedNet.FiresSequence.append {P T : Type*}
    {net : WeightedNet P T} {src i tgt : Marking P} {ts₁ ts₂ : List T}
    (h₁ : net.FiresSequence src ts₁ i)
    (h₂ : net.FiresSequence i ts₂ tgt) :
    net.FiresSequence src (ts₁ ++ ts₂) tgt := by
  induction h₁ with
  | nil => exact h₂
  | cons head tail ih =>
      exact WeightedNet.FiresSequence.cons head (ih h₂)

/-- A transition sequence has a unique target marking when fired from a
source marking. -/
theorem WeightedNet.FiresSequence.deterministic {P T : Type*}
    {net : WeightedNet P T} {src tgt₁ tgt₂ : Marking P} {ts : List T}
    (h₁ : net.FiresSequence src ts tgt₁)
    (h₂ : net.FiresSequence src ts tgt₂) : tgt₁ = tgt₂ := by
  induction h₁ generalizing tgt₂ with
  | nil =>
      cases h₂
      rfl
  | cons head₁ tail₁ ih =>
      cases h₂ with
      | cons head₂ tail₂ =>
          cases WeightedNet.fires_is_deterministic head₁ head₂
          exact ih tail₂

/-- A marking is reachable from another marking when some transition sequence
takes the first marking to the second. -/
def WeightedNet.Reachable {P T : Type*} (net : WeightedNet P T)
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

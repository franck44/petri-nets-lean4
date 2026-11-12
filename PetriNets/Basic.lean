module

public import Mathlib
public import Cslib

/-!
# Weighted place/transition nets

This module uses the matrix-oriented presentation of a weighted P/T net

`N = (P, T, Pre, Post)`,

where `P` and `T` are the types of places and transitions and
`Pre, Post : P → T → ℕ` are the input and output multiplicity matrices.

For a place `p` and transition `t`, a positive value `Pre p t` is the weight of
the arc from `p` to `t`, and a positive value `Post p t` is the weight of the
arc from `t` to `p`. A zero matrix entry denotes that the corresponding arc is
absent; it does not represent an existing arc of weight zero.

This presentation is equivalent to the flow-relation presentation
`(P, T, F, W)`, in which `F` contains the arcs and `W` assigns a positive
weight to each arc: membership in `F` corresponds precisely to a positive
entry in `Pre` or `Post`. The matrix presentation is convenient for defining
the incidence matrix `Post - Pre`, state equations, and invariants.

The terminology follows the standard weighted P/T-net literature; see, for
example, T. Murata, "Petri Nets: Properties, Analysis and Applications",
*Proceedings of the IEEE* 77(4), 1989, pp. 541–580.
-/

namespace PetriNet

/-- A weighted place/transition net represented by its multiplicity matrices.

`pre p t` is the number of tokens consumed from place `p` when transition `t`
fires. `post p t` is the number of tokens produced in `p`. In either matrix,
zero denotes the absence of an arc.
-/
structure WeightedNet (P : Type*) (T : Type*) where
  pre : P → T → ℕ
  post : P → T → ℕ

/-- A marking assigns a token count to each place.

It defines the state of the net, as the distribution of tokens across the places.

-/
abbrev Marking (P : Type*) := P → ℕ

/-- A transition is enabled when every place contains at least the number of
tokens required by its input multiplicity. -/
def WeightedNet.Enabled {P T : Type*} (net : WeightedNet P T)
    (marking : Marking P) (transition : T) : Prop :=
  ∀ place, net.pre place transition ≤ marking place

/-- `net.Fires marking transition marking'` means that `transition` is enabled
at `marking` and that firing it produces `marking'`. -/
def WeightedNet.Fires {P T : Type*} (net : WeightedNet P T)
    (marking : Marking P) (transition : T) (marking' : Marking P) : Prop :=
  net.Enabled marking transition ∧
    ∀ place,
      marking' place = marking place - net.pre place transition + net.post place transition

/-- Firing a fixed transition from a fixed marking has a unique result i.e. is deterministic. -/
theorem WeightedNet.fires_is_deterministic {P T : Type*} {net : WeightedNet P T}
    {m m₁ m₂ : Marking P} {t : T}
    (h₁ : net.Fires m t m₁)
    (h₂ : net.Fires m t m₂) : m₁ = m₂ := by
  -- It suffices to show that for each place `p`, the token count in `m₁` equals the token count in `m₂`. We use the extensionality of functions to introduce an arbitrary place.
  funext p
  exact (h₁.right p).trans (h₂.right p).symm

end PetriNet

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

## References

* W. Reisig, *Understanding Petri Nets: Modeling Techniques, Analysis Methods,
  Case Studies*, Springer, 2013, especially "The Basic Concepts", pp. 13–24.
  DOI: 10.1007/978-3-642-33278-4.
* T. Murata, "Petri Nets: Properties, Analysis and Applications",
  *Proceedings of the IEEE* 77(4), 1989, pp. 541–580, especially Section II
  for weighted nets, markings, enabling, and firing.
  DOI: 10.1109/5.24143.
-/

@[expose] public section

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
    (m : Marking P) (t : T) : Prop :=
  ∀ p, net.pre p t ≤ m p

/-- `net.Fires m t m'` means that `t` is enabled at `m` and that firing it
produces `m'`. -/
def WeightedNet.Fires {P T : Type*} (net : WeightedNet P T)
    (m : Marking P) (t : T) (m' : Marking P) : Prop :=
  net.Enabled m t ∧
    ∀ p,
      m' p = m p - net.pre p t + net.post p t

/-- Firing a fixed transition from a fixed marking has a unique result i.e. is deterministic. -/
theorem WeightedNet.fires_is_deterministic {P T : Type*} {net : WeightedNet P T}
    {m m₁ m₂ : Marking P} {t : T}
    (h₁ : net.Fires m t m₁)
    (h₂ : net.Fires m t m₂) : m₁ = m₂ := by
  -- It suffices to show that for each place `p`, the token count in `m₁` equals the token count in `m₂`. We use the extensionality of functions to introduce an arbitrary place.
  funext p
  exact (h₁.right p).trans (h₂.right p).symm

end PetriNet

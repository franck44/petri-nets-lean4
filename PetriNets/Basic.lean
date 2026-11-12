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
structure WeightedNet (Place : Type*) (Transition : Type*) where
  pre : Place → Transition → ℕ
  post : Place → Transition → ℕ

end PetriNet

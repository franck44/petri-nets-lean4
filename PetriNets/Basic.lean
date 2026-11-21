/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import Mathlib

/-!
# Weighted place/transition nets

This module uses the matrix-oriented presentation of a weighted P/T net

`N = (P, T, Pre, Post)`,

where `P` and `T` are the types of places and transitions and
`Pre, Post : P → T → ℕ` are the pre- and post-incidence matrices.

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

/-- A weighted place/transition net represented by its pre- and post-incidence
matrices.

`pre p t` is the number of tokens consumed from place `p` when transition `t`
fires. `post p t` is the number of tokens produced in `p`. In either matrix,
zero denotes the absence of an arc.
-/
structure WeightedNet (P : Type*) (T : Type*) where
  pre : P → T → ℕ
  post : P → T → ℕ

/-- A marking assigns a token count to each place.

It is the state of a net: the distribution of tokens across its places. -/
abbrev Marking (P : Type*) := P → ℕ

/-- A transition is enabled when every place contains at least the number of
tokens specified by its pre-incidence entry. -/
def WeightedNet.Enabled {P T : Type*} (net : WeightedNet P T)
    (m : Marking P) (t : T) : Prop :=
  ∀ p, net.pre p t ≤ m p

/-- The marking obtained by applying the token update of transition `t` to
`src`.

This is a total function: it computes `src - pre(t) + post(t)` even when `t`
is not enabled. The relation `net.Fires src t tgt` additionally requires
enabledness and states that `tgt = net.firingResult src t`. -/
def WeightedNet.firingResult {P T : Type*} (net : WeightedNet P T)
    (src : Marking P) (t : T) : Marking P := fun p =>
  src p - net.pre p t + net.post p t

@[simp]
theorem WeightedNet.firingResult_apply {P T : Type*}
    (net : WeightedNet P T) (src : Marking P) (t : T) (p : P) :
    net.firingResult src t p = src p - net.pre p t + net.post p t :=
  rfl

/-- A marking `m` is dead when no transition is enabled in `m`. -/
def WeightedNet.IsDead {P T : Type*} (net : WeightedNet P T)
    (m : Marking P) : Prop :=
  ∀ t, ¬net.Enabled m t

/-- `net.Fires m t m'` means that `t` is enabled at `m` and that firing it
produces `m'`. -/
def WeightedNet.Fires {P T : Type*} (net : WeightedNet P T)
    (m : Marking P) (t : T) (m' : Marking P) : Prop :=
  net.Enabled m t ∧
    ∀ p, m' p = net.firingResult m t p

/-- The target of a valid firing is exactly the marking computed by
`firingResult`. -/
theorem WeightedNet.Fires.eq_firingResult {P T : Type*}
    {net : WeightedNet P T} {m m' : Marking P} {t : T}
    (h : net.Fires m t m') : m' = net.firingResult m t := by
  funext p
  exact h.right p

/-- A transition is enabled at a marking exactly when it can fire to some
target marking. -/
theorem WeightedNet.enabled_iff_exists_fires {P T : Type*}
    (net : WeightedNet P T) (m : Marking P) (t : T) :
    net.Enabled m t ↔ ∃ m', net.Fires m t m' := by
  constructor
  · intro henabled
    exact ⟨net.firingResult m t, henabled, fun _ => rfl⟩
  · rintro ⟨_, hfires⟩
    exact hfires.1

/-- Firing a fixed transition from a fixed marking has a unique result. -/
theorem WeightedNet.fires_is_deterministic {P T : Type*} {net : WeightedNet P T}
    {m m₁ m₂ : Marking P} {t : T}
    (h₁ : net.Fires m t m₁)
    (h₂ : net.Fires m t m₂) : m₁ = m₂ := by
  exact h₁.eq_firingResult.trans h₂.eq_firingResult.symm

end PetriNet

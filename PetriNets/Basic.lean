/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import Mathlib

/-!
# Weighted P/T nets

Provides basic definitions for a weighted place/transition net (weighted P/T
net for short)

`N = (P, T, Pre, Post)`,

where `P` and `T` are the types of places and transitions, and
`Pre, Post : P → T → ℕ` are the pre- and post-incidence functions.

A state of the net is given by a *marking*, which assigns a natural number of
tokens to each place, i.e. a function `P → ℕ`.

The state of the net changes by *firing* transitions.
Firing a transition `t` consumes `Pre p t` tokens from each place `p` and
produces `Post p t` tokens in each place `p`.

If a marking contains at least `Pre p t` tokens in each place `p`, then the
transition `t` is *enabled* and can fire.

The result of firing a transition `t` at a marking `M` is the marking `M'`
given by

```text
M' p = M p - Pre p t + Post p t.
```

A zero value of `Pre` or `Post` denotes the absence of the corresponding arc;
it does not represent an existing arc of weight zero.

## Example

A net is usually depicted as a bipartite graph with places (circles) and
transitions (rectangles), and arcs connecting them with associated weights.
Consider a net with two places `p₁`, `p₂` and one transition `t`:

```text
               2          1
       ( p₁ ) ───▶ [ t ] ───▶ ( p₂ )
```

The transition `t` consumes two tokens from `p₁` and produces one token in
`p₂`. It is enabled in any marking `(x, y)` with `x ≥ 2`, and firing it
produces the marking `(x - 2, y + 1)`. It is not enabled at `(1, 0)`, because
`p₁` does not contain enough tokens.

This net corresponds to the tuple `(P, T, Pre, Post)` with:

- `P = {p₁, p₂}`
- `T = {t}`
- `Pre` and `Post` given by

```text
Pre p₁ t = 2      Post p₁ t = 0
Pre p₂ t = 0      Post p₂ t = 1.
```

This module contains only the local, one-step semantics of a net. Firing
sequences and reachability are defined in `PetriNets.Reachability`.

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

/-! ## Nets and markings -/

/-- A weighted P/T net represented by its pre- and post-incidence functions.

`pre p t` is the number of tokens consumed from place `p` when transition `t`
fires. `post p t` is the number of tokens produced in `p`. In either function,
zero denotes the absence of an arc.
-/
structure WeightedNet (P : Type*) (T : Type*) where
  pre : P → T → ℕ
  post : P → T → ℕ

/-- A marking assigns a token count to each place.

It is the state of a net: the distribution of tokens across its places. -/
abbrev Marking (P : Type*) := P → ℕ

/-! ## Enabledness and firing -/

/-- A transition is enabled when every place contains at least the number of
tokens that the transition consumes there. Equivalently, the transition's
pre-incidence function is pointwise below the marking. -/
def WeightedNet.Enabled {P T : Type*} (net : WeightedNet P T)
    (m : Marking P) (t : T) : Prop :=
  ∀ p, net.pre p t ≤ m p

/-- The marking obtained by applying the token update of transition `t` to
`src`.

This is a total function. If `t` is not enabled, natural-number subtraction
may truncate values to zero, so the result does not represent a valid firing.
The relation `net.Fires src t tgt` additionally requires enabledness, in which
case no truncation occurs. -/
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

/-- The one-step firing relation of the `net`.

`net.Fires m t m'` means that `t` is enabled at `m` and that consuming its
pre-incidence tokens and producing its post-incidence tokens yields `m'`. -/
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

/-- The subtraction-free one-step token-balance equation. At each place, the
tokens after firing plus the tokens consumed equal the tokens before firing
plus the tokens produced. All quantities in this equation are natural
numbers. -/
theorem WeightedNet.Fires.balance {P T : Type*} {net : WeightedNet P T}
    {m m' : Marking P} {t : T} (h : net.Fires m t m') :
    ∀ p, m' p + net.pre p t = m p + net.post p t := by
  intro p
  have hfire : m' p = m p - net.pre p t + net.post p t := by
    simpa using h.right p
  have henabled := h.left p
  omega

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

/-- Firing a transition from a marking has a unique result. -/
theorem WeightedNet.fires_is_deterministic {P T : Type*} {net : WeightedNet P T}
    {m m₁ m₂ : Marking P} {t : T}
    (h₁ : net.Fires m t m₁)
    (h₂ : net.Fires m t m₂) : m₁ = m₂ := by
  exact h₁.eq_firingResult.trans h₂.eq_firingResult.symm

end PetriNet

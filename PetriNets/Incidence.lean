/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.Basic

/-!
# Incidence matrix of a weighted P/T net

Our weighted P/T net representation contains two natural-number incidence
matrices, both with places as rows and transitions as columns:

* the pre-incidence matrix `Pre` records token consumption: `Pre p t` is the
  number of tokens consumed from place `p` by transition `t`;
* the post-incidence matrix `Post` records token production: `Post p t` is the
  number of tokens produced in place `p` by transition `t`.

In Lean, `Matrix P T ℕ` is definitionally equivalent to `P → T → ℕ`.
Consequently, the functions `WeightedNet.pre` and `WeightedNet.post` already
are the pre- and post-incidence matrices; no separate definitions are needed.

The integer incidence matrix `C` combines these two matrices as follows:

`C p t = Post p t - Pre p t`.

A positive entry records net token production, while a negative entry records
net token consumption. No finiteness assumptions are needed to define the
matrix; they will be introduced later for finite sums and matrix products.

## Orientation relative to Murata

Murata uses a transition-by-place incidence matrix `A` and writes the one-step
state equation as `M' = M + Aᵀ u`, where `u` selects the transition that fires.
Our incidence matrix `C` is place-by-transition, so it corresponds to Murata's
`Aᵀ`. With our orientation, the equation is `M' = M + C u`; for a single
transition `t`, its component at place `p` is
`M' p = M p + C p t`.

## Example

Consider places `p₁, p₂` and transitions `t₁, t₂`, with
pre and post incidence matrices

```
Pre:       t₁ t₂         Post:       t₁ t₂
      p₁  [1  0]                p₁  [0  1]
      p₂  [0  2]                p₂  [1  0].
```

Thus `t₁` consumes one token from `p₁` and produces one in `p₂`, while `t₂`
consumes two tokens from `p₂` and produces one in `p₁`. The incidence matrix `C`
is

```
C = Post - Pre =
       t₁  t₂
 p₁  [-1   1]
 p₂  [ 1  -2].
```

## References

* T. Murata, "Petri Nets: Properties, Analysis and Applications",
  *Proceedings of the IEEE* 77(4), 1989, Section V-A, pp. 551–552.
  DOI: 10.1109/5.24143.
-/

@[expose] public section

namespace PetriNet

/-- The place-by-transition incidence matrix `Post - Pre`, with integer
entries. -/
def WeightedNet.incidence {P T : Type*} (net : WeightedNet P T) :
    Matrix P T ℤ :=
  fun p t => (net.post p t : ℤ) - (net.pre p t : ℤ)

/-- The natural-number token-balance equation for one firing: at each place,
the tokens after firing plus the tokens consumed equal the tokens before firing
plus the tokens produced. -/
theorem WeightedNet.Fires.balance {P T : Type*} {net : WeightedNet P T}
    {m m' : Marking P} {t : T} (h : net.Fires m t m') :
    ∀ p, m' p + net.pre p t = m p + net.post p t := by
  intro p
  have hfire := h.right p
  have henabled := h.left p
  omega

/-- The integer one-step state equation: firing `t` from `m` to `m'` changes
the token count at each place by the corresponding signed incidence entry.

The proof unfolds `WeightedNet.Fires` and `WeightedNet.incidence`, then uses
integer arithmetic with coercions from natural numbers. -/
theorem WeightedNet.Fires.int_state_equation {P T : Type*}
    {net : WeightedNet P T}
    {m m' : Marking P} {t : T} (h : net.Fires m t m') :
    ∀ p, (m' p : ℤ) = (m p : ℤ) + net.incidence p t := by
  intro p
  rw [h.right p]
  simp only [Nat.cast_add, Nat.cast_sub (h.left p), WeightedNet.incidence]
  ring

end PetriNet

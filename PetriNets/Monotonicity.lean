/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.Reachability

/-!
# Monotonicity of weighted P/T nets

Provides monotonicity results for the pointwise order on markings.
Here `m₁ ≤ m₂` means `m₁ p ≤ m₂ p` for every place `p`.

* An enabled transition remains enabled at any larger marking.
* Adding the same tokens to both ends of a firing preserves that firing.
* A firing sequence can be replayed from a larger source, reaching a marking
  at least as large as its original target.
* Reachability is preserved when the same tokens are added to the source
  and target (`Reachable.add`).
* From a larger source, some reachable marking covers the original reachable
  target (`Reachable.mono`).

Later sections use these results to replay and combine firing sequences
that grow selected places.
-/

@[expose] public section

namespace PetriNet

variable {P T : Type*} {net : WeightedNet P T}

/-! ## One-step monotonicity -/

/-- A transition enabled at a marking remains enabled at any larger
marking. -/
theorem WeightedNet.Enabled.mono {m₁ m₂ : Marking P} {t : T}
    (h : net.Enabled m₁ t) (hle : m₁ ≤ m₂) :
    net.Enabled m₂ t := by
  intro p
  exact (h p).trans (hle p)

/-- If `t` fires from `m` to `m'`, then for any additional marking `d`,
the transition also fires from `m + d` to `m' + d`.

```text
m   ──t──▶ m'
│          │
+ d        + d
▼          ▼
m+d ──t──▶ m'+d
```
-/
theorem WeightedNet.Fires.add {m m' : Marking P} {t : T}
    (h : net.Fires m t m') (d : Marking P) :
    net.Fires (m + d) t (m' + d) := by
  constructor
  · have hle: m ≤ m + d := by simp
    exact WeightedNet.Enabled.mono h.left hle
  · intro p
    have hfire : m' p = m p - net.pre p t + net.post p t := by
      simpa using h.right p
    have henabled := h.left p
    /- Use pointwise addition at `p`. -/
    change m' p + d p = (m p + d p) - net.pre p t + net.post p t
    omega

/-! ## Firing-sequence monotonicity -/

/-- Extend `WeightedNet.Fires.add` to firing sequences: if `ts` fires from
`src` to `tgt`, then for any additional marking `d`, `ts` also fires from
`src + d` to `tgt + d`.
 -/
theorem WeightedNet.FiresSequence.add {src tgt : Marking P} {ts : List T}
    (h : net.FiresSequence src ts tgt) (d : Marking P) :
    net.FiresSequence (src + d) ts (tgt + d) := by
  induction h with
  | nil src =>
      exact WeightedNet.FiresSequence.nil (src + d)
  | cons head tail ih =>
      exact WeightedNet.FiresSequence.cons (WeightedNet.Fires.add head d) ih

/-- A firing sequence can be replayed from any larger source. The
target is shifted by the additional marking `largerSrc - src`. -/
theorem WeightedNet.FiresSequence.mono
    {src tgt largerSrc : Marking P} {ts : List T}
    (h : net.FiresSequence src ts tgt) (hle : src ≤ largerSrc) :
    net.FiresSequence largerSrc ts (tgt + (largerSrc - src)) := by
  have hsrc : src + (largerSrc - src) = largerSrc := by
    funext p
    exact Nat.add_sub_of_le (hle p)
  have hshifted := h.add (largerSrc - src)
  rw [hsrc] at hshifted
  exact hshifted

/-! ## Reachability monotonicity -/

/-- Extend `WeightedNet.FiresSequence.add` to reachability: if `tgt` is
reachable from `src`, then `tgt + d` is reachable from `src + d` for any
additional marking `d`.

The same transition sequence witnesses both reachability statements. -/
theorem WeightedNet.Reachable.add {src tgt : Marking P}
    (h : net.Reachable src tgt) (d : Marking P) :
    net.Reachable (src + d) (tgt + d) := by
  rcases h with ⟨ts, hts⟩
  have hts_add := WeightedNet.FiresSequence.add hts d
  use ts

/-- Reachability is monotonic with respect to the pointwise order on markings:
if `m₁ ≤ m₂` and `m₁'` is reachable from `m₁`, then there is an `m₂'`
reachable from `m₂` such that `m₁' ≤ m₂'`.

For the proof, let `d = m₂ - m₁`. The assumption `m₁ ≤ m₂` gives
`m₁ + d = m₂` pointwise. By `WeightedNet.Reachable.add`, `m₁' + d` is
reachable from `m₁ + d = m₂`. Finally, `m₁' ≤ m₁' + d` pointwise, so take
`m₂' = m₁' + d`.
-/
theorem WeightedNet.Reachable.mono {m₁ m₂ m₁' : Marking P}
    (hreach : net.Reachable m₁ m₁')
    (hle : m₁ ≤ m₂) :
    ∃ m₂', net.Reachable m₂ m₂' ∧ m₁' ≤ m₂' := by
  let d : Marking P := m₂ - m₁
  have hsrc : m₁ + d = m₂ := by
    funext p
    change m₁ p + (m₂ p - m₁ p) = m₂ p
    exact Nat.add_sub_of_le (hle p)
  have hreach_add := WeightedNet.Reachable.add hreach d
  rw [hsrc] at hreach_add
  have htgt_le : m₁' ≤ m₁' + d := by
    intro p
    simp
  use m₁' + d

/-! ## Growth at places -/

/-- `src <[p] tgt` means that `tgt` is pointwise at least `src` and is
strictly larger at place `p`.

The value type is polymorphic, so the relation applies to any pointwise
ordered indexed family. In particular, it can be used with ordinary markings,
ω-markings, vectors represented by `Fin n → α`, and matrix rows. -/
def Marking.GrowsAt {α : Type*} [LE α] [LT α]
    (src tgt : P → α) (p : P) : Prop :=
  src ≤ tgt ∧ src p < tgt p

/-- Pointwise growth notation which is strict at the specified place. -/
notation:50 src " <[" p "] " tgt => Marking.GrowsAt src tgt p

/-- `Marking.GrowsOn src tgt A` means that `tgt` is pointwise at least
`src` and is strictly larger at every place in the finite set `A`.

Like `GrowsAt`, the relation is polymorphic in the value type. -/
def Marking.GrowsOn {α : Type*} [LE α] [LT α]
    (src tgt : P → α) (A : Finset P) : Prop :=
  src ≤ tgt ∧ ∀ p ∈ A, src p < tgt p

/-- Growth on a singleton set is growth at its unique place. -/
@[simp]
theorem Marking.growsOn_singleton {α : Type*} [LE α] [LT α]
    [DecidableEq P] (src tgt : P → α) (p : P) :
    Marking.GrowsOn src tgt {p} ↔ src <[p] tgt := by
  simp [Marking.GrowsOn, Marking.GrowsAt]

/-- A firing sequence which is nondecreasing and strictly grows every place
in `A`.

This packages the executable sequence together with the growth property used
when combining and repeating firing sequences. -/
def WeightedNet.FiresSequence.GrowsOn (net : WeightedNet P T)
    (src : Marking P) (ts : List T) (tgt : Marking P) (A : Finset P) : Prop :=
  net.FiresSequence src ts tgt ∧ Marking.GrowsOn src tgt A

/-! ## Replaying a firing sequence -/

/-- A nondecreasing firing sequence can be fired again from its target, and
the second firing adds the same marking difference as the first.

If `ts` takes `src` to `tgt` and `src ≤ tgt`, the additional marking
`tgt - src` supplies the difference between the two markings. Monotonicity
therefore shifts the original execution from `src` to `tgt` and gives the
exact next target.

```text
src ──ts──▶ tgt ──ts──▶ tgt + (tgt - src)
``` -/
theorem WeightedNet.FiresSequence.fire_again
    {src tgt : Marking P} {ts : List T}
    (hseq : net.FiresSequence src ts tgt) (hle : src ≤ tgt) :
    net.FiresSequence tgt ts (tgt + (tgt - src)) := by
  exact hseq.mono hle

/-! ## Combining growth sequences -/

/-- Combine two firing sequences `σ₁` and `σ₂` starting at `src`.
Each leaves every place with at least its starting token count.
The sequence `σ₁` strictly increases every place in `A`, and
`σ₂` strictly increases the token count at `q`.

After firing `σ₁` to reach `grownA`, replay `σ₂` from `grownA`.
Since `src ≤ grownA`, monotonicity lets `σ₂` fire there and carry
the extra tokens `grownA - src` through to its target. The concatenation
`σ₁ ++ σ₂` thus strictly increases every place in `A ∪ {q}` and
leaves every place with at least its starting token count. -/
theorem WeightedNet.FiresSequence.combine_growth_firing_sequences
    [DecidableEq P] (A : Finset P) (q : P)
    {src grownA grownQ : Marking P} {labelsA labelsQ : List T}
    (hgrowsA : WeightedNet.FiresSequence.GrowsOn net src labelsA grownA A)
    (hgrowsQ : WeightedNet.FiresSequence.GrowsOn net src labelsQ grownQ {q}) :
    ∃ tgt,
      WeightedNet.FiresSequence.GrowsOn net src
        (labelsA ++ labelsQ) tgt (insert q A) := by
  let tgt := grownQ + (grownA - src)
  have hgrowsAtQ : src <[q] grownQ :=
    Marking.growsOn_singleton src grownQ q |>.mp hgrowsQ.2
  have hreplayed := hgrowsQ.1.mono hgrowsA.2.1
  refine ⟨tgt, hgrowsA.1.append hreplayed, ?_, ?_⟩
  · intro p
    exact (hgrowsAtQ.1 p).trans (by simp [tgt])
  · intro p hp
    rw [Finset.mem_insert] at hp
    rcases hp with rfl | hp
    · exact hgrowsAtQ.2.trans_le (by simp [tgt])
    · have hgrowthAtP := hgrowsA.2.2 p hp
      have hmonoAtP := hgrowsAtQ.1 p
      change src p < grownQ p + (grownA p - src p)
      exact (Nat.lt_add_of_pos_right
        (Nat.sub_pos_of_lt hgrowthAtP)).trans_le
          (Nat.add_le_add_right hmonoAtP (grownA p - src p))

/-- Given, for each `p ∈ A`, a non-decreasing firing sequence from `src`
that strictly grows `p`, combine these sequences into a single non-decreasing
firing sequence from `src` that strictly grows every place in `A`.

For each `p ∈ A`, suppose a sequence `σₚ` fires from `src`, strictly
increases the token count at `p`, and leaves every place with at least
its starting token count. Replay each `σₚ` in turn from the marking reached
so far. The resulting sequence fires from `src`, strictly increases every
place in `A`, and leaves every place with at least its starting token count. -/
theorem WeightedNet.FiresSequence.exists_combined_growth_from
    (src : Marking P) (A : Finset P)
    (hsegments : ∀ p ∈ A, ∃ labels tgt,
      WeightedNet.FiresSequence.GrowsOn net src labels tgt {p}) :
    ∃ labels tgt,
      WeightedNet.FiresSequence.GrowsOn net src labels tgt A := by
  classical
  induction A using Finset.induction with
  | empty => exact ⟨[], src, WeightedNet.FiresSequence.nil src, le_rfl, by simp⟩
  | @insert q A hq ih =>
      obtain ⟨labelsA, grownA, hgrowsA⟩ :=
        ih (fun p hp => hsegments p (by simp [hp]))
      obtain ⟨labelsQ, grownQ, hgrowsQ⟩ :=
        hsegments q (by simp)
      obtain ⟨combined, hcombined⟩ :=
        WeightedNet.FiresSequence.combine_growth_firing_sequences A q hgrowsA hgrowsQ
      exact ⟨labelsA ++ labelsQ, combined, hcombined⟩

/-- Given, for each `p ∈ A`, a non-decreasing firing sequence `σₚ` that
ends at `base` and strictly grows `p`, combine them into a single
non-decreasing firing sequence from `base` that strictly grows every
place in `A`.

Each `σₚ` can fire again from `base` because its original source is
at most `base`. The replays now share the same source, so
`exists_combined_growth_from` combines them. -/
theorem WeightedNet.FiresSequence.exists_combined_growth
    (base : Marking P) (A : Finset P)
    (hsegments : ∀ p ∈ A, ∃ src ts,
      net.FiresSequence src ts base ∧ src <[p] base) :
    ∃ ts tgt,
      WeightedNet.FiresSequence.GrowsOn net base ts tgt A := by
  classical
  apply WeightedNet.FiresSequence.exists_combined_growth_from base A
  intro p hp
  obtain ⟨src, ts, hseq, hgrows⟩ := hsegments p hp
  refine ⟨ts, base + (base - src), hseq.fire_again hgrows.1, ?_⟩
  rw [Marking.growsOn_singleton]
  exact ⟨by simp, by simp [Nat.sub_pos_of_lt hgrows.2]⟩

end PetriNet

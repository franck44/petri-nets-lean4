/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.CoveringGraphV2.Properties
import PetriNets.LTS.Basic

/-!
# Soundness of the covering LTS

Provides soundness of the algorithm-independent covering LTS. Every node
reachable from the initial node carries an `ω`-marking that is
`ω`-coverable from the initial concrete marking.

The quantifiers in `OmegaCoverableFrom` are important. For every finite
marking represented below the reachable `ω`-marking, the theorem constructs
a possibly different reachable concrete marking that covers it. Thus an
`ω` component denotes arbitrarily large reachable token counts rather than
a concrete infinite token count.
-/

@[expose] public section

namespace PetriNet.CoveringGraphV2

variable {P T : Type*} [FinEnum P] [FinEnum T]
variable {net : WeightedNet P T}

omit [FinEnum T] in
/-- The initial marking is `K`-coverable from itself for every `K`. -/
private theorem kCoverableFrom_initial (net : WeightedNet P T)
    (m₀ : Marking P) :
    ∀ K, net.KCoverableFrom m₀ m₀ K := by
  apply net.omegaCoverableFrom_iff_forall_kCoverableFrom.mp
  exact net.omegaCoverableFrom_initial m₀

/-! ## Preservation along covering-LTS executions -/

omit [FinEnum T] in
/-- `K`-coverability is preserved by a covering-LTS edge which
introduces no new `ω`-place.

Because no place is accelerated to `ω`, the target marking is exactly the
ordinary `ω`-firing result:

```text
src.marking ──t──▶ tgt.marking = rawSuccessor net src.marking t
```

To prove target `K`-coverability, first concretise the target with `K` tokens
at every `ω`-place. Propagate this finite target backwards through `t` using
`weakestPreMarking`. Since the abstract source fires to the abstract target,
this finite predecessor lies below `src.marking`:

```text
             src.marking ──t──▶ tgt.marking
                  ▲                  ▲
                  │ ≤                │ ≤
weakestPreMarking t target ──t──▶ a marking covering target
```

The induction hypothesis says that the source is `K`-coverable for every
`K`, hence every finite marking below `src.marking` is coverable. It therefore
covers the weakest predecessor. -/
private theorem kCoverableFrom_of_coveringLTS_tr_of_no_newOmega
    {m₀ : Marking P} {src tgt : Node P} {t : T}
    (hsrc : ∀ K, net.KCoverableFrom m₀ src.marking K)
    (htr : (coveringLTS net).Tr src t tgt)
    (homega : OmegaMarking.omegaPlaces src.marking =
      OmegaMarking.omegaPlaces tgt.marking) :
    ∀ K, net.KCoverableFrom m₀ tgt.marking K := by
  have htgt := marking_eq_rawSuccessor_of_tr_of_omegaPlaces_eq htr homega
  intro K
  let target := tgt.marking.concretise fun _ => K
  let pre := net.weakestPreMarking t target
  have homegaFires : net.OmegaFires src.marking t tgt.marking := by
    rw [htgt]
    exact ⟨htr.2.1, fun _ => rfl⟩
  have hpre : pre ≤ src.marking :=
    net.weakestPreMarking_le_of_omegaFires homegaFires
      (tgt.marking.concretise_toOmega_le fun _ => K)
  apply net.coverableFrom_of_weakestPreMarking
  exact (net.omegaCoverableFrom_iff_forall_kCoverableFrom.mpr hsrc) pre hpre

/-- The places which become `ω` across one covering-LTS edge. -/
private noncomputable def newOmegaPlaces
    (src tgt : Node P) : Finset P :=
  OmegaMarking.omegaPlaces tgt.marking \
    OmegaMarking.omegaPlaces src.marking

/-- Every newly accelerated place has a growth witness realised by an earlier
node on the prefix.

For each `p ∈ newOmegaPlaces src tgt`, the prefix splits at an ancestor
whose marking is below the raw successor and strictly smaller there at `p`:

```text
Node.initial m₀ ──before──▶ ancestor ──segment──▶ src ──t──▶ raw
                                  │                         ▲
                                  └──≤, strict at p───────────────────┘
```
-/
private theorem growth_witnesses_of_newOmegaPlaces
    {m₀ : Marking P} {pre : List T}
    {src tgt : Node P} {t : T}
    (hprefix :
      (coveringLTS net).MTr (Node.initial m₀) pre src)
    (htr : (coveringLTS net).Tr src t tgt) :
    ∀ p ∈ newOmegaPlaces src tgt,
      ∃ ancestor before segment,
        (coveringLTS net).MTr (Node.initial m₀) before ancestor ∧
        (coveringLTS net).MTr ancestor segment src ∧
        ancestor.marking ≤ rawSuccessor net src.marking t ∧
        ancestor.marking p < rawSuccessor net src.marking t p := by
  intro p hp
  have hpParts := Finset.mem_sdiff.mp hp
  have hpAccelerated : p ∈ Node.acceleratedPlaces
      (rawSuccessor net src.marking t) src := by
    by_contra hpNot
    have hpTgtTop : tgt.marking p = ⊤ :=
      OmegaMarking.mem_omegaPlaces.mp hpParts.1
    have hpRawTop : rawSuccessor net src.marking t p = ⊤ := by
      rw [htr.2.2] at hpTgtTop
      simpa [successor, OmegaMarking.accelerateFinset, hpNot] using hpTgtTop
    apply hpParts.2
    rw [← omegaPlaces_rawSuccessor (net := net) src.marking t,
      OmegaMarking.mem_omegaPlaces]
    exact hpRawTop
  obtain ⟨a, ha, hgrows⟩ : ∃ a ∈ src.history,
      a <[p] rawSuccessor net src.marking t := by
    simpa [Node.acceleratedPlaces] using hpAccelerated
  rw [Node.history, List.mem_append, List.mem_singleton] at ha
  rcases ha with ha | rfl
  · rcases ancestor_eq_predecessor_of_mTr hprefix ha with hroot |
        ⟨before, ancestor, segment, _, hbefore, hsegment, _, hmarking⟩
    · simp [Node.initial, Node.root] at hroot
    · rw [← hmarking] at hgrows
      exact ⟨ancestor, before, segment, hbefore, hsegment,
        hgrows.1, hgrows.2⟩
  · exact ⟨src, pre, [], hprefix, Cslib.LTS.MTr.refl,
      hgrows.1, hgrows.2⟩

/-- Soundness is preserved by a covering-LTS edge which introduces at least
one new `ω`-place.

This is the substantive pumping case. Before implementing it, we must isolate
a short construction which combines the concrete growth witnesses using the
existing monotonicity results. -/
private theorem kCoverableFrom_of_coveringLTS_tr_of_newOmega
    {m₀ : Marking P} {pre : List T}
    {src tgt : Node P} {t : T}
    (hprefix :
      (coveringLTS net).MTr (Node.initial m₀) pre src)
    (hsrc : ∀ K, net.KCoverableFrom m₀ src.marking K)
    (htr : (coveringLTS net).Tr src t tgt) :
    ∀ K, net.KCoverableFrom m₀ tgt.marking K := by
  sorry

/-- `K`-coverability for every `K` is preserved by one covering-LTS transition reached from the
initial node.

```text
Node.initial m₀ ──prefix──▶ src ──t──▶ tgt
                                  │          │
                    every K coverable ⇒ every K coverable
```

The prefix is required because acceleration at the final edge is justified
by markings occurring earlier on that path. The proof distinguishes whether
the edge introduces a new `ω`-place. If it does not, the target is the raw
`ω`-firing result and soundness follows directly from preservation of
`ω`-coverability by an `ω`-firing. -/
private theorem kCoverableFrom_of_coveringLTS_tr
    {m₀ : Marking P} {pre : List T}
    {src tgt : Node P} {t : T}
    (hprefix :
      (coveringLTS net).MTr (Node.initial m₀) pre src)
    (hsrc : ∀ K, net.KCoverableFrom m₀ src.marking K)
    (htr : (coveringLTS net).Tr src t tgt) :
    ∀ K, net.KCoverableFrom m₀ tgt.marking K := by
  by_cases homega : OmegaMarking.omegaPlaces src.marking =
      OmegaMarking.omegaPlaces tgt.marking
  · exact kCoverableFrom_of_coveringLTS_tr_of_no_newOmega
      hsrc htr homega
  · exact kCoverableFrom_of_coveringLTS_tr_of_newOmega
      hprefix hsrc htr

/-- Extend soundness from a reachable source node along a finite covering-LTS
execution.

The proof applies `omegaCoverableFrom_of_coveringLTS_tr` to the first edge,
extends the known prefix by that edge, and continues inductively along the
remaining execution. -/
private theorem kCoverableFrom_of_mTr_from
    {m₀ : Marking P} {pre labels : List T}
    {src tgt : Node P}
    (hprefix :
      (coveringLTS net).MTr (Node.initial m₀) pre src)
    (hsrc : ∀ K, net.KCoverableFrom m₀ src.marking K)
    (hexec : (coveringLTS net).MTr src labels tgt) :
    ∀ K, net.KCoverableFrom m₀ tgt.marking K := by
  induction hexec generalizing pre with
  | refl => exact hsrc
  | @stepL src t mid labels tgt htr htail ih =>
      have hmid := kCoverableFrom_of_coveringLTS_tr
        hprefix hsrc htr
      exact ih (Cslib.LTS.MTr.stepR (coveringLTS net) hprefix htr)
        hmid

/-- **Soundness of the covering LTS.**

Every node reachable in `coveringLTS net` from the node carrying the initial
marking `m₀` denotes an `ω`-marking that is `ω`-coverable from `m₀`:

```text
Node.initial m₀ ──covering-LTS path──▶ node

For every finite demand ≤ node.marking:

                 reached
                 ▲     ▲
       Reachable │     │ demand ≤ reached
                 │     │
                m₀   demand
```

The reachable witness may depend on `demand`. -/
theorem omegaCoverableFrom_of_coveringLTS_canReach
    {m₀ : Marking P} {node : Node P}
    (hreach : (coveringLTS net).CanReach (Node.initial m₀) node) :
    net.OmegaCoverableFrom m₀ node.marking := by
  obtain ⟨labels, hexec⟩ := hreach
  apply net.omegaCoverableFrom_iff_forall_kCoverableFrom.mpr
  exact kCoverableFrom_of_mTr_from
    Cslib.LTS.MTr.refl
    (kCoverableFrom_initial net m₀) hexec

end PetriNet.CoveringGraphV2

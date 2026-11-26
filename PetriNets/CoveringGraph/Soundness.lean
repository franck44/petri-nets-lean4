/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.CoveringGraph.Properties
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

namespace PetriNet.CoveringGraph

variable {P T : Type*} [FinEnum P]
variable {net : WeightedNet P T}

/-! ## Preservation along covering-LTS executions -/

/-- The places which become `ω` across one covering-LTS edge. -/
private noncomputable def newOmegaPlaces
    (src tgt : Node P) : Finset P :=
  OmegaMarking.omegaPlaces tgt.marking \
    OmegaMarking.omegaPlaces src.marking

/-- Every place newly changed to `ω` by a covering step has a growth witness
in the source history. -/
private theorem history_growth_witnesses_of_newOmegaPlaces
    {src tgt : Node P} {t : T}
    (htr : (coveringLTS net).Tr src t tgt) :
    ∀ p ∈ newOmegaPlaces src tgt,
      ∃ earlier ∈ src.history,
        earlier <[p] rawSuccessor net src.marking t := by
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
  simpa [Node.acceleratedPlaces] using hpAccelerated

/-- Every newly accelerated place has a growth segment from an earlier node
to the source of the covering step.

For each `p ∈ newOmegaPlaces src tgt`, the prefix splits at an ancestor
whose marking is below the raw successor and strictly smaller there at `p`:

```text
Node.initial m₀ ──before──▶ ancestor ──segment──▶ src ──t──▶ raw
                                  │                         ▲
                                  └──≤, strict at p───────────────────┘
```
-/
private theorem growth_segments_of_newOmegaPlaces
    {m₀ : Marking P}
    {src tgt : Node P} {t : T}
    (hreach :
      (coveringLTS net).CanReach (Node.initial m₀) src)
    (htr : (coveringLTS net).Tr src t tgt) :
    ∀ p ∈ newOmegaPlaces src tgt,
      ∃ ancestor segment,
        (coveringLTS net).MTr ancestor segment src ∧
        ancestor.marking <[p] rawSuccessor net src.marking t := by
  obtain ⟨pre, hprefix⟩ := hreach
  intro p hp
  obtain ⟨a, ha, hgrows⟩ :=
    history_growth_witnesses_of_newOmegaPlaces htr p hp
  rw [Node.history, List.mem_append, List.mem_singleton] at ha
  rcases ha with ha | rfl
  · rcases ancestor_eq_predecessor_of_mTr hprefix ha with hroot |
        ⟨_before, ancestor, segment, _, _hbefore, hsegment, _, hmarking⟩
    · simp [Node.initial, Node.root] at hroot
    · rw [← hmarking] at hgrows
      exact ⟨ancestor, segment, hsegment, hgrows⟩
  · exact ⟨src, [], Cslib.LTS.MTr.refl, hgrows⟩

/-- Replay a covering edge as an ordinary ω-firing after setting the places
in `A` to ω at both ends. The set `A` contains every ω-place of the target. -/
private theorem omegaTr_of_coveringTr
    {src tgt : Node P} {t : T} {A : Set P}
    (htr : (coveringLTS net).Tr src t tgt)
    (hA : ∀ p, tgt.marking p = ⊤ → p ∈ A) :
    net.omegaMarkingLTS.Tr (OmegaMarking.accelerate A src.marking) t
      (OmegaMarking.accelerate A tgt.marking) := by
  classical
  constructor
  · intro p
    by_cases hp : p ∈ A
    · simp [OmegaMarking.accelerate, hp]
    · simpa [OmegaMarking.accelerate, hp] using htr.2.1 p
  · intro p
    by_cases hp : p ∈ A
    · simp [OmegaMarking.accelerate, hp]
    · have hfinite := fun heq => hp (hA p heq)
      have hacc : p ∉ Node.acceleratedPlaces
          (rawSuccessor net src.marking t) src := by
        intro ha
        apply hfinite
        rw [htr.2.2]
        exact successor_eq_top_of_mem_acceleratedPlaces _ _ ha
      rw [htr.2.2]
      simp [successor, OmegaMarking.accelerateFinset, OmegaMarking.accelerate,
        hp, hacc, rawSuccessor]

/-- Replay a covering-LTS execution as an ordinary ω-execution with the
same transition labels. Choose a set `A` containing every ω-place of the
target marking, and set all places in `A` to ω throughout the replay.

At a place in `A`, the ω value meets every transition's input demand and
stays ω after firing. Outside `A`, the place is finite at the target and
therefore stayed finite throughout the covering execution, because ω-places
persist. No covering step accelerated that place, so its values already
follow the ordinary firing rule. -/
private theorem omegaMTr_of_coveringMTr
    {src tgt : Node P} {ts : List T} {A : Set P}
    (hexec : (coveringLTS net).MTr src ts tgt)
    (hA : ∀ p, tgt.marking p = ⊤ → p ∈ A) :
    net.omegaMarkingLTS.MTr (OmegaMarking.accelerate A src.marking) ts
      (OmegaMarking.accelerate A tgt.marking) := by
  induction hexec with
  | refl => exact Cslib.LTS.MTr.refl
  | @stepL src t mid ts tgt htr htail ih =>
      have hmid p (hp : mid.marking p = ⊤) := hA p (OmegaMarking.mem_omegaPlaces.mp
        (omegaPlaces_mono_of_mTr htail (OmegaMarking.mem_omegaPlaces.mpr hp)))
      exact Cslib.LTS.MTr.stepL (omegaTr_of_coveringTr htr hmid) (ih hA)

/-- Replay a covering suffix followed by the final raw firing. The replay
starts with the source's existing ω-places set to ω. -/
private theorem omegaMTr_to_rawSuccessor
    {earlier src tgt : Node P} {segment : List T} {t : T}
    (hsegment : (coveringLTS net).MTr earlier segment src)
    (htr : (coveringLTS net).Tr src t tgt) :
    net.omegaMarkingLTS.MTr
      (OmegaMarking.accelerate {q | src.marking q = ⊤} earlier.marking)
      (segment ++ [t]) (rawSuccessor net src.marking t) := by
  have hreplay := omegaMTr_of_coveringMTr
    (A := {q | src.marking q = ⊤}) hsegment (fun _ h => h)
  have hsrc : OmegaMarking.accelerate {q | src.marking q = ⊤}
      src.marking = src.marking := by
    funext q
    by_cases hq : src.marking q = ⊤ <;> simp [OmegaMarking.accelerate, hq]
  rw [hsrc] at hreplay
  have hfire : net.OmegaFires src.marking t (rawSuccessor net src.marking t) :=
    ⟨htr.2.1, fun _ => rfl⟩
  exact Cslib.LTS.MTr.stepR net.omegaMarkingLTS hreplay hfire

/-- A step `src ─t→ tgt` in the covering LTS first fires `t` from
`src.marking` to obtain the raw firing result. It then uses the source
history to select which places of that result to set to ω. The accelerated
result is `tgt.marking`.

Equivalently, start with the raw firing result and set each place in
`newOmegaPlaces src tgt` to ω. Places that were already ω in the source
are still ω after firing, and places that remain finite in the target
keep their raw firing values.

```text

                   accelerate at A
src.marking ─────────────────────────▶ accelerate A src.marking
     │                                            │
     │ ordinary ω-firing t                        │ ordinary ω-firing t
     ▼                                            ▼
rawSuccessor ─────────────────────────────────▶ tgt.marking
                   accelerate at A

A = newOmegaPlaces src tgt
```

For this fixed set `A`, setting its places to ω commutes with the firing:
places in `A` stay at ω and all other places follow the same firing rule.
The equality proved here identifies the lower route with `tgt.marking`. -/
private theorem accelerate_newOmegaPlaces_eq_target
    {src tgt : Node P} {t : T} (htr : (coveringLTS net).Tr src t tgt) :
    OmegaMarking.accelerateFinset (newOmegaPlaces src tgt)
      (rawSuccessor net src.marking t) = tgt.marking := by
  funext p
  have hraw : rawSuccessor net src.marking t p = ⊤ ↔ src.marking p = ⊤ := by
    simp [rawSuccessor]
  have hmem : p ∈ newOmegaPlaces src tgt ↔
      tgt.marking p = ⊤ ∧ src.marking p ≠ ⊤ := by
    simp [newOmegaPlaces, OmegaMarking.mem_omegaPlaces]
  by_cases hs : src.marking p = ⊤
  · simp [OmegaMarking.accelerateFinset, hraw.mpr hs, marking_eq_top_of_tr htr hs]
  · by_cases ht : tgt.marking p = ⊤
    · simp [OmegaMarking.accelerateFinset, hmem.mpr ⟨ht, hs⟩, ht]
    · have hn : p ∉ newOmegaPlaces src tgt := fun hp => ht (hmem.mp hp).1
      rw [htr.2.2] at ht
      have ha : p ∉ Node.acceleratedPlaces (rawSuccessor net src.marking t) src :=
        fun hp => ht (successor_eq_top_of_mem_acceleratedPlaces src t hp)
      simp only [OmegaMarking.accelerateFinset, ite_eq_right hn]
      rw [htr.2.2]
      simp [successor, OmegaMarking.accelerateFinset, ha]

/-- Preserve ω-coverability across a covering edge.
The prefix reaching the source supplies the history needed for acceleration.

First fire the final transition without acceleration. The raw successor
is coverable because the source is coverable and ordinary ω-firing
preserves coverability.

For each newly accelerated place `p`, the covering history supplies a
suffix from an earlier node whose marking is at most the raw successor
and strictly smaller at `p`. Replay that suffix and the final firing as
an ordinary ω-execution by setting the old ω-places to ω throughout.
The place `p` is finite in the raw successor, so its strict growth is
preserved by the replay.

These replays supply the witnesses for
`omegaCoverableFrom_accelerateFinset_of_growsAt`. Accelerating exactly
the new ω-places of the raw successor gives the target marking. When no
new ω-places appear, the acceleration set is empty. -/
private theorem omegaCoverableFrom_of_coveringLTS_tr
    {m₀ : Marking P} {pre : List T}
    {src tgt : Node P} {t : T}
    (hprefix :
      (coveringLTS net).MTr (Node.initial m₀) pre src)
    (hsrc : net.OmegaCoverableFrom m₀ src.marking)
    (htr : (coveringLTS net).Tr src t tgt) :
    net.OmegaCoverableFrom m₀ tgt.marking := by
  let raw := rawSuccessor net src.marking t
  have hfire : net.OmegaFires src.marking t raw := ⟨htr.2.1, fun _ => rfl⟩
  have hraw := net.omegaCoverableFrom_of_omegaFires hsrc hfire
  rw [← accelerate_newOmegaPlaces_eq_target htr]
  apply net.omegaCoverableFrom_accelerateFinset_of_growsAt _ hraw
  intro p hp
  obtain ⟨earlier, segment, hsegment, hgrowth⟩ :=
    growth_segments_of_newOmegaPlaces ⟨pre, hprefix⟩ htr p hp
  have hpFinite : src.marking p ≠ ⊤ :=
    fun htop => (Finset.mem_sdiff.mp hp).2 (OmegaMarking.mem_omegaPlaces.mpr htop)
  refine ⟨_, segment ++ [t], omegaMTr_to_rawSuccessor hsegment htr, ?_, ?_⟩
  · intro q
    by_cases hq : src.marking q = ⊤
    · simp [OmegaMarking.accelerate, raw, rawSuccessor, hq]
    · simpa [OmegaMarking.accelerate, hq] using hgrowth.1 q
  · simpa [OmegaMarking.accelerate, hpFinite] using hgrowth.2

/-- Extend soundness from a reachable source node along a finite covering-LTS
execution.

The proof applies `omegaCoverableFrom_of_coveringLTS_tr` to the first edge,
extends the known prefix by that edge, and continues inductively along the
remaining execution. -/
private theorem omegaCoverableFrom_of_mTr_from
    {m₀ : Marking P} {pre labels : List T}
    {src tgt : Node P}
    (hprefix :
      (coveringLTS net).MTr (Node.initial m₀) pre src)
    (hsrc : net.OmegaCoverableFrom m₀ src.marking)
    (hexec : (coveringLTS net).MTr src labels tgt) :
    net.OmegaCoverableFrom m₀ tgt.marking := by
  induction hexec generalizing pre with
  | refl => exact hsrc
  | @stepL src t mid labels tgt htr htail ih =>
      have hmid := omegaCoverableFrom_of_coveringLTS_tr
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
  exact omegaCoverableFrom_of_mTr_from
    Cslib.LTS.MTr.refl (net.omegaCoverableFrom_initial m₀) hexec

end PetriNet.CoveringGraph

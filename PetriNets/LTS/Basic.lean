/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic

/-!
# Additional basic LTS results

This module contains generic labelled-transition-system results used by the
Petri-net development which may eventually be contributed to CSLib.
-/

@[expose] public section

namespace Cslib.LTS.CanReach

/-- Extend reachability by one transition on the right.

TODO: this generic result should eventually move to CSLib's LTS library. -/
theorem stepR {State Label : Type*} {lts : Cslib.LTS State Label}
    {src mid tgt : State} {label : Label}
    (hreach : lts.CanReach src mid) (hstep : lts.Tr mid label tgt) :
    lts.CanReach src tgt := by
  obtain ⟨labels, hexec⟩ := hreach
  exact ⟨labels ++ [label], Cslib.LTS.MTr.stepR lts hexec hstep⟩

end Cslib.LTS.CanReach

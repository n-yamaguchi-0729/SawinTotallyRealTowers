/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.LocalRing.Module
import Nyll.SchemeTheory.FiniteEtale.Henselian.ChosenLocalization

/-!
# Etaleness of a chosen Henselian local factor

An arbitrary localization of an etale algebra need not be finite over the original base.
For the localization at a prime over the closed point of a Henselian local ring, Tag 00UJ
supplies finiteness.  Flatness then makes this finite module free over the local base, hence
finitely presented.  Together with formal etaleness of localization, this upgrades the chosen
local factor itself to an etale algebra over the Henselian base.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe u v

/-- A chosen prime-local factor of an etale algebra over a Henselian local ring is etale
over the base ring.  Unlike a raw localization-finiteness assertion, the finiteness used here
is produced by `moduleFinite_localizationAtPrime_of_henselian_of_etale`. -/
theorem etale_localizationAtPrime_of_henselian_of_etale
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [HenselianLocalRing R] [Algebra.Etale R S]
    (q : Ideal S) [q.IsPrime] [q.LiesOver (IsLocalRing.maximalIdeal R)] :
    Algebra.Etale R (Localization.AtPrime q) := by
  let : Module.Finite R (Localization.AtPrime q) :=
    moduleFinite_localizationAtPrime_of_henselian_of_etale q
  let : Module.Flat R (Localization.AtPrime q) := inferInstance
  let : Module.Free R (Localization.AtPrime q) :=
    Module.free_of_flat_of_isLocalRing
  let : Module.Projective R (Localization.AtPrime q) := inferInstance
  let : Module.FinitePresentation R (Localization.AtPrime q) :=
    Module.finitePresentation_of_projective R (Localization.AtPrime q)
  exact
    { formallyEtale := inferInstance
      finitePresentation := inferInstance }

end EtaleFundamentalGroups

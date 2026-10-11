/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Smooth.Flat

/-!
# Ramification in an etale square

Suppose a ring in the upper-right corner is etale over the upper-left
corner, while the lower-right corner is etale over the lower-left corner.
For one prime in the lower-right corner and its contraction to the
lower-left corner, the two horizontal ramification indices agree.

This form does not mention a tensor presentation.  It is therefore suited
to an actual compositum normalization after the relevant connected generic
component has already been selected.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uR uB uC uS

/-- Ramification indices agree across a commutative square whose two
vertical maps are essentially of finite type and formally unramified, and
whose right vertical map is flat.

This is the local form needed for prime localizations of etale scheme
stalks: those maps need not be finitely presented. -/
theorem ramificationIdx_eq_of_formallyUnramified_flat_square
    {R : Type uR} {B : Type uB} {C : Type uC} {S : Type uS}
    [CommRing R] [CommRing B] [CommRing C] [CommRing S]
    [Algebra R B] [Algebra R C]
    [Algebra B S] [Algebra C S] [Algebra R S]
    [IsScalarTower R B S] [IsScalarTower R C S]
    [Algebra.EssFiniteType R C] [Algebra.FormallyUnramified R C]
    [Algebra.EssFiniteType B S] [Algebra.FormallyUnramified B S]
    [Module.Flat B S]
    (q : Ideal B) [q.IsPrime]
    (Q : Ideal S) [Q.IsPrime] [Q.LiesOver q] :
    Q.ramificationIdx C = q.ramificationIdx R := by
  let P := Q.under C
  let p := P.under R
  let Rp := Localization.AtPrime p
  let Cp := Localization.AtPrime P
  let SQ := Localization.AtPrime Q
  have hUnramified : Algebra.IsUnramifiedAt R P := by
    exact
      (Algebra.formallyUnramified_iff_forall.mp
        (inferInstance : Algebra.FormallyUnramified R C))
          (PrimeSpectrum.mk P inferInstance)
  let : Algebra.IsUnramifiedAt R P := hUnramified
  let : Algebra Rp Cp := Localization.AtPrime.algebraOfLiesOver p P
  let : Algebra Cp SQ := Localization.AtPrime.algebraOfLiesOver P Q
  have hpMap :
      p.map (algebraMap R Cp) = IsLocalRing.maximalIdeal Cp :=
    ((Algebra.isUnramifiedAt_iff_map_eq R p P).mp hUnramified).2
  have hPMap :
      P.map (algebraMap C Cp) = IsLocalRing.maximalIdeal Cp :=
    Localization.AtPrime.map_eq_maximalIdeal
  have hSameIdeal :
      p.map (algebraMap R SQ) = P.map (algebraMap C SQ) := by
    calc
      p.map (algebraMap R SQ) =
          (p.map (algebraMap R Cp)).map (algebraMap Cp SQ) := by
        symm
        rw [Ideal.map_map, IsScalarTower.algebraMap_eq R Cp SQ]
      _ = (P.map (algebraMap C Cp)).map (algebraMap Cp SQ) := by
        rw [hpMap, hPMap]
      _ = P.map (algebraMap C SQ) := by
        rw [Ideal.map_map, IsScalarTower.algebraMap_eq C Cp SQ]
  have hQOverP : Q.LiesOver p := Ideal.LiesOver.trans Q P p
  let : Q.LiesOver p := hQOverP
  have hAcrossBase :
      Q.ramificationIdx C = Q.ramificationIdx R := by
    rw [Ideal.ramificationIdx_eq P Q, Ideal.ramificationIdx_eq p Q,
      hSameIdeal]
  calc
    Q.ramificationIdx C = Q.ramificationIdx R := hAcrossBase
    _ = q.ramificationIdx R * Q.ramificationIdx B :=
      Ideal.ramificationIdx_tower q Q
    _ = q.ramificationIdx R := by
      rw [Ideal.ramificationIdx_eq_one Q B, mul_one]

/-- Ramification indices agree across a commutative square whose two
vertical maps are etale.

The prime `q` is the literal contraction of `Q` through `B → S`, expressed
by its `LiesOver` instance.  No residue-degree, tensor-kernel, or component
comparison is required. -/
theorem ramificationIdx_eq_of_etale_square
    {R : Type uR} {B : Type uB} {C : Type uC} {S : Type uS}
    [CommRing R] [CommRing B] [CommRing C] [CommRing S]
    [Algebra R B] [Algebra R C]
    [Algebra B S] [Algebra C S] [Algebra R S]
    [IsScalarTower R B S] [IsScalarTower R C S]
    [Algebra.Etale R C] [Algebra.Etale B S]
    (q : Ideal B) [q.IsPrime]
    (Q : Ideal S) [Q.IsPrime] [Q.LiesOver q] :
    Q.ramificationIdx C = q.ramificationIdx R := by
  exact ramificationIdx_eq_of_formallyUnramified_flat_square q Q

end EtaleFundamentalGroups

end

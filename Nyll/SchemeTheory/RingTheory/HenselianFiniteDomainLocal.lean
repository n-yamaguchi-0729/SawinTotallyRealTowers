/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.HenselianIdempotents
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Finite domains over Henselian local rings are local

The special fiber is an Artinian algebra. Two distinct maximal ideals would
be separated by an idempotent in that fiber. Henselian lifting produces an
idempotent in the domain, which must be zero or one, a contradiction.
-/

namespace SchemeTheory

universe u v

/-- A finite algebra which is a domain over a Henselian local ring has a
unique maximal ideal. No locality assumption on the finite algebra is used. -/
theorem isLocalRing_of_finite_domain_henselian
    (R : Type u) (B : Type v) [CommRing R] [HenselianLocalRing R]
    [CommRing B] [IsDomain B] [Algebra R B] [Module.Finite R B] :
    IsLocalRing B := by
  let m := IsLocalRing.maximalIdeal R
  let J : Ideal B := m.map (algebraMap R B)
  let k := R ⧸ m
  let Q := B ⧸ J
  have hJ : J ≤ Ideal.jacobson ⊥ :=
    Ideal.map_le_jacobson_bot_of_isIntegral (HenselianRing.jac (R := R) (I := m))
  obtain ⟨M, hM⟩ := Ideal.exists_maximal B
  have hJM : J ≤ M := hJ.trans (sInf_le ⟨bot_le, hM⟩)
  have hproper : J ≠ ⊤ := ne_top_of_le_ne_top hM.ne_top hJM
  let : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hproper
  let : Field k := Ideal.Quotient.field m
  let : Module.Finite k Q := Module.Finite.of_restrictScalars_finite R k Q
  let : IsArtinianRing Q := isArtinian_of_tower k inferInstance
  have hidempotent : ∀ a : Q, IsIdempotentElem a → a = 0 ∨ a = 1 := by
    intro a ha
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective a
    have hbId : IsIdempotentElem (Ideal.Quotient.mk J b) := hb.symm ▸ ha
    obtain ⟨e, he, heq⟩ := Algebra.exists_idempotent_lift_of_isIntegral m b hbId
    have hezero : e * (1 - e) = 0 := isIdempotentElem_iff_mul_one_sub_self.mp he
    rcases mul_eq_zero.mp hezero with he0 | he1
    · left
      exact (heq.trans hb).symm.trans (he0 ▸ map_zero (Ideal.Quotient.mk J))
    · right
      have heone : e = 1 := (sub_eq_zero.mp he1).symm
      exact (heq.trans hb).symm.trans (heone ▸ map_one (Ideal.Quotient.mk J))
  have hlocal : IsLocalRing Q := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal Q
    apply IsLocalRing.of_unique_max_ideal
    refine ⟨P, hP, ?_⟩
    intro N hN
    by_contra hne
    let : P.IsMaximal := hP
    obtain ⟨a, haP, ha, haN⟩ := IsArtinianRing.exists_not_mem_forall_mem_of_ne P
    rcases hidempotent a ha with hzero | hone
    · exact haP (hzero ▸ P.zero_mem)
    · exact hN.ne_top (N.eq_top_of_isUnit_mem (haN N hN.isPrime hne)
        (hone ▸ isUnit_one))
  let : IsLocalRing Q := hlocal
  let : IsLocalHom (Ideal.Quotient.mk J) := isLocalHom_of_le_jacobson_bot J hJ
  exact (Ideal.Quotient.mk J).domain_isLocalRing

end SchemeTheory

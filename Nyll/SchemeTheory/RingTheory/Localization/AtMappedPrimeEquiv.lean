/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Localizing a ring equivalence at a prime

An algebra equivalence carries the complement of a prime ideal onto the
complement of its image.  Hence it induces an algebra equivalence between
the corresponding local rings.  The explicit formula on elements from the
base ring is retained for later transport of distinguished root parameters.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uA uR uS

variable {A : Type uA} {R : Type uR} {S : Type uS}
variable [CommRing A] [CommRing R] [CommRing S]
variable [Algebra A R] [Algebra A S]

/-- An algebra equivalence maps the complement of a prime onto the complement
of the image prime. -/
theorem localizationAtMappedPrime_map_primeCompl
    (e : R ≃ₐ[A] S) (P : Ideal R) [P.IsPrime] :
    Submonoid.map e P.primeCompl =
      (P.map e.toRingEquiv).primeCompl := by
  let Q := P.map e.toRingEquiv
  let : Q.IsPrime := inferInstance
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Ideal.mem_primeCompl_iff.mpr fun hxe ↦
      hx ((Ideal.apply_mem_of_equiv_iff
        (f := e.toRingEquiv)).mp hxe)
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    exact Ideal.mem_primeCompl_iff.mpr fun hx ↦ by
      apply hy
      rw [← e.apply_symm_apply y]
      exact (Ideal.apply_mem_of_equiv_iff
        (f := e.toRingEquiv)).mpr hx

/-- An algebra equivalence induces an algebra equivalence of the local rings
at a prime and its image. -/
noncomputable def localizationAtMappedPrimeAlgEquiv
    (e : R ≃ₐ[A] S) (P : Ideal R) [P.IsPrime] :
    Localization.AtPrime P ≃ₐ[A]
      Localization.AtPrime (P.map e.toRingEquiv) := by
  let Q := P.map e.toRingEquiv
  letI : Q.IsPrime := inferInstance
  exact IsLocalization.algEquivOfAlgEquiv
    (Localization.AtPrime P) (Localization.AtPrime Q) e
      (localizationAtMappedPrime_map_primeCompl e P)

/-- On elements coming from the original ring, the localized equivalence is
the original equivalence followed by the target localization map. -/
@[simp]
theorem localizationAtMappedPrimeAlgEquiv_algebraMap
    (e : R ≃ₐ[A] S) (P : Ideal R) [P.IsPrime] (x : R) :
    localizationAtMappedPrimeAlgEquiv e P
        (algebraMap R (Localization.AtPrime P) x) =
      algebraMap S
        (Localization.AtPrime (P.map e.toRingEquiv)) (e x) := by
  let Q := P.map e.toRingEquiv
  let : Q.IsPrime := inferInstance
  exact IsLocalization.algEquivOfAlgEquiv_eq
    (H := localizationAtMappedPrime_map_primeCompl e P) x

end EtaleFundamentalGroups

end

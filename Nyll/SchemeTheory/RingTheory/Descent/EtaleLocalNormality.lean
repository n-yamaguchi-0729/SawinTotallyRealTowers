/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Descent.EtaleAtPrimeNormality
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Local normality under an etale algebra

Only the local ring of the base at the contracted prime is assumed normal.
Localizing the etale algebra over that ring and then at the lifted prime gives
the original local ring, through the actual localization comparison.
-/

noncomputable section

namespace SchemeTheory

universe u

/-- Normality of the base local ring ascends to the local ring of an etale
algebra. The original base ring need not be a domain or normal. -/
theorem isDomain_and_isIntegrallyClosed_atPrime_of_etale
    (R C : Type u) [CommRing R] [CommRing C] [Algebra R C] [Algebra.Etale R C]
    (q : Ideal C) [q.IsPrime]
    [IsDomain (Localization.AtPrime (q.under R))]
    [IsIntegrallyClosed (Localization.AtPrime (q.under R))] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  let p : Ideal R := q.under R
  let Rp := Localization.AtPrime p
  let M : Submonoid C := Algebra.algebraMapSubmonoid C p.primeCompl
  let Cp := Localization M
  let : Algebra.IsPushout R Rp C Cp :=
    (Algebra.isPushout_of_isLocalization p.primeCompl Rp C Cp).symm
  let : Algebra.Etale Rp Cp :=
    Algebra.Etale.of_equiv (Algebra.IsPushout.equiv R Rp C Cp)
  let q' : Ideal Cp := q.map (algebraMap C Cp)
  let : q'.IsPrime := IsLocalization.AtPrime.isPrime_map_of_liesOver C p Cp q
  have hcontract : q'.under C = q :=
    IsLocalization.under_map_of_isPrime_disjoint M Cp inferInstance
      (Ideal.disjoint_primeCompl_of_liesOver q p)
  have hn := Algebra.Etale.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
    Rp Cp q' (Localization.AtPrime q')
  let : IsDomain (Localization.AtPrime q') := hn.1
  let : IsIntegrallyClosed (Localization.AtPrime q') := hn.2
  have hcompl : (q'.under C).primeCompl = q.primeCompl := by
    ext c
    change c ∉ q'.under C ↔ c ∉ q
    rw [hcontract]
  let : IsLocalization.AtPrime (Localization.AtPrime q') q :=
    Eq.mp (congrArg (fun N : Submonoid C => IsLocalization N (Localization.AtPrime q')) hcompl)
      (inferInstance : IsLocalization.AtPrime (Localization.AtPrime q') (q'.under C))
  let e : Localization.AtPrime q ≃ₐ[C] Localization.AtPrime q' :=
    IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) (Localization.AtPrime q')
  exact ⟨MulEquiv.isDomain (Localization.AtPrime q') e.toRingEquiv.toMulEquiv,
    IsIntegrallyClosed.of_equiv e.symm.toRingEquiv⟩

end SchemeTheory

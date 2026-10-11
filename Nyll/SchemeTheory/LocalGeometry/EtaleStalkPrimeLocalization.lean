/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.RingHom.EssFiniteType

/-!
# Prime localizations of etale scheme stalks

An etale morphism induces a formally etale, essentially finite type map on
stalks.  These properties persist after localizing the target stalk at an
arbitrary prime.  The resulting map need not be etale: prime localization is
not finite presentation in general.  A separate theorem records the exact
finite-presentation hypothesis which upgrades the map to an etale algebra.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}}

/-- The canonical algebra structure on a prime localization of a source
stalk, over the corresponding target stalk of a scheme morphism. -/
@[reducible]
noncomputable def stalkPrimeLocalizationAlgebra
    (f : Y ⟶ X) (y : Y) (P : Ideal (Y.presheaf.stalk y)) [P.IsPrime] :
    Algebra (X.presheaf.stalk (f y)) (Localization.AtPrime P) :=
  (((algebraMap (Y.presheaf.stalk y) (Localization.AtPrime P)).comp
    (f.stalkMap y).hom)).toAlgebra

/-- The map on stalks of an etale morphism is formally etale. -/
private theorem stalkMap_ringHom_formallyEtale_of_etale
    (f : Y ⟶ X) [Etale f] (y : Y) :
    (f.stalkMap y).hom.FormallyEtale := by
  algebraize [(f.stalkMap y).hom]
  let : Algebra.FormallyUnramified (X.presheaf.stalk (f y))
      (Y.presheaf.stalk y) := by
    change (f.stalkMap y).hom.FormallyUnramified
    exact AlgebraicGeometry.FormallyUnramified.stalkMap f y
  let : Algebra.FormallySmooth (X.presheaf.stalk (f y))
      (Y.presheaf.stalk y) := by
    change (f.stalkMap y).hom.FormallySmooth
    rw [← Scheme.Hom.mem_smoothLocus]
    rw [f.smoothLocus_eq_top]
    exact Set.mem_univ y
  exact Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth

/-- The map on stalks of an etale morphism is formally etale. -/
theorem stalkMap_formallyEtale_of_etale
    (f : Y ⟶ X) [Etale f] (y : Y) :
    letI : Algebra (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) :=
      (f.stalkMap y).hom.toAlgebra
    Algebra.FormallyEtale (X.presheaf.stalk (f y))
      (Y.presheaf.stalk y) := by
  exact f.stalkMap_ringHom_formallyEtale_of_etale y

/-- Localizing the source stalk of an etale morphism at any prime remains
formally etale over the target stalk, for the literal composite algebra map. -/
private theorem stalkPrimeLocalization_ringHom_formallyEtale_of_etale
    (f : Y ⟶ X) [Etale f] (y : Y)
    (P : Ideal (Y.presheaf.stalk y)) [P.IsPrime] :
    ((algebraMap (Y.presheaf.stalk y) (Localization.AtPrime P)).comp
      (f.stalkMap y).hom).FormallyEtale := by
  let A := X.presheaf.stalk (f y)
  let B := Y.presheaf.stalk y
  let C := Localization.AtPrime P
  have hAB : (f.stalkMap y).hom.FormallyEtale := by
    change @Algebra.FormallyEtale A B _ _ (f.stalkMap y).hom.toAlgebra
    exact f.stalkMap_formallyEtale_of_etale y
  have hBC : (algebraMap B C).FormallyEtale := by
    rw [RingHom.formallyEtale_algebraMap]
    exact Algebra.FormallyEtale.of_isLocalization P.primeCompl
  change ((algebraMap B C).comp (f.stalkMap y).hom).FormallyEtale
  exact hAB.comp hBC

/-- Localizing the source stalk of an etale morphism at any prime remains
formally etale over the target stalk, for the literal composite algebra map. -/
theorem stalkPrimeLocalization_formallyEtale_of_etale
    (f : Y ⟶ X) [Etale f] (y : Y)
    (P : Ideal (Y.presheaf.stalk y)) [P.IsPrime] :
    letI : Algebra (X.presheaf.stalk (f y)) (Localization.AtPrime P) :=
      f.stalkPrimeLocalizationAlgebra y P
    Algebra.FormallyEtale (X.presheaf.stalk (f y))
      (Localization.AtPrime P) := by
  exact f.stalkPrimeLocalization_ringHom_formallyEtale_of_etale y P

/-- Localizing the source stalk of an etale morphism at any prime is
essentially of finite type over the target stalk. -/
theorem stalkPrimeLocalization_essFiniteType_of_etale
    (f : Y ⟶ X) [Etale f] (y : Y)
    (P : Ideal (Y.presheaf.stalk y)) [P.IsPrime] :
    letI : Algebra (X.presheaf.stalk (f y)) (Localization.AtPrime P) :=
      f.stalkPrimeLocalizationAlgebra y P
    Algebra.EssFiniteType (X.presheaf.stalk (f y))
      (Localization.AtPrime P) := by
  let A := X.presheaf.stalk (f y)
  let B := Y.presheaf.stalk y
  let C := Localization.AtPrime P
  have hAB : (f.stalkMap y).hom.EssFiniteType :=
    AlgebraicGeometry.LocallyOfFiniteType.stalkMap f y
  have hBC : (algebraMap B C).EssFiniteType := by
    rw [RingHom.essFiniteType_algebraMap]
    exact Algebra.EssFiniteType.of_isLocalization C P.primeCompl
  change ((algebraMap B C).comp (f.stalkMap y).hom).EssFiniteType
  exact hAB.comp hBC

/-- The prime-localized stalk map is etale exactly when finite presentation
is supplied in addition to the canonical formal-etaleness result. -/
theorem stalkPrimeLocalization_etale_of_finitePresentation
    (f : Y ⟶ X) [Etale f] (y : Y)
    (P : Ideal (Y.presheaf.stalk y)) [P.IsPrime]
    (hfp :
      letI : Algebra (X.presheaf.stalk (f y)) (Localization.AtPrime P) :=
        f.stalkPrimeLocalizationAlgebra y P
      Algebra.FinitePresentation (X.presheaf.stalk (f y))
        (Localization.AtPrime P)) :
    letI : Algebra (X.presheaf.stalk (f y)) (Localization.AtPrime P) :=
      f.stalkPrimeLocalizationAlgebra y P
    Algebra.Etale (X.presheaf.stalk (f y))
      (Localization.AtPrime P) := by
  let A := X.presheaf.stalk (f y)
  let B := Y.presheaf.stalk y
  let C := Localization.AtPrime P
  let phi := (algebraMap B C).comp (f.stalkMap y).hom
  change phi.Etale
  exact @Algebra.Etale.mk A C _ _ phi.toAlgebra
    (f.stalkPrimeLocalization_ringHom_formallyEtale_of_etale y P) hfp

end AlgebraicGeometry.Scheme.Hom

end

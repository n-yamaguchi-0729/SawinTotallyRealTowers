/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Etale.ResidueFieldExtension
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Local Noetherian base change realizing a residue extension

A finite separable extension of the residue field of a Noetherian local
ring is realized by localizing an actual etale neighborhood at its supplied
prime. The resulting ring is Noetherian and faithfully flat over the
original local ring. The residue-field equivalence is compatible with the
canonical map of local residue fields.
The maximal ideal of the original ring generates the new maximal ideal,
so the closed-fibre base change is exactly the new residue field.

The localization need not itself be finitely presented over the original
ring; its flatness and the displayed residue compatibility are the facts
needed for the proper-section base-change argument.
-/

noncomputable section

namespace Algebra.Etale

universe u v

/-- A finite separable extension of a local residue field comes from an actual
Noetherian faithfully flat local base change, with its canonical residue map. -/
theorem exists_faithfullyFlat_local_residueField_extension
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (L : Type v) [Field L] [Algebra (IsLocalRing.ResidueField A) L]
    [FiniteDimensional (IsLocalRing.ResidueField A) L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) L] :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : IsLocalRing B)
      (_ : IsNoetherianRing B) (_ : Module.FaithfullyFlat A B)
      (_ : IsLocalHom (algebraMap A B)),
      ∃ e : IsLocalRing.ResidueField B ≃+* L,
        e.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap A B)) =
          algebraMap (IsLocalRing.ResidueField A) L ∧
        (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
          IsLocalRing.maximalIdeal B := by
  let p : Ideal A := IsLocalRing.maximalIdeal A
  let eκ : IsLocalRing.ResidueField A ≃+* p.ResidueField :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal p (Localization.AtPrime p)).toRingEquiv
  let : Algebra p.ResidueField L :=
    ((algebraMap (IsLocalRing.ResidueField A) L).comp eκ.symm.toRingHom).toAlgebra
  have hScalar : (algebraMap p.ResidueField L).comp eκ.toRingHom =
      (RingEquiv.refl L).toRingHom.comp (algebraMap (IsLocalRing.ResidueField A) L) := by
    ext x
    change algebraMap (IsLocalRing.ResidueField A) L (eκ.symm (eκ x)) =
      algebraMap (IsLocalRing.ResidueField A) L x
    rw [eκ.symm_apply_apply]
  have : FiniteDimensional p.ResidueField L :=
    Module.Finite.of_equiv_equiv eκ (RingEquiv.refl L) hScalar
  have : Algebra.IsSeparable p.ResidueField L :=
    Algebra.IsSeparable.of_equiv_equiv eκ (RingEquiv.refl L) hScalar
  obtain ⟨R, hR, hAR, hEtale, q, hqPrime, hqOver, e, he⟩ :=
    exists_residueField_extension p L
  let B : Type u := Localization.AtPrime q
  have hRNoetherian : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing A R
  have hBNoetherian : IsNoetherianRing B := inferInstance
  have hBFlat : Module.Flat A B := inferInstance
  have hMaximal : (IsLocalRing.maximalIdeal B).comap (algebraMap A B) = p := by
    rw [IsScalarTower.algebraMap_eq A R B, ← Ideal.comap_comap]
    change ((IsLocalRing.maximalIdeal B).under R).under A = p
    rw [IsLocalization.AtPrime.under_maximalIdeal B q]
    exact (q.over_def p).symm
  have hLocal : IsLocalHom (algebraMap A B) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap A B)).out 1 5).mpr hMaximal
  have hFaithfullyFlat : Module.FaithfullyFlat A B :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hEssential : Algebra.EssFiniteType A B := inferInstance
  have hUnramified : Algebra.FormallyUnramified A B := inferInstance
  have hMapMaximal : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B :=
    Algebra.FormallyUnramified.map_maximalIdeal (R := A) (S := B)
  have hResidue : IsLocalRing.ResidueField.map (algebraMap A B) =
      (Ideal.ResidueField.map p q (algebraMap A R) (q.over_def p)).comp eκ.toRingHom := by
    ext x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    rw [IsLocalRing.ResidueField.map_residue, RingHom.comp_apply]
    have hκa : eκ.toRingHom (IsLocalRing.residue A a) = algebraMap A p.ResidueField a :=
      IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk p (Localization.AtPrime p) a
    rw [hκa, Ideal.ResidueField.map_algebraMap]
    change IsLocalRing.residue B (algebraMap A B a) =
      IsLocalRing.residue B (algebraMap R B (algebraMap A R a))
    exact congrArg (IsLocalRing.residue B) (IsScalarTower.algebraMap_apply A R B a)
  refine ⟨B, inferInstance, inferInstance, inferInstance, hBNoetherian,
    hFaithfullyFlat, hLocal, e, ?_, hMapMaximal⟩
  rw [hResidue, ← RingHom.comp_assoc, he]
  exact hScalar

end Algebra.Etale

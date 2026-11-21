/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidue
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidueCommon
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidueCore
public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import Nyll.GaloisCohomology.Cyclic.NormKernelVanishing

/-!
# The global norm-residue symbol for finite Galois extensions

For an arbitrary finite Galois extension of number fields, the global
norm-residue quotient is the abelianization of the genuine Galois group:

`C_K / N_{L/K} C_L ≃ Gal(L / K)ᵃᵇ`.

The abelian specialization in `GlobalNormResidue` identifies this target
further with `Gal(L / K)`.  This file retains the abelianization and therefore
states global reciprocity at its full finite-Galois generality.
-/



@[expose] public section

open scoped IsMulCommutative NumberField
open NumberField

noncomputable section

universe u v

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open KummerTheory


section AbelianSpecialization

variable
    (F : Type u) (E : Type v) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    [FiniteDimensional F E] [IsAbelianGalois F E]

private theorem
    globalNormResidueAbelianizationEquiv_abelianSpecialization_apply
    (q :
      Additive
        (IdeleClassGroup F ⧸
          (_root_.ideleClassNorm F E).range)) :
    MulEquiv.toAdditive
          (Group.Abelianization.equivOfComm :
            Gal(E / F) ≃*
              Group.Abelianization (Gal(E / F))).symm
        (globalNormResidueAbelianizationEquiv F E q) =
      globalNormResidueEquiv F E q :=
  rfl

/-- For an abelian extension, composing the finite-Galois equivalence with
the canonical equivalence from the Galois abelianization recovers the usual
global norm-residue equivalence. -/
theorem globalNormResidueAbelianizationEquiv_abelianSpecialization :
    (globalNormResidueAbelianizationEquiv F E).trans
        (MulEquiv.toAdditive
          (Group.Abelianization.equivOfComm :
            Gal(E / F) ≃*
              Group.Abelianization (Gal(E / F))).symm) =
      globalNormResidueEquiv F E := by
  apply AddEquiv.ext
  intro q
  exact
    globalNormResidueAbelianizationEquiv_abelianSpecialization_apply
      F E q

/-- In the canonical direction used by the global reciprocity isomorphism,
the finite-Galois construction likewise specializes to the ordinary
abelian reciprocity equivalence. -/
theorem globalReciprocityAbelianizationEquiv_abelianSpecialization :
    (MulEquiv.toAdditive
        (Group.Abelianization.equivOfComm :
          Gal(E / F) ≃*
            Group.Abelianization (Gal(E / F)))).trans
      (globalReciprocityAbelianizationEquiv F E) =
        globalReciprocityEquiv F E := by
  change
    ((globalNormResidueAbelianizationEquiv F E).trans
      (MulEquiv.toAdditive
        (Group.Abelianization.equivOfComm :
          Gal(E / F) ≃*
            Group.Abelianization (Gal(E / F))).symm)).symm =
      (globalNormResidueEquiv F E).symm
  exact
    congrArg AddEquiv.symm
      (globalNormResidueAbelianizationEquiv_abelianSpecialization F E)

private theorem
    globalNormResidueAbelianizationMonoidHom_abelianSpecialization_apply
    (c : IdeleClassGroup F) :
    (Group.Abelianization.equivOfComm :
        Gal(E / F) ≃*
          Group.Abelianization (Gal(E / F))).symm
        (globalNormResidueAbelianizationMonoidHom F E c) =
      globalNormResidueMonoidHom F E c := by
  simpa only [
    globalNormResidueAbelianizationMonoidHom_apply,
    globalNormResidueMonoidHom_apply,
    MulEquiv.toAdditive_apply_apply,
    MonoidHom.toAdditive_apply_apply,
    MulEquiv.coe_toMonoidHom,
    toMul_ofMul] using
      congrArg Additive.toMul
        (globalNormResidueAbelianizationEquiv_abelianSpecialization_apply
          F E
          (Additive.ofMul
            (QuotientGroup.mk'
              (_root_.ideleClassNorm F E).range c)))

/-- The finite-Galois norm-residue homomorphism specializes to the ordinary
abelian global Artin homomorphism after the canonical target
identification. -/
theorem
    globalNormResidueAbelianizationMonoidHom_abelianSpecialization :
    (Group.Abelianization.equivOfComm :
        Gal(E / F) ≃*
          Group.Abelianization (Gal(E / F))).symm.toMonoidHom.comp
        (globalNormResidueAbelianizationMonoidHom F E) =
      globalNormResidueMonoidHom F E := by
  apply MonoidHom.ext
  intro c
  exact
    globalNormResidueAbelianizationMonoidHom_abelianSpecialization_apply
      F E c

/-- The idele-level finite-Galois symbol has the same abelian
specialization, after pulling both class symbols back along
`I_F → C_F`. -/
theorem
    globalNormResidueAbelianizationIdeleMonoidHom_abelianSpecialization :
    (Group.Abelianization.equivOfComm :
        Gal(E / F) ≃*
          Group.Abelianization (Gal(E / F))).symm.toMonoidHom.comp
        (globalNormResidueAbelianizationIdeleMonoidHom F E) =
      (globalNormResidueMonoidHom F E).comp
        (IdeleGroup.toStandardClass F) := by
  apply MonoidHom.ext
  intro a
  simpa only [
    MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom,
    globalNormResidueAbelianizationIdeleMonoidHom_apply] using
      globalNormResidueAbelianizationMonoidHom_abelianSpecialization_apply
        F E
        (IdeleGroup.toStandardClass F a)

end AbelianSpecialization

end Reciprocity
end GlobalClassFieldTheory

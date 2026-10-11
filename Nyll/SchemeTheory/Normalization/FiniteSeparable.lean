/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Nyll.SchemeTheory.Normalization.Normal

/-!
# Finite normalizations in separable function-field extensions

This file records the scheme-level form of the trace-dual finiteness theorem:
over a locally Noetherian normal integral scheme, normalization in a finite
separable extension of the function field is finite.
-/


noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

namespace Scheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- The algebra structure on a field extension induced from an affine chart
through the function field. -/
@[reducible]
def affineExtensionAlgebra (U : X.Opens) [Nonempty U]
    (L : Type u) [CommRing L] [Algebra X.functionField L] : Algebra Γ(X, U) L :=
  (X.germToFunctionField U ≫
    CommRingCat.ofHom (algebraMap X.functionField L)).hom.toAlgebra

/-- The algebra structure on a field extension induced from a local ring
through the function field. -/
@[reducible]
def stalkExtensionAlgebra (x : X)
    (L : Type u) [CommRing L] [Algebra X.functionField L] :
    Algebra (X.presheaf.stalk x) L :=
  ((algebraMap X.functionField L).comp
    (algebraMap (X.presheaf.stalk x) X.functionField)).toAlgebra

section AffineIntegralClosure

variable [IsNormalIntegral X] [IsLocallyNoetherian X]
variable (U : X.affineOpens) [Nonempty U.1]
variable (L : Type u) [Field L] [Algebra X.functionField L]
variable [FiniteDimensional X.functionField L] [Algebra.IsSeparable X.functionField L]

local instance : Algebra Γ(X, U.1) L := X.affineExtensionAlgebra U.1 L
local instance : IsScalarTower Γ(X, U.1) X.functionField L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- On a nonempty affine chart of a normal locally Noetherian integral scheme,
the integral closure in a finite separable extension of the function field is
module-finite. -/
theorem affineIntegralClosure_finite :
    Module.Finite Γ(X, U.1) (integralClosure Γ(X, U.1) L) := by
  let : IsNoetherianRing Γ(X, U.1) :=
    IsLocallyNoetherian.component_noetherian U
  let : IsIntegrallyClosed Γ(X, U.1) :=
    IsNormalIntegral.affine_isIntegrallyClosed U.1 U.2
  let : IsFractionRing Γ(X, U.1) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U.1 U.2
  exact IsIntegralClosure.finite Γ(X, U.1) X.functionField L
    (integralClosure Γ(X, U.1) L)

end AffineIntegralClosure

section StalkIntegralClosure

variable [IsNormalIntegral X] [IsLocallyNoetherian X]
variable (x : X)
variable (L : Type u) [Field L] [Algebra X.functionField L]
variable [FiniteDimensional X.functionField L] [Algebra.IsSeparable X.functionField L]

local instance : Algebra (X.presheaf.stalk x) L :=
  X.stalkExtensionAlgebra x L
local instance : IsScalarTower (X.presheaf.stalk x) X.functionField L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The integral closure of any local ring in a finite separable extension
of the function field is module-finite. -/
theorem stalkIntegralClosure_finite :
    Module.Finite (X.presheaf.stalk x)
      (integralClosure (X.presheaf.stalk x) L) := by
  let : IsIntegrallyClosed (X.presheaf.stalk x) :=
    IsNormalIntegral.stalk_isIntegrallyClosed x
  exact IsIntegralClosure.finite
    (X.presheaf.stalk x) X.functionField L
      (integralClosure (X.presheaf.stalk x) L)

end StalkIntegralClosure

/-- The generic-point morphism associated to an extension of the function field. -/
def genericExtensionMorphism (L : Type u) [CommRing L] [Algebra X.functionField L] :
    Spec (.of L) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) ≫
    X.fromSpecStalk (genericPoint X)

@[simp]
lemma genericExtensionMorphism_apply_closedPoint (L : Type u) [Field L]
    [Algebra X.functionField L] :
    X.genericExtensionMorphism L (IsLocalRing.closedPoint (CommRingCat.of L)) = genericPoint X := by
  erw [genericExtensionMorphism, Scheme.Hom.comp_apply, Spec_closedPoint,
    Scheme.fromSpecStalk_closedPoint]

lemma genericExtensionMorphism_preimage_eq_top (L : Type u) [Field L]
    [Algebra X.functionField L] (U : X.Opens) [Nonempty U] :
    X.genericExtensionMorphism L ⁻¹ᵁ U = ⊤ := by
  apply top_unique
  rintro y -
  change X.genericExtensionMorphism L y ∈ U
  rw [Subsingleton.elim y (IsLocalRing.closedPoint (CommRingCat.of L)),
    genericExtensionMorphism_apply_closedPoint]
  exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
    (by simpa using (inferInstance : Nonempty U))

/-- Sections on the inverse image of a nonempty open under the generic
extension morphism identify canonically with the extension field. -/
def genericExtensionSectionsIso (L : Type u) [Field L]
    [Algebra X.functionField L] (U : X.Opens) [Nonempty U] :
    Γ(Spec (.of L), X.genericExtensionMorphism L ⁻¹ᵁ U) ≅ CommRingCat.of L :=
  let hU : X.genericExtensionMorphism L (IsLocalRing.closedPoint (CommRingCat.of L)) ∈ U := by
    rw [genericExtensionMorphism_apply_closedPoint]
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
      (by simpa using (inferInstance : Nonempty U))
  (Spec (.of L)).presheaf.mapIso
      (eqToIso (Scheme.preimage_eq_top_of_closedPoint_mem
        (X.genericExtensionMorphism L) hU).symm).op ≪≫
    Scheme.ΓSpecIso (.of L)

lemma genericExtensionSectionsIso_hom_app (L : Type u) [Field L]
    [Algebra X.functionField L] (U : X.Opens) [Nonempty U] (r : Γ(X, U)) :
    (X.genericExtensionSectionsIso L U).hom
        ((X.genericExtensionMorphism L).app U r) =
      algebraMap X.functionField L (X.germToFunctionField U r) := by
  let hU : X.genericExtensionMorphism L
      (IsLocalRing.closedPoint (CommRingCat.of L)) ∈ U := by
    rw [genericExtensionMorphism_apply_closedPoint]
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
      (by simpa using (inferInstance : Nonempty U))
  have h₁ := Scheme.germ_stalkClosedPointTo
    (f := X.genericExtensionMorphism L) U hU
  have h₂ := Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk
    (X := X) (R := CommRingCat.of L)
    (CommRingCat.ofHom (algebraMap X.functionField L)) U hU
  have H : (X.genericExtensionMorphism L).app U ≫
      (X.genericExtensionSectionsIso L U).hom =
      X.germToFunctionField U ≫
        CommRingCat.ofHom (algebraMap X.functionField L) := by
    calc
      _ = X.presheaf.germ U _ hU ≫
          Scheme.stalkClosedPointTo (X.genericExtensionMorphism L) := by
        simpa [genericExtensionSectionsIso] using h₁.symm
      _ = _ := by
        unfold genericExtensionMorphism
        convert h₂ using 1
        all_goals rfl
  exact congrArg (fun q : Γ(X, U) ⟶ CommRingCat.of L ↦ q.hom r) H

section ExtensionSections

variable (L : Type u) [Field L] [Algebra X.functionField L]
variable (U : X.Opens) [Nonempty U]

local instance : Algebra Γ(X, U)
    Γ(Spec (.of L), X.genericExtensionMorphism L ⁻¹ᵁ U) :=
  ((X.genericExtensionMorphism L).app U).hom.toAlgebra

local instance : Algebra Γ(X, U) L := X.affineExtensionAlgebra U L

/-- The section-ring identification over a nonempty open, as an algebra
equivalence over the base chart. -/
def genericExtensionSectionsAlgEquiv :
    Γ(Spec (.of L), X.genericExtensionMorphism L ⁻¹ᵁ U) ≃ₐ[Γ(X, U)] L :=
  AlgEquiv.ofRingEquiv
    (f := (X.genericExtensionSectionsIso L U).commRingCatIsoToRingEquiv)
    (X.genericExtensionSectionsIso_hom_app L U)

end ExtensionSections

end Scheme

namespace Scheme.Hom

variable {Y Z : Scheme.{u}} (f : Y ⟶ Z) [QuasiCompact f] [QuasiSeparated f]

/-- A relative normalization is finite as soon as its affine integral-closure
charts are module-finite. -/
private theorem isFinite_fromNormalization_of_finite_integralClosure
    (hfinite : ∀ (U : Z.Opens) (_hU : IsAffineOpen U),
      letI := (f.app U).hom.toAlgebra
      Module.Finite Γ(Z, U) (integralClosure Γ(Z, U) Γ(Y, f ⁻¹ᵁ U))) :
    IsFinite f.fromNormalization := by
  refine { finite_app := ?_ }
  intro U hU
  let := (f.app U).hom.toAlgebra
  rw [f.fromNormalization_app hU]
  exact RingHom.Finite.comp
    (f.normalizationObjIso hU).symm.commRingCatIsoToRingEquiv.finite
    (show (algebraMap Γ(Z, U)
      (integralClosure Γ(Z, U) Γ(Y, f ⁻¹ᵁ U))).Finite from
      hfinite U hU)

/-- The relative normalization of a normal locally Noetherian integral scheme
in a finite separable extension of its function field is finite. -/
theorem isFinite_fromNormalization_genericExtension
    (X : Scheme.{u}) [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L] [Algebra.IsSeparable X.functionField L] :
    IsFinite (X.genericExtensionMorphism L).fromNormalization := by
  apply isFinite_fromNormalization_of_finite_integralClosure
    (X.genericExtensionMorphism L)
  intro U hU
  let := ((X.genericExtensionMorphism L).app U).hom.toAlgebra
  cases isEmpty_or_nonempty U with
  | inl hEmpty =>
      have hUbot : U = ⊥ := U.not_nonempty_iff_eq_bot.mp fun hU =>
        let ⟨x, hx⟩ := hU
        hEmpty.false ⟨x, hx⟩
      subst U
      have : Subsingleton
          Γ(Spec (.of L), X.genericExtensionMorphism L ⁻¹ᵁ (⊥ : X.Opens)) := by
        simpa using (inferInstance : Subsingleton Γ(Spec (.of L), (⊥ : (Spec (.of L)).Opens)))
      apply Module.Finite.of_surjective
        (Algebra.linearMap Γ(X, (⊥ : X.Opens))
          (integralClosure Γ(X, (⊥ : X.Opens))
            Γ(Spec (.of L), X.genericExtensionMorphism L ⁻¹ᵁ (⊥ : X.Opens))))
      intro x
      exact ⟨0, Subsingleton.elim _ _⟩
  | inr hNonempty =>
      let : Nonempty U := hNonempty
      let : Algebra Γ(X, U) L := X.affineExtensionAlgebra U L
      let e := X.genericExtensionSectionsAlgEquiv L U
      let eInt := e.mapIntegralClosure
      have hL : Module.Finite Γ(X, U) (integralClosure Γ(X, U) L) :=
        X.affineIntegralClosure_finite ⟨U, hU⟩ L
      change (algebraMap Γ(X, U)
        (integralClosure Γ(X, U)
          Γ(Spec (.of L), X.genericExtensionMorphism L ⁻¹ᵁ U))).Finite
      rw [show algebraMap Γ(X, U)
          (integralClosure Γ(X, U)
            Γ(Spec (.of L), X.genericExtensionMorphism L ⁻¹ᵁ U)) =
          eInt.symm.toRingEquiv.toRingHom.comp
            (algebraMap Γ(X, U) (integralClosure Γ(X, U) L)) by
        ext r
        exact congrArg Subtype.val (eInt.symm.commutes r).symm]
      exact RingHom.Finite.comp eInt.symm.toRingEquiv.finite
        (show (algebraMap Γ(X, U) (integralClosure Γ(X, U) L)).Finite from hL)

end Scheme.Hom

end AlgebraicGeometry

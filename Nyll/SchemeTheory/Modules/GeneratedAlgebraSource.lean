/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.AffineSourceColimit
import Nyll.SchemeTheory.Modules.DirectImageAlgebra
import Nyll.SchemeTheory.Modules.GeneratedAlgebraLocalization
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# The original source maps to its generated relative algebra model

The inclusion of the actual generated section rings induces a map of the
literal spectrum diagrams. The previously proved colimit with vertex the
original affine-morphism source gives the scheme morphism. Its composite
with the generated model's structure morphism is the original morphism.
Consequently source surjectivity supplies surjectivity of the model.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.DirectImageAlgebra

variable {T X : Scheme.{u}} (g : T ⟶ X) [IsAffineHom g]
variable [(RelativeSpec.underlyingModule (structureMap g)).IsQuasicoherent]
variable (N : SheafOfModules.Submodule (RelativeSpec.underlyingModule (structureMap g)))
variable [(show X.Modules from N.toSheafOfModules).IsQuasicoherent]

local instance generatedDiagram_isLocallyDirected :
    ((GeneratedAlgebra.gluingData (structureMap g) N).functor ⋙
      Scheme.forget).IsLocallyDirected :=
  Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin
    (GeneratedAlgebra.gluingData (structureMap g) N)

/-- The actual generated-ring inclusion, mapped contravariantly by `Spec`. -/
def generatedDiagramMap :
    AffineSourceColimit.diagram g ⟶ (GeneratedAlgebra.gluingData (structureMap g) N).functor :=
  Functor.whiskerRight
    (Functor.whiskerLeft (AffineZariskiSite.toOpensFunctor X).op
      (GeneratedAlgebra.inclusion (structureMap g) N.toSubmodule)).rightOp Scheme.Spec

private def generatedCocone : Cocone (AffineSourceColimit.diagram g) where
  pt := GeneratedAlgebra.scheme (structureMap g) N
  ι := generatedDiagramMap g N ≫
    (colimit.cocone (GeneratedAlgebra.gluingData (structureMap g) N).functor).ι

/-- The map from the original scheme source to the actual generated
relative model, using the original source's proved colimit. -/
def toGenerated : T ⟶ GeneratedAlgebra.scheme (structureMap g) N :=
  (AffineSourceColimit.coconeIsColimit g).desc (generatedCocone g N)

/-- On a literal source affine chart, the new morphism is `Spec` of the
actual inclusion of generated sections. -/
@[reassoc]
theorem fromSpec_toGenerated (U : X.AffineZariskiSite) :
    (U.2.preimage g).fromSpec ≫ toGenerated g N =
      Spec.map ((GeneratedAlgebra.inclusion (structureMap g) N.toSubmodule).app (op U.1)) ≫
        colimit.ι (GeneratedAlgebra.gluingData (structureMap g) N).functor U :=
  (AffineSourceColimit.coconeIsColimit g).fac (generatedCocone g N) U

omit [IsAffineHom g] in
private theorem generatedChart_toBase (U : X.AffineZariskiSite) :
    colimit.ι (GeneratedAlgebra.gluingData (structureMap g) N).functor U ≫
        GeneratedAlgebra.toBase (structureMap g) N =
      Spec.map ((GeneratedAlgebra.structureMap (structureMap g) N.toSubmodule).app (op U.1)) ≫
        U.2.fromSpec := by
  have h := (GeneratedAlgebra.gluingData (structureMap g) N).ι_toBase U
  change
    colimit.ι (GeneratedAlgebra.gluingData (structureMap g) N).functor U ≫
        GeneratedAlgebra.toBase (structureMap g) N =
      (Spec.map ((GeneratedAlgebra.structureMap (structureMap g) N.toSubmodule).app (op U.1)) ≫
        U.2.isoSpec.inv) ≫ U.1.ι at h
  exact h.trans (Category.assoc
    (Spec.map ((GeneratedAlgebra.structureMap (structureMap g) N.toSubmodule).app (op U.1)))
    U.2.isoSpec.inv U.1.ι)

/-- The actual original source morphism factors through the generated model. -/
@[reassoc]
theorem toGenerated_toBase :
    toGenerated g N ≫ GeneratedAlgebra.toBase (structureMap g) N = g := by
  apply (AffineSourceColimit.coconeIsColimit g).hom_ext
  intro U
  let R : CommRingCat.{u} := Γ(X, U.1)
  let B : CommRingCat.{u} := Γ(T, g ⁻¹ᵁ U.1)
  let C : CommRingCat.{u} :=
    (GeneratedAlgebra.presheaf (structureMap g) N.toSubmodule).obj (op U.1)
  let a : R ⟶ C := (GeneratedAlgebra.structureMap (structureMap g) N.toSubmodule).app (op U.1)
  let b : C ⟶ B := (GeneratedAlgebra.inclusion (structureMap g) N.toSubmodule).app (op U.1)
  let γ : R ⟶ B := g.app U.1
  let Y : Scheme.{u} := GeneratedAlgebra.scheme (structureMap g) N
  let t : T ⟶ Y := toGenerated g N
  let q : Y ⟶ X := GeneratedAlgebra.toBase (structureMap g) N
  let p : Spec B ⟶ T := (U.2.preimage g).fromSpec
  let v : Spec R ⟶ X := U.2.fromSpec
  let c : Spec C ⟶ Y :=
    colimit.ι (GeneratedAlgebra.gluingData (structureMap g) N).functor U
  let k : Spec B ⟶ Spec C := Spec.map b
  let s : Spec C ⟶ Spec R := Spec.map a
  have hp : p ≫ t = k ≫ c := fromSpec_toGenerated g N U
  have hc : c ≫ q = s ≫ v := generatedChart_toBase g N U
  have hstructure : a ≫ b = γ :=
    congrArg (fun τ => τ.app (op U.1))
      (GeneratedAlgebra.structureMap_inclusion (structureMap g) N.toSubmodule)
  have hmap : k ≫ s = Spec.map γ :=
    (Spec.map_comp a b).symm.trans (congrArg (fun z : R ⟶ B => Spec.map z) hstructure)
  have happ : Spec.map γ ≫ v = p ≫ g :=
    (congrArg (fun z : R ⟶ B => Spec.map z ≫ v) (g.app_eq_appLE (U := U.1))).trans
      (IsAffineOpen.SpecMap_appLE_fromSpec g U.2 (U.2.preimage g) le_rfl)
  calc
    p ≫ (t ≫ q) = (p ≫ t) ≫ q := (Category.assoc p t q).symm
    _ = (k ≫ c) ≫ q := congrArg (fun z : Spec B ⟶ Y => z ≫ q) hp
    _ = k ≫ (c ≫ q) := Category.assoc k c q
    _ = k ≫ (s ≫ v) := congrArg (fun z : Spec C ⟶ X => k ≫ z) hc
    _ = (k ≫ s) ≫ v := (Category.assoc k s v).symm
    _ = Spec.map γ ≫ v := congrArg (fun z : Spec B ⟶ Spec R => z ≫ v) hmap
    _ = p ≫ g := happ

/-- Surjectivity of the original morphism gives surjectivity of the actual
generated model's structure map. -/
theorem surjective_toBase [Surjective g] :
    Surjective (GeneratedAlgebra.toBase (structureMap g) N) := by
  have : Surjective (toGenerated g N ≫ GeneratedAlgebra.toBase (structureMap g) N) := by
    rw [toGenerated_toBase]
    infer_instance
  exact Surjective.of_comp (toGenerated g N) (GeneratedAlgebra.toBase (structureMap g) N)

end AlgebraicGeometry.Scheme.DirectImageAlgebra

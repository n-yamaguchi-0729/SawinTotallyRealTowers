/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Stalk localization in an affine chart

The local-ring isomorphism induced by the open chart identifies its literal
prime localization map with the canonical map from the original stalk.
-/


noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
  (p : Spec Γ(X, U))

local instance : p.asIdeal.IsPrime := p.isPrime

/-- The stalk at the image of a point of an affine chart is its coordinate
ring localized at the actual prime. -/
def IsAffineOpen.stalkIsoLocalization :
    X.presheaf.stalk (hU.fromSpec p) ≅ CommRingCat.of (Localization.AtPrime p.asIdeal) :=
  asIso (hU.fromSpec.stalkMap p) ≪≫ Spec.stalkIso Γ(X, U) p

/-- The affine-chart local-ring isomorphism intertwines the two actual maps
back to the ambient scheme. -/
@[reassoc]
theorem IsAffineOpen.SpecMap_stalkIsoLocalization_fromSpecStalk :
    Spec.map (hU.stalkIsoLocalization p).hom ≫ X.fromSpecStalk (hU.fromSpec p) =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.AtPrime p.asIdeal))) ≫
        hU.fromSpec := by
  rw [IsAffineOpen.stalkIsoLocalization, Iso.trans_hom, asIso_hom, Spec.map_comp,
    Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
    ← Category.assoc, Spec.fromSpecStalk_eq, ← Spec.map_comp]
  have hbase : CommRingCat.ofHom
      (algebraMap Γ(X, U) (Localization.AtPrime p.asIdeal)) ≫
        (Spec.stalkIso Γ(X, U) p).inv =
      (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec Γ(X, U)).presheaf.germ ⊤ p trivial :=
    Spec.algebraMap_stalkIso_inv (R := Γ(X, U)) p
  have h : ((Scheme.ΓSpecIso Γ(X, U)).inv ≫
      (Spec Γ(X, U)).presheaf.germ ⊤ p trivial) ≫ (Spec.stalkIso Γ(X, U) p).hom =
      CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.AtPrime p.asIdeal)) :=
    (congrArg (fun k => k ≫ (Spec.stalkIso Γ(X, U) p).hom) hbase.symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => CommRingCat.ofHom
          (algebraMap Γ(X, U) (Localization.AtPrime p.asIdeal)) ≫ k)
            (Iso.inv_hom_id (Spec.stalkIso Γ(X, U) p))).trans (Category.comp_id _)))
  exact congrArg (fun k => Spec.map k ≫ hU.fromSpec) h

end AlgebraicGeometry

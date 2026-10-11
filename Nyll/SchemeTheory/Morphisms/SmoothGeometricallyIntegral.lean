/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.LocalGeometry.ConnectedDomainStalks
import Nyll.SchemeTheory.LocalGeometry.SmoothStalkNormality
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smooth geometrically connected morphisms are geometrically integral

After an arbitrary field-valued base change, smoothness supplies domain
stalks and local Noetherianity. Geometric connectedness supplies connectedness,
so the resulting scheme is integral.
-/

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

/-- Every smooth geometrically connected morphism is geometrically integral. -/
theorem Smooth.geometricallyIntegral_of_geometricallyConnected
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [GeometricallyConnected f] :
    GeometricallyIntegral f := by
  constructor
  intro K _ x P fst p h
  let : Smooth p := MorphismProperty.of_isPullback h inferInstance
  let : ConnectedSpace P :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) x fst p h
  let : IsDomain Γ(Spec (CommRingCat.of K), ⊤) :=
    Function.Injective.isDomain (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.injective
  let : IsIntegrallyClosed Γ(Spec (CommRingCat.of K), ⊤) :=
    IsIntegrallyClosed.of_equiv
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  let : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian p
  exact isIntegral_of_connected_of_isDomain_stalk P
    (fun z => (Smooth.isDomain_and_isIntegrallyClosed_stalk p z).1)

end AlgebraicGeometry

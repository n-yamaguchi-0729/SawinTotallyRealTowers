/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Etale.Field

/-!
# Reducedness of etale morphisms

An etale algebra over a field is reduced, because it is essentially of finite
type and formally unramified.  Applying this on an affine cover after an
arbitrary field-valued base change shows that every etale morphism is
geometrically reduced.  Combined with Mathlib's flat descent theorem, this
also gives reducedness of an etale source over a locally Noetherian reduced
base.

Mathlib defines `Etale`, `GeometricallyReduced`, and the relevant reducedness
descent theorem, but currently does not provide the implication proved here.
-/

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

/-- An etale morphism of schemes is geometrically reduced. -/
theorem Etale.geometricallyReduced
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] :
    GeometricallyReduced f := by
  constructor
  intro K _ y Z fst snd h
  let : Etale snd := MorphismProperty.of_isPullback h inferInstance
  let (i : Z.affineCover.I₀) : IsReduced (Z.affineCover.X i) := by
    let g : Z.affineCover.X i ⟶ Spec (.of K) := Z.affineCover.f i ≫ snd
    let R := Γ(Spec (.of K), ⊤)
    let T := Γ(Z.affineCover.X i, ⊤)
    let φ := g.appLE (⊤ : (Spec (.of K)).Opens) (⊤ : (Z.affineCover.X i).Opens)
      (by simp)
    have hφ : φ.hom.Etale := by
      have : Etale g := by dsimp [g]; infer_instance
      exact g.etale_appLE (isAffineOpen_top _) (isAffineOpen_top _) (by simp)
    let : Field R :=
      ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.isField
        (Field.toIsField K)).toField
    let := φ.hom.toAlgebra
    let : Algebra.Etale R T := hφ.toAlgebra
    let : _root_.IsReduced T :=
      Algebra.FormallyUnramified.isReduced_of_field R T
    exact isReduced_of_isAffine_isReduced (Z.affineCover.X i)
  exact IsReduced.of_openCover Z Z.affineCover

/-- The source of an etale morphism over a locally Noetherian reduced scheme
is reduced. -/
theorem Etale.isReduced_of_isLocallyNoetherian
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]
    [IsReduced Y] [IsLocallyNoetherian Y] : IsReduced X := by
  let : GeometricallyReduced f := Etale.geometricallyReduced f
  exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian f

end AlgebraicGeometry

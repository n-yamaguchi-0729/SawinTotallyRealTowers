/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.ResidueField

/-!
# From the literal residue action to a fixed residue-field point

If a scheme endomorphism fixes a point and its induced residue-field map
is the canonical identification at that same point, naturality identifies
its composite with the actual canonical residue-field point morphism.
Conversely, injectivity of residue-field maps proves the point and residue
condition at every point in any fixed test morphism's image. No geometric-point
comparison is assumed.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- The original point-and-residue inertia condition fixes the actual
canonical residue-field point morphism. The equality of residue maps uses
the canonical identification supplied by the given equality of points. -/
theorem fixes_fromSpecResidueField_of_residueFieldMap_eq
    {X : Scheme.{u}} (e : X ⟶ X) (x : X) (hx : e x = x)
    (hres : e.residueFieldMap x = (X.residueFieldCongr hx).hom) :
    X.fromSpecResidueField x ≫ e = X.fromSpecResidueField x := by
  calc
    X.fromSpecResidueField x ≫ e =
        Spec.map (e.residueFieldMap x) ≫ X.fromSpecResidueField (e x) :=
      (e.SpecMap_residueFieldMap_fromSpecResidueField x).symm
    _ = Spec.map (X.residueFieldCongr hx).hom ≫ X.fromSpecResidueField (e x) := by
      rw [hres]
    _ = X.fromSpecResidueField x := Scheme.residueFieldCongr_fromSpecResidueField hx

/-- A fixed test morphism forces the original point-and-residue inertia
condition at every point of its image. Residue-field injectivity supplies
the cancellation; no residue-action comparison is assumed. -/
theorem residueFieldMap_eq_of_comp_eq_self
    {X T : Scheme.{u}} (e : X ⟶ X) (z : T ⟶ X) (hz : z ≫ e = z) (t : T) :
    ∃ hy : e (z t) = z t,
      e.residueFieldMap (z t) = (X.residueFieldCongr hy).hom := by
  have hy : e (z t) = z t :=
    (Scheme.Hom.comp_apply z e t).symm.trans
      (congrArg (fun a : T ⟶ X => a t) hz)
  have hcomp : (z ≫ e).residueFieldMap t =
      (X.residueFieldCongr hy).hom ≫ z.residueFieldMap t :=
    Scheme.Hom.residueFieldMap_congr hz t
  have : Mono (z.residueFieldMap t) :=
    ConcreteCategory.mono_of_injective _ (z.residueFieldMap t).hom.injective
  refine ⟨hy, ?_⟩
  apply (cancel_mono (z.residueFieldMap t)).mp
  exact (Scheme.residueFieldMap_comp z e t).symm.trans hcomp

end AlgebraicGeometry.Scheme.Hom

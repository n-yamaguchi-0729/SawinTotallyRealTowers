/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FiniteEtale.Algebra.EtaleQuotientLift
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-!
# Affine étale lifts across closed immersions

An affine étale scheme over a closed subscheme of an affine scheme lifts to
an affine étale scheme over the ambient scheme. We apply the shared algebraic
lifting theorem to the actual maps on global sections and use the spectrum
of the tensor product to construct the base-change isomorphism over the
closed subscheme. No nilpotence, noetherian, or field hypothesis is needed.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace AlgebraicGeometry.Etale

/-- An affine étale scheme over an affine closed subscheme lifts to the ambient affine
scheme, with an isomorphism over the closed subscheme after base change. -/
theorem exists_affine_lift_of_closedImmersion
    {X Z W : Scheme.{u}} [IsAffine X] [IsAffine W]
    (i : Z ⟶ X) [IsClosedImmersion i] (f : W ⟶ Z) [Etale f] :
    ∃ (V : Scheme.{u}) (_ : IsAffine V) (g : V ⟶ X), Etale g ∧
      ∃ e : pullback i g ≅ W, e.hom ≫ f = pullback.fst i g := by
  have hclosed := IsClosedImmersion.isAffine_surjective_of_isAffine i
  have : IsAffine Z := hclosed.1
  let : Algebra Γ(X, ⊤) Γ(Z, ⊤) := i.appTop.hom.toAlgebra
  let : Algebra Γ(Z, ⊤) Γ(W, ⊤) := f.appTop.hom.toAlgebra
  have : Algebra.Etale Γ(Z, ⊤) Γ(W, ⊤) :=
    HasRingHomProperty.appTop (P := @Etale) f inferInstance
  obtain ⟨T, _, _, hT, ⟨e⟩⟩ :=
    Algebra.Etale.exists_etale_lift_of_surjective
      (R := Γ(Z, ⊤)) (S := Γ(W, ⊤)) Γ(X, ⊤) hclosed.2
  let b : Spec Γ(Z, ⊤) ⟶ Spec Γ(X, ⊤) := Spec.map i.appTop
  let t : Spec (.of T) ⟶ Spec Γ(X, ⊤) :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) T))
  have : Etale t :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr hT)
  let g : Spec (.of T) ⟶ X := t ≫ X.isoSpec.inv
  let ep : pullback b t ≅ Spec Γ(W, ⊤) :=
    pullbackSpecIso Γ(X, ⊤) Γ(Z, ⊤) T ≪≫
      (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op).symm
  have hep : ep.hom ≫ Spec.map f.appTop = pullback.fst b t := by
    change ((pullbackSpecIso Γ(X, ⊤) Γ(Z, ⊤) T).hom ≫
      Spec.map (CommRingCat.ofHom e.symm.toRingHom)) ≫ Spec.map f.appTop = _
    rw [Category.assoc, ← Spec.map_comp]
    have hc : f.appTop ≫ CommRingCat.ofHom e.symm.toRingHom =
        CommRingCat.ofHom (algebraMap Γ(Z, ⊤) (Γ(Z, ⊤) ⊗[Γ(X, ⊤)] T)) := by
      apply CommRingCat.hom_ext
      exact RingHom.ext e.symm.commutes
    rw [hc]
    exact pullbackSpecIso_hom_fst Γ(X, ⊤) Γ(Z, ⊤) T
  let m : pullback i g ⟶ pullback b t :=
    pullback.map i g b t Z.isoSpec.hom (𝟙 _) X.isoSpec.hom
      (Scheme.isoSpec_hom_naturality i).symm
      (by simp only [g, Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp])
  have : IsIso m := by dsimp only [m]; infer_instance
  let E : pullback i g ≅ W := asIso m ≪≫ ep ≪≫ W.isoSpec.symm
  refine ⟨Spec (.of T), inferInstance, g, inferInstance, E, ?_⟩
  apply (cancel_mono Z.isoSpec.hom).mp
  rw [Category.assoc, ← Scheme.isoSpec_hom_naturality f]
  simp only [E, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc,
    Iso.inv_hom_id_assoc, hep]
  exact pullback.lift_fst _ _ _

end AlgebraicGeometry.Etale

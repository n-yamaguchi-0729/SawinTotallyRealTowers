/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.AlgebraicGeometry.Scheme

/-!
# The actual section map of a morphism from a spectrum

The ΓSpec conversion is performed in this generic owner. The exported
constructor and its equations keep that intermediate section ring out of
callers that use the resulting morphism.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- The actual global-section map of a morphism from an affine spectrum.
Its intermediate sections of `Spec S` stay inside this generic constructor. -/
def specLiftSectionMap {S : Type u} [CommRing S] {X : Scheme.{u}}
    (l : Spec (.of S) ⟶ X) : Γ(X, ⊤) ⟶ CommRingCat.of S :=
  l.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom

theorem specLiftSectionMap_comp_endomorphism
    {S : Type u} [CommRing S] {X : Scheme.{u}}
    (l : Spec (.of S) ⟶ X) (τ : S →+* S)
    (hl : Spec.map (CommRingCat.ofHom τ) ≫ l = l) :
    specLiftSectionMap l ≫ CommRingCat.ofHom τ = specLiftSectionMap l := by
  let e : Γ(Spec (.of S), ⊤) ⟶ CommRingCat.of S :=
    (Scheme.ΓSpecIso (CommRingCat.of S)).hom
  change (l.appTop ≫ e) ≫ CommRingCat.ofHom τ = l.appTop ≫ e
  calc
    (l.appTop ≫ e) ≫ CommRingCat.ofHom τ =
        l.appTop ≫ (e ≫ CommRingCat.ofHom τ) := Category.assoc _ _ _
    _ = l.appTop ≫ ((Spec.map (CommRingCat.ofHom τ)).appTop ≫ e) :=
      congrArg (fun k : Γ(Spec (.of S), ⊤) ⟶ CommRingCat.of S => l.appTop ≫ k)
        (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom τ)).symm
    _ = (l.appTop ≫ (Spec.map (CommRingCat.ofHom τ)).appTop) ≫ e :=
      (Category.assoc _ _ _).symm
    _ = (Spec.map (CommRingCat.ofHom τ) ≫ l).appTop ≫ e :=
      congrArg (fun k : Γ(X, ⊤) ⟶ Γ(Spec (.of S), ⊤) => k ≫ e)
        (Scheme.Hom.comp_appTop (Spec.map (CommRingCat.ofHom τ)) l).symm
    _ = l.appTop ≫ e :=
      congrArg (fun k : Spec (.of S) ⟶ X => k.appTop ≫ e) hl

/-- The section-map constructor on an actual affine spectrum morphism is
the native ΓSpec map of its ring homomorphism. -/
theorem specLiftSectionMap_specMap
    {B S : Type u} [CommRing B] [CommRing S] (g : B →+* S) :
    specLiftSectionMap (Spec.map (CommRingCat.ofHom g)) =
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom ≫ CommRingCat.ofHom g :=
  Scheme.ΓSpecIso_naturality (CommRingCat.ofHom g)

/-- Evaluating the actual section map of an affine spectrum morphism returns
exactly its original ring-category morphism. -/
theorem specLiftSectionMap_affine {B S : CommRingCat.{u}} (g : B ⟶ S) :
    (Scheme.ΓSpecIso B).inv ≫ specLiftSectionMap (Spec.map g) = g := by
  change (Scheme.ΓSpecIso B).inv ≫
    ((Spec.map g).appTop ≫ (Scheme.ΓSpecIso S).hom) = g
  rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

end AlgebraicGeometry

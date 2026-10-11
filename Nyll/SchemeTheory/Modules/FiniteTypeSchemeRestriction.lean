/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.FiniteTypePushforward
import Nyll.SchemeTheory.Modules.QuasicoherentLocal
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.Module
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# Finite type under actual open restriction and slice equivalence

The native site-equivalence coefficient isomorphisms transport the actual
finite local generating families in both directions. These comparisons
connect slice-site finite type with the geometric restriction functor.
-/

noncomputable section

universe u v₁ u₁ v₂ u₂

open CategoryTheory

private theorem overPostContinuousOfDenseEquivalence
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
    [G.IsEquivalence] [G.IsDenseSubsite J K] (W : C) :
    (Over.post (X := W) G).IsContinuous (J.over W) (K.over (G.obj W)) :=
  Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat _ (Over.post (X := W) G))
    (CoverPreserving.overPost W (Functor.IsDenseSubsite.coverPreserving J K G))

namespace TopologicalSpace.Opens

/-- The actual slice-to-open equivalence preserves finite local generators. -/
theorem isFiniteType_sheafOfModulesEquivOver
    {X : TopCat.{u}} (V : Opens X) (R : X.Sheaf RingCat.{u})
    (M : SheafOfModules.{u} (R.over V)) (hM : M.IsFiniteType) :
    ((V.sheafOfModulesEquivOver R).functor.obj M).IsFiniteType := by
  let α : V.sheafRestrict.obj R ⟶
      (V.overEquivalence.inverse.sheafPushforwardContinuous RingCat.{u}
        (_root_.Opens.grothendieckTopology V)
        ((_root_.Opens.grothendieckTopology X).over V)).obj (R.over V) :=
    (V.overPullbackSheafEquivOver.app R).inv
  have : IsIso α := (V.overPullbackSheafEquivOver.app R).isIso_inv
  have : ∀ W : Opens V,
      (Over.post (X := W) V.overEquivalence.inverse).IsContinuous
        ((_root_.Opens.grothendieckTopology V).over W)
        (((_root_.Opens.grothendieckTopology X).over V).over
          (V.overEquivalence.inverse.obj W)) :=
    fun W => overPostContinuousOfDenseEquivalence _ _ V.overEquivalence.inverse W
  exact SheafOfModules.isFiniteType_pushforward_of_isLeftAdjoint
    V.overEquivalence.inverse α (V.sheafOfModulesEquivOverUnit R) hM

/-- The actual open-to-slice inverse equivalence preserves finite local generators. -/
theorem isFiniteType_sheafOfModulesEquivOver_inverse
    {X : TopCat.{u}} (V : Opens X) (R : X.Sheaf RingCat.{u})
    (M : SheafOfModules.{u} (V.sheafRestrict.obj R)) (hM : M.IsFiniteType) :
    ((V.sheafOfModulesEquivOver R).inverse.obj M).IsFiniteType := by
  let α : R.over V ⟶
      (V.overEquivalence.functor.sheafPushforwardContinuous RingCat.{u}
        ((_root_.Opens.grothendieckTopology X).over V)
        (_root_.Opens.grothendieckTopology V)).obj (V.sheafRestrict.obj R) :=
    (V.sheafRestrictSheafEquivOver.app R).inv
  have : IsIso α := (V.sheafRestrictSheafEquivOver.app R).isIso_inv
  have : ∀ W : Over V,
      (Over.post (X := W) V.overEquivalence.functor).IsContinuous
        (((_root_.Opens.grothendieckTopology X).over V).over W)
        ((_root_.Opens.grothendieckTopology V).over
          (V.overEquivalence.functor.obj W)) :=
    fun W => overPostContinuousOfDenseEquivalence _ _ V.overEquivalence.functor W
  exact SheafOfModules.isFiniteType_pushforward_of_isLeftAdjoint
    V.overEquivalence.functor α (V.sheafOfModulesEquivOverInverseUnit R) hM

end TopologicalSpace.Opens

namespace AlgebraicGeometry.Scheme.Modules

/-- Finite type on the actual slice site gives finite type on the open subscheme. -/
theorem isFiniteType_restrict_of_over
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (hM : (M.over U).IsFiniteType) : (M.restrict U.ι).IsFiniteType := by
  have h : ((overEquiv U).functor.obj (M.over U)).IsFiniteType :=
    U.isFiniteType_sheafOfModulesEquivOver X.ringCatSheaf (M.over U) hM
  let A : SheafOfModules.{u} U.toScheme.ringCatSheaf :=
    (overEquiv U).functor.obj (M.over U)
  let B : SheafOfModules.{u} U.toScheme.ringCatSheaf := M.restrict U.ι
  let e : A ≅ B := (sheafOfModulesEquivalence U.toScheme).functor.mapIso
    ((overFunctorEquiv U).app M)
  exact SheafOfModules.IsFiniteType.of_iso
    (C := U.toScheme.Opens) (R := U.toScheme.ringCatSheaf) (M := A) (N := B) e h

/-- Finite type on the open subscheme gives finite type on the actual slice site. -/
theorem isFiniteType_over_of_restrict
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (hM : (M.restrict U.ι).IsFiniteType) : (M.over U).IsFiniteType := by
  have h : ((overEquiv U).inverse.obj (M.restrict U.ι)).IsFiniteType :=
    U.isFiniteType_sheafOfModulesEquivOver_inverse X.ringCatSheaf (M.restrict U.ι) hM
  let e : (overEquiv U).inverse.obj (M.restrict U.ι) ≅ M.over U :=
    (overEquiv U).inverse.mapIso ((overFunctorEquiv U).app M).symm ≪≫
      ((overEquiv U).unitIso.app (M.over U)).symm
  exact SheafOfModules.IsFiniteType.of_iso
    (C := Over U) (R := X.ringCatSheaf.over U)
    (M := (overEquiv U).inverse.obj (M.restrict U.ι)) (N := M.over U) e h

/-- Restriction along an actual open immersion preserves finite type. -/
theorem isFiniteType_restrictFunctor
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (hM : M.IsFiniteType) : (M.restrict f).IsFiniteType := by
  let α : X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf :=
    { app U := (f.appIso U.unop).inv }
  have hαapp : ∀ U, IsIso (α.app U) :=
    fun U => inferInstanceAs (IsIso (f.appIso U.unop).inv)
  have hα : IsIso α := NatIso.isIso_of_isIso_app α
  let S : Sheaf (_root_.Opens.grothendieckTopology X) RingCat.{u} := X.ringCatSheaf
  let R : Sheaf (_root_.Opens.grothendieckTopology Y) RingCat.{u} := Y.ringCatSheaf
  let ρ : S ⟶
      (f.opensFunctor.sheafPushforwardContinuous RingCat.{u}
        (_root_.Opens.grothendieckTopology X)
        (_root_.Opens.grothendieckTopology Y)).obj R :=
    ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩
  have hρ : IsIso ρ := by
    have hh : IsIso ρ.hom :=
      inferInstanceAs (IsIso (Functor.whiskerRight α (forget₂ CommRingCat RingCat)))
    exact (ObjectProperty.isIso_hom_iff ρ).mp hh
  exact SheafOfModules.isFiniteType_pushforward_of_isLeftAdjoint
    f.opensFunctor ρ (restrictUnitIso f) hM

end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.isIso_of_isIso_pullback_closedFibre_of_isFinite_of_etale_of_isProper
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Nyll.SchemeTheory.Morphisms.UnramifiedHomExt
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Faithful finite étale pullback to a proper closed fibre

Over any local ring, finite étale morphisms on a proper scheme are determined
by their restriction to the closed fibre. The proof uses the actual relative
equalizer, which is open and closed, and the existing proper closed-fibre
isomorphism detector. Neither Noetherianity nor henselianity is assumed.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Relative maps into a separated unramified scheme are determined by the
closed fibre when their source is proper over a local ring. -/
theorem Over.hom_ext_of_closedFiber_of_isProper
    {R : Type u} [CommRing R] [IsLocalRing R]
    {S : Scheme.{u}} {U V : Over S}
    (f : U.left ⟶ AlgebraicGeometry.Spec (CommRingCat.of R)) [IsProper f]
    [FormallyUnramified V.hom] [LocallyOfFiniteType V.hom] [IsSeparated V.hom]
    (a b : U ⟶ V)
    (h : pullback.fst f
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ≫ a.left =
      pullback.fst f
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ≫ b.left) :
    a = b := by
  let j := pullback.fst f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
  let T : Over S := Over.mk (j ≫ U.hom)
  let i : T ⟶ U := Over.homMk j rfl
  have hi : i ≫ a = i ≫ b := CategoryTheory.Over.OverMorphism.ext h
  let l : T ⟶ equalizer a b := equalizer.lift i hi
  let e : (equalizer a b).left ⟶ U.left := (equalizer.ι a b).left
  have hl : l.left ≫ e = j :=
    congrArg (fun q : T ⟶ U ↦ q.left) (equalizer.lift_ι i hi)
  have heFinite : IsFinite e := by
    dsimp only [e]
    infer_instance
  have heEtale : Etale e := by
    dsimp only [e]
    infer_instance
  have heMono : Mono e := by
    dsimp only [e]
    infer_instance
  have hcond : l.left ≫ e = 𝟙 T.left ≫ j := by
    rw [Category.id_comp]
    exact hl
  have hs : IsSplitEpi (pullback.snd e j) :=
    IsSplitEpi.mk' ⟨pullback.lift l.left (𝟙 T.left) hcond,
      pullback.lift_snd l.left (𝟙 T.left) hcond⟩
  have hk : IsIso (pullback.snd e j) := isIso_of_mono_of_isSplitEpi _
  have he : IsIso e :=
    isIso_of_isIso_pullback_closedFibre_of_isFinite_of_etale_of_isProper f e hk
  apply CategoryTheory.Over.OverMorphism.ext
  apply (cancel_epi e).mp
  exact congrArg (fun q : equalizer a b ⟶ V ↦ q.left) (equalizer.condition a b)

namespace FiniteEtale

/-- Pullback to the closed fibre of a proper scheme over any local ring is
faithful on finite étale schemes. No henselian or Noetherian hypothesis is needed. -/
theorem pullback_faithful_closedFiber_of_isProper
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] :
    (FiniteEtale.pullback
      (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))).Faithful where
  map_injective {A B} a b hab := by
    let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    let i := pullback.fst f r
    have hleft : ((FiniteEtale.pullback i).map a).left =
        ((FiniteEtale.pullback i).map b).left :=
      congrArg (fun q : (FiniteEtale.pullback i).obj A ⟶
        (FiniteEtale.pullback i).obj B ↦ q.left) hab
    have hcomp : pullback.fst A.hom i ≫ a.left =
        pullback.fst A.hom i ≫ b.left := by
      have ha : pullback.fst A.hom i ≫ a.left =
          ((FiniteEtale.pullback i).map a).left ≫ pullback.fst B.hom i :=
        (pullback.lift_fst _ _ _).symm
      have hb : ((FiniteEtale.pullback i).map b).left ≫ pullback.fst B.hom i =
          pullback.fst A.hom i ≫ b.left := pullback.lift_fst _ _ _
      exact ha.trans ((congrArg (fun k ↦ k ≫ pullback.fst B.hom i) hleft).trans hb)
    have hclosed : pullback.fst (A.hom ≫ f) r ≫ a.left =
        pullback.fst (A.hom ≫ f) r ≫ b.left := by
      rw [← pullbackRightPullbackFstIso_inv_fst f r A.hom]
      simp only [Category.assoc]
      exact congrArg ((pullbackRightPullbackFstIso f r A.hom).inv ≫ ·) hcomp
    have hOver : a.hom = b.hom :=
      AlgebraicGeometry.Over.hom_ext_of_closedFiber_of_isProper
        (A.hom ≫ f) a.hom b.hom hclosed
    apply MorphismProperty.Over.Hom.ext
    exact congrArg (fun q : A.toComma ⟶ B.toComma ↦ q.left) hOver

end FiniteEtale
end AlgebraicGeometry

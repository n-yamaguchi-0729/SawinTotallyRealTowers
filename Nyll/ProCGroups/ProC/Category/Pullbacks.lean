/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Nyll.ProCGroups.Categorical.ProfinitePullbacks
import Nyll.ProCGroups.ProC.Category.Basic

/-!
# Pro C Groups / pro-C / Category / Pullbacks

This module relates mathlib's `CategoryTheory.IsPullback` predicate in
`ProCGrp C` to the concrete universal property tested against profinite
source groups.
-/

open CategoryTheory
open CategoryTheory.Limits
open ProCGroups.Categorical

universe u

namespace ProCGrp

variable {ProC : ProCGroups.FiniteGroupClass.{u}}
variable {G H H1 H2 : ProCGrp ProC}

/-- A continuous profinite-test pullback square is a pullback in `ProCGrp`. -/
theorem isPullback_of_hasProfiniteTestPullbackProperty
    {alpha1 : G ⟶ H1} {alpha2 : G ⟶ H2}
    {beta1 : H1 ⟶ H} {beta2 : H2 ⟶ H}
    (hpb : HasProfiniteTestPullbackProperty
      (continuousHom alpha1) (continuousHom alpha2)
      (continuousHom beta1) (continuousHom beta2)) :
    CategoryTheory.IsPullback alpha1 alpha2 beta1 beta2 := by
  have hw : alpha1 ≫ beta1 = alpha2 ≫ beta2 := by
    apply hom_ext
    change (continuousHom beta1).comp (continuousHom alpha1) =
      (continuousHom beta2).comp (continuousHom alpha2)
    exact hpb.1
  let condition :
      ∀ s : PullbackCone beta1 beta2,
        (continuousHom beta1).comp (continuousHom s.fst) =
          (continuousHom beta2).comp (continuousHom s.snd) :=
    fun s => by
      have hs := congrArg (fun f : s.pt ⟶ H => continuousHom f) s.condition
      change (continuousHom beta1).comp (continuousHom s.fst) =
        (continuousHom beta2).comp (continuousHom s.snd) at hs
      exact hs
  let lift : ∀ s : PullbackCone beta1 beta2, s.pt ⟶ G :=
    fun s => ConcreteCategory.ofHom (C := ProCGrp ProC)
      (pullbackDescCont hpb (continuousHom s.fst) (continuousHom s.snd)
        (condition s))
  refine { w := hw, isLimit' := ⟨?_⟩ }
  refine PullbackCone.IsLimit.mk hw lift ?_ ?_ ?_
  · intro s
    apply hom_ext
    change (continuousHom alpha1).comp
        (pullbackDescCont hpb (continuousHom s.fst) (continuousHom s.snd)
          (condition s)) =
      continuousHom s.fst
    exact pullbackDescCont_left hpb (continuousHom s.fst) (continuousHom s.snd)
      (condition s)
  · intro s
    apply hom_ext
    change (continuousHom alpha2).comp
        (pullbackDescCont hpb (continuousHom s.fst) (continuousHom s.snd)
          (condition s)) =
      continuousHom s.snd
    exact pullbackDescCont_right hpb (continuousHom s.fst) (continuousHom s.snd)
      (condition s)
  · intro s m hm1 hm2
    apply hom_ext
    change continuousHom m =
      pullbackDescCont hpb (continuousHom s.fst) (continuousHom s.snd)
        (condition s)
    apply pullbackDescCont_uniq hpb (continuousHom s.fst) (continuousHom s.snd)
      (condition s)
    constructor
    · have h := congrArg (fun f : s.pt ⟶ H1 => continuousHom f) hm1
      change (continuousHom alpha1).comp (continuousHom m) =
        continuousHom s.fst at h
      exact h
    · have h := congrArg (fun f : s.pt ⟶ H2 => continuousHom f) hm2
      change (continuousHom alpha2).comp (continuousHom m) =
        continuousHom s.snd at h
      exact h

/-- In the all-finite category, a pullback has the profinite-test universal property. -/
theorem hasProfiniteTestPullbackProperty_of_isPullback_allFinite
    {G H H1 H2 : ProCGrp ProCGroups.FiniteGroupClass.allFinite}
    {alpha1 : G ⟶ H1} {alpha2 : G ⟶ H2}
    {beta1 : H1 ⟶ H} {beta2 : H2 ⟶ H}
    (hpb : CategoryTheory.IsPullback alpha1 alpha2 beta1 beta2) :
    HasProfiniteTestPullbackProperty
      (continuousHom alpha1) (continuousHom alpha2)
      (continuousHom beta1) (continuousHom beta2) := by
  refine ⟨?_, ?_⟩
  · change continuousHom (alpha1 ≫ beta1) = continuousHom (alpha2 ≫ beta2)
    exact congrArg (fun f : G ⟶ H => continuousHom f) hpb.w
  · intro K _ _ _ _ _ _ phi1 phi2 hphi
    let Kc : ProCGrp ProCGroups.FiniteGroupClass.allFinite :=
      ProCGrp.of ProCGroups.FiniteGroupClass.allFinite (ProfiniteGrp.of K)
        (ProCGrp.allFinite_property (ProfiniteGrp.of K))
    let phi1' : Kc ⟶ H1 :=
      ConcreteCategory.ofHom (C := ProCGrp ProCGroups.FiniteGroupClass.allFinite) phi1
    let phi2' : Kc ⟶ H2 :=
      ConcreteCategory.ofHom (C := ProCGrp ProCGroups.FiniteGroupClass.allFinite) phi2
    have hphi' : phi1' ≫ beta1 = phi2' ≫ beta2 := by
      apply hom_ext
      exact hphi
    let psi : Kc ⟶ G := hpb.lift phi1' phi2' hphi'
    refine ⟨continuousHom psi, ?_, ?_⟩
    · constructor
      · have h := hpb.lift_fst phi1' phi2' hphi'
        exact congrArg (fun f : Kc ⟶ H1 => continuousHom f) h
      · have h := hpb.lift_snd phi1' phi2' hphi'
        exact congrArg (fun f : Kc ⟶ H2 => continuousHom f) h
    · intro theta htheta
      let theta' : Kc ⟶ G :=
        ConcreteCategory.ofHom (C := ProCGrp ProCGroups.FiniteGroupClass.allFinite) theta
      have htheta1 : theta' ≫ alpha1 = phi1' := by
        apply hom_ext
        exact htheta.1
      have htheta2 : theta' ≫ alpha2 = phi2' := by
        apply hom_ext
        exact htheta.2
      have hthetaEq : theta' = psi := by
        apply hpb.hom_ext
        · exact htheta1.trans (hpb.lift_fst phi1' phi2' hphi').symm
        · exact htheta2.trans (hpb.lift_snd phi1' phi2' hphi').symm
      have h := congrArg (fun f : Kc ⟶ G => continuousHom f) hthetaEq
      change theta = continuousHom psi at h
      exact h

end ProCGrp

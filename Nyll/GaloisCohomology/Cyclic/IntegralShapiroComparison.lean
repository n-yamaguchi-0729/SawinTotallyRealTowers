/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Basic.FunLike.Basic
public import Nyll.GaloisCohomology.Cyclic.IntegralConnectingMapComparison
public import Nyll.GaloisCohomology.Cyclic.IntegralShapiro
public import Nyll.GaloisCohomology.Cyclic.IntegralUniverseShapiro
public import Nyll.GaloisCohomology.GroupTheory.CoefficientRingShapiroComparison
public import Nyll.GaloisCohomology.GroupTheory.GroupEquivComplexComparison
public import Nyll.GaloisCohomology.GroupTheory.ShapiroEvaluation

/-!
# The selected integral Shapiro maps recover the original map

The common-universe comparison removes only the actual group/carrier lifts in the cochains.
The coefficient comparison then removes the lifted integer ring. These squares compare the
existing selected Shapiro isomorphisms, including their maps in the literal Type-zero API.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace IntegralGroupCohomology

section Original

variable {G : Type} [Group G]

/-- The original integral cohomology comparison is natural on the actual representation maps. -/
theorem cohomologyIsoOriginal_naturality {A B : Rep.{0} ℤ G} (f : A ⟶ B) (n : ℕ) :
    (cohomologyFunctor G n).map f ≫ (cohomologyIsoOriginal B n).hom =
      (cohomologyIsoOriginal A n).hom ≫ (groupCohomology.functor ℤ G n).map f := by
  let e : ULift.{0} ℤ ≃+* ℤ := ULift.ringEquiv
  let Q : ModuleCat.{0} ℤ ≌ ModuleCat.{0} (ULift.{0} ℤ) :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
  let F : ModuleCat.{0} (ULift.{0} ℤ) ⥤ ModuleCat.{0} ℤ := integerScalars
  let A' : Rep.{0} (ULift.{0} ℤ) G := (coefficientFunctor G).obj A
  let B' : Rep.{0} (ULift.{0} ℤ) G := (coefficientFunctor G).obj B
  let cA : Q.functor.obj (groupCohomology A n) ≅ groupCohomology A' n :=
    groupCohomology.coefficientRingIso e A n
  let cB : Q.functor.obj (groupCohomology B n) ≅ groupCohomology B' n :=
    groupCohomology.coefficientRingIso e B n
  let d : groupCohomology A n ⟶ groupCohomology B n :=
    (groupCohomology.functor ℤ G n).map f
  let d' : groupCohomology A' n ⟶ groupCohomology B' n :=
    (groupCohomology.functor (ULift.{0} ℤ) G n).map ((coefficientFunctor G).map f)
  let aA : F.obj (Q.functor.obj (groupCohomology A n)) ⟶ groupCohomology A n :=
    (Q.unitIso.app (groupCohomology A n)).inv
  let aB : F.obj (Q.functor.obj (groupCohomology B n)) ⟶ groupCohomology B n :=
    (Q.unitIso.app (groupCohomology B n)).inv
  have hc : d' ≫ cB.inv = cA.inv ≫ Q.functor.map d :=
    groupCohomology.map_coefficientRingIso_inv e (MonoidHom.id G) f n
  have hm : F.map d' ≫ F.map cB.inv = F.map cA.inv ≫ F.map (Q.functor.map d) :=
    (F.map_comp d' cB.inv).symm.trans
      ((congrArg (fun q : groupCohomology A' n ⟶ Q.functor.obj (groupCohomology B n) =>
          F.map q) hc).trans (F.map_comp cA.inv (Q.functor.map d)))
  have hu : F.map (Q.functor.map d) ≫ aB = aA ≫ d := Q.unitIso.inv.naturality d
  change F.map d' ≫ (F.map cB.inv ≫ aB) = (F.map cA.inv ≫ aA) ≫ d
  exact (Category.assoc (F.map d') (F.map cB.inv) aB).symm.trans
    ((congrArg (fun q => q ≫ aB) hm).trans
      ((Category.assoc (F.map cA.inv) (F.map (Q.functor.map d)) aB).trans
        ((congrArg (fun q => F.map cA.inv ≫ q) hu).trans
          (Category.assoc (F.map cA.inv) aA d).symm)))

/-- The existing common-universe integral Shapiro map becomes the selected original map. -/
theorem coindIso_cohomologyIsoOriginal {S : Subgroup G} (A : Rep.{0} ℤ S) (n : ℕ) :
    (coindIso A n).hom ≫ (cohomologyIsoOriginal A n).hom =
      (cohomologyIsoOriginal (Rep.coind S.subtype A) n).hom ≫
        (groupCohomology.coindIso A n).hom := by
  let e : ULift.{0} ℤ ≃+* ℤ := ULift.ringEquiv
  let Q : ModuleCat.{0} ℤ ≌ ModuleCat.{0} (ULift.{0} ℤ) :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
  let F : ModuleCat.{0} (ULift.{0} ℤ) ⥤ ModuleCat.{0} ℤ := integerScalars
  let C : Rep.{0} ℤ G := Rep.coind S.subtype A
  let A' : Rep.{0} (ULift.{0} ℤ) S := (coefficientFunctor S).obj A
  let C' : Rep.{0} (ULift.{0} ℤ) G := (coefficientFunctor G).obj C
  let cA : Q.functor.obj (groupCohomology A n) ≅ groupCohomology A' n :=
    groupCohomology.coefficientRingIso e A n
  let cC : Q.functor.obj (groupCohomology C n) ≅ groupCohomology C' n :=
    groupCohomology.coefficientRingIso e C n
  let d : groupCohomology C n ⟶ groupCohomology A n :=
    (groupCohomology.coindIso A n).hom
  let d' : groupCohomology C' n ⟶ groupCohomology A' n :=
    (groupCohomology.functor (ULift.{0} ℤ) G n).map
        (Rep.coefficientRingCoindIso e S.subtype A).hom ≫
      (groupCohomology.coindIso A' n).hom
  let aA : F.obj (Q.functor.obj (groupCohomology A n)) ⟶ groupCohomology A n :=
    (Q.unitIso.app (groupCohomology A n)).inv
  let aC : F.obj (Q.functor.obj (groupCohomology C n)) ⟶ groupCohomology C n :=
    (Q.unitIso.app (groupCohomology C n)).inv
  have hc : d' ≫ cA.inv = cC.inv ≫ Q.functor.map d :=
    groupCohomology.coindIso_coefficientRingIso_inv e A n
  have hm : F.map d' ≫ F.map cA.inv = F.map cC.inv ≫ F.map (Q.functor.map d) :=
    (F.map_comp d' cA.inv).symm.trans
      ((congrArg (fun q : groupCohomology C' n ⟶ Q.functor.obj (groupCohomology A n) =>
          F.map q) hc).trans (F.map_comp cC.inv (Q.functor.map d)))
  have hu : F.map (Q.functor.map d) ≫ aA = aC ≫ d := Q.unitIso.inv.naturality d
  change F.map d' ≫ (F.map cA.inv ≫ aA) = (F.map cC.inv ≫ aC) ≫ d
  exact (Category.assoc (F.map d') (F.map cA.inv) aA).symm.trans
    ((congrArg (fun q => q ≫ aA) hm).trans
      ((Category.assoc (F.map cC.inv) (F.map (Q.functor.map d)) aA).trans
        ((congrArg (fun q => F.map cC.inv ≫ q) hu).trans
          (Category.assoc (F.map cC.inv) aC d).symm)))

end Original

namespace Universe

variable {G : Type u} [Group G]

/-- Removing the actual group/carrier lifts is natural on the original coefficient maps. -/
theorem cohomologyIsoCommon_naturality {A B : Rep.{u} ℤ G} (f : A ⟶ B) (n : ℕ) :
    (cohomologyFunctor G n).map f ≫ (cohomologyIsoCommon B n).hom =
      (cohomologyIsoCommon A n).hom ≫
        (IntegralGroupCohomology.cohomologyFunctor G n).map f := by
  let Hn := HomologicalComplex.homologyFunctor (ModuleCat (ULift.{u} ℤ)) (.up ℕ) n
  let E := nativeCochainsCommonNatIso G
  change integerScalars.map (Hn.map
      ((nativeFunctor G ⋙
        groupCohomology.cochainsFunctor (ULift.{u} ℤ) (ULift.{u} G)).map f)) ≫
      integerScalars.map (Hn.map (E.hom.app B)) =
    integerScalars.map (Hn.map (E.hom.app A)) ≫ integerScalars.map (Hn.map
      ((coefficientFunctor G ⋙ groupCohomology.cochainsFunctor (ULift.{u} ℤ) G).map f))
  simpa only [Functor.map_comp] using
    congrArg (fun c => integerScalars.map (Hn.map c)) (E.hom.naturality f)

/-- The independently lifted selected Shapiro map agrees with the existing common owner. -/
theorem coindIso_cohomologyIsoCommon {S : Subgroup G} (A : Rep.{u} ℤ S) (n : ℕ) :
    ((coindIso (G := G) (S := S) A n).hom :
        cohomology (Rep.coind S.subtype A) n ⟶ cohomology A n) ≫
      ((cohomologyIsoCommon (G := S) A n).hom :
        cohomology A n ⟶ IntegralGroupCohomology.cohomology A n) =
      ((cohomologyIsoCommon (G := G) (Rep.coind S.subtype A) n).hom :
        cohomology (Rep.coind S.subtype A) n ⟶
          IntegralGroupCohomology.cohomology (Rep.coind S.subtype A) n) ≫
        ((IntegralGroupCohomology.coindIso (G := G) (S := S) A n).hom :
          IntegralGroupCohomology.cohomology (Rep.coind S.subtype A) n ⟶
            IntegralGroupCohomology.cohomology A n) := by
  let Hn := HomologicalComplex.homologyFunctor (ModuleCat (ULift.{u} ℤ)) (.up ℕ) n
  let J : Subgroup (ULift.{u} G) := coindLiftSubgroup S
  let B := coindLiftRepresentation A
  let E := groupCohomology.groupEquivComplexIso
    (A := B) (B := (nativeFunctor S).obj A)
    (coindLiftSubgroupEquiv S)
    (LinearEquiv.refl (ULift.{u} ℤ) ((nativeFunctor S).obj A).V) (by
      intro g
      apply LinearMap.ext
      intro a
      rfl)
  let eC := groupCohomology.groupEquivComplexIso
    (A := (nativeFunctor G).obj (Rep.coind S.subtype A))
    (B := (coefficientFunctor G).obj (Rep.coind S.subtype A))
    (MulEquiv.ulift : ULift.{u} G ≃* G)
    (nativeCarrierEquiv (Rep.coind S.subtype A))
    (nativeCarrierEquiv_comm (Rep.coind S.subtype A))
  let eA := groupCohomology.groupEquivComplexIso
    (A := (nativeFunctor S).obj A) (B := (coefficientFunctor S).obj A)
    (MulEquiv.ulift : ULift.{u} S ≃* S) (nativeCarrierEquiv A) (nativeCarrierEquiv_comm A)
  let c₁ := groupCohomology.cochainsMap
    (A := (nativeFunctor G).obj (Rep.coind S.subtype A))
    (B := Rep.coind J.subtype B)
    (MonoidHom.id (ULift.{u} G)) (nativeCoindIso A).hom
  let c₂ := groupCohomology.cochainsMap J.subtype (Rep.coindEvaluation J.subtype B)
  let d₁ := groupCohomology.cochainsMap
    (A := (coefficientFunctor G).obj (Rep.coind S.subtype A))
    (B := Rep.coind S.subtype ((coefficientFunctor S).obj A))
    (MonoidHom.id G)
    (Rep.coefficientRingCoindIso (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ) S.subtype A).hom
  let d₂ := groupCohomology.cochainsMap S.subtype
    (Rep.coindEvaluation S.subtype ((coefficientFunctor S).obj A))
  have hc : (c₁ ≫ c₂ ≫ E.hom) ≫ eA.hom = eC.hom ≫ (d₁ ≫ d₂) := by
    apply HomologicalComplex.hom_ext
    intro i
    apply ModuleCat.hom_ext
    apply DFunLike.ext
    intro f
    rfl
  change integerScalars.map
      (Hn.map c₁ ≫ (groupCohomology.coindIso B n).hom ≫ Hn.map E.hom) ≫
      integerScalars.map (Hn.map eA.hom) =
    integerScalars.map (Hn.map eC.hom) ≫ integerScalars.map
      (Hn.map d₁ ≫ (groupCohomology.coindIso ((coefficientFunctor S).obj A) n).hom)
  rw [groupCohomology.coindIso_hom_eq_map, groupCohomology.coindIso_hom_eq_map]
  change integerScalars.map (Hn.map c₁ ≫ Hn.map c₂ ≫ Hn.map E.hom) ≫
      integerScalars.map (Hn.map eA.hom) =
    integerScalars.map (Hn.map eC.hom) ≫ integerScalars.map (Hn.map d₁ ≫ Hn.map d₂)
  simpa only [Functor.map_comp] using
    congrArg (fun c => integerScalars.map (Hn.map c)) hc

section Original

variable {H : Type} [Group H]

/-- The independently lifted original comparison is natural on the same coefficient maps. -/
theorem cohomologyIsoOriginal_naturality {A B : Rep.{0} ℤ H} (f : A ⟶ B) (n : ℕ) :
    (cohomologyFunctor H n).map f ≫ (cohomologyIsoOriginal B n).hom =
      (cohomologyIsoOriginal A n).hom ≫ (groupCohomology.functor ℤ H n).map f := by
  change (cohomologyFunctor H n).map f ≫
      ((cohomologyIsoCommon B n).hom ≫
        (IntegralGroupCohomology.cohomologyIsoOriginal B n).hom) =
    ((cohomologyIsoCommon A n).hom ≫
      (IntegralGroupCohomology.cohomologyIsoOriginal A n).hom) ≫
        (groupCohomology.functor ℤ H n).map f
  rw [← Category.assoc, cohomologyIsoCommon_naturality, Category.assoc,
    IntegralGroupCohomology.cohomologyIsoOriginal_naturality]
  exact (Category.assoc (cohomologyIsoCommon A n).hom
    (IntegralGroupCohomology.cohomologyIsoOriginal A n).hom
    (show groupCohomology A n ⟶ groupCohomology B n from
      (groupCohomology.functor ℤ H n).map f)).symm

/-- In Type zero the selected independently lifted Shapiro map is the selected original map. -/
theorem coindIso_cohomologyIsoOriginal {S : Subgroup H} (A : Rep.{0} ℤ S) (n : ℕ) :
    (coindIso A n).hom ≫ (cohomologyIsoOriginal A n).hom =
      (cohomologyIsoOriginal (Rep.coind S.subtype A) n).hom ≫
        (groupCohomology.coindIso A n).hom := by
  change (coindIso A n).hom ≫
      ((cohomologyIsoCommon A n).hom ≫
        (IntegralGroupCohomology.cohomologyIsoOriginal A n).hom) =
    ((cohomologyIsoCommon (Rep.coind S.subtype A) n).hom ≫
      (IntegralGroupCohomology.cohomologyIsoOriginal (Rep.coind S.subtype A) n).hom) ≫
        (groupCohomology.coindIso A n).hom
  rw [← Category.assoc, coindIso_cohomologyIsoCommon, Category.assoc,
    IntegralGroupCohomology.coindIso_cohomologyIsoOriginal]
  exact (Category.assoc (cohomologyIsoCommon (Rep.coind S.subtype A) n).hom
    (IntegralGroupCohomology.cohomologyIsoOriginal (Rep.coind S.subtype A) n).hom
    (groupCohomology.coindIso A n).hom).symm

end Original

end Universe

end IntegralGroupCohomology

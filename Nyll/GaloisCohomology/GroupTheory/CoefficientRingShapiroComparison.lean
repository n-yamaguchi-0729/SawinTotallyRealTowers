/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Iso
public import Nyll.GaloisCohomology.GroupTheory.CoefficientRingEquivalence
public import Nyll.GaloisCohomology.GroupTheory.CoefficientRingCoinduction
public import Nyll.GaloisCohomology.GroupTheory.ShapiroEvaluation

/-!
# Coefficient transport preserves the selected Shapiro map

The original cochain maps commute with coefficient restriction. Combining that concrete square
with the evaluation description of native Shapiro identifies the selected Shapiro maps on both
sides of the existing coefficient comparison.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Category

namespace groupCohomology

variable {R T G H : Type u} [CommRing R] [CommRing T] [Group G] [Group H]
  (e : R ≃+* T)

/-- Coefficient restriction preserves the actual cohomology map of any group/representation map. -/
theorem coefficientRingIso_map {A : Rep T H} {B : Rep T G}
    (φ : G →* H) (f : Rep.res φ A ⟶ B) (n : ℕ) :
    (ModuleCat.restrictScalars e.toRingHom).map (map φ f n) ≫
        (coefficientRingIso e B n).hom =
      (coefficientRingIso e A n).hom ≫
        map φ ((Rep.coefficientRingEquivalence e G).functor.map f) n := by
  let F := ModuleCat.restrictScalars e.toRingHom
  let c := cochainsMap φ f
  let c' := cochainsMap (A := (Rep.coefficientRingEquivalence e H).functor.obj A)
    (B := (Rep.coefficientRingEquivalence e G).functor.obj B) φ
    ((Rep.coefficientRingEquivalence e G).functor.map f)
  let eA := coefficientRingComplexIso e A
  let eB := coefficientRingComplexIso e B
  let MA := ((inhomogeneousCochains A).sc n).mapHomologyIso F
  let MB := ((inhomogeneousCochains B).sc n).mapHomologyIso F
  have hc : (F.mapHomologicalComplex (.up ℕ)).map c ≫ eB.hom = eA.hom ≫ c' := by
    apply HomologicalComplex.hom_ext
    intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  have hn : F.map (HomologicalComplex.homologyMap c n) ≫ MB.inv =
      MA.inv ≫ HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (.up ℕ)).map c) n :=
    ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor (ModuleCat T) (.up ℕ) n).map c) F
  change F.map (HomologicalComplex.homologyMap c n) ≫
      (MB.inv ≫ HomologicalComplex.homologyMap eB.hom n) =
    (MA.inv ≫ HomologicalComplex.homologyMap eA.hom n) ≫
      HomologicalComplex.homologyMap c' n
  have hcomp : HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (.up ℕ)).map c) n ≫
      HomologicalComplex.homologyMap eB.hom n =
      HomologicalComplex.homologyMap eA.hom n ≫ HomologicalComplex.homologyMap c' n :=
    (HomologicalComplex.homologyMap_comp
      ((F.mapHomologicalComplex (.up ℕ)).map c) eB.hom n).symm.trans
        ((congrArg (fun q => HomologicalComplex.homologyMap q n) hc).trans
          (HomologicalComplex.homologyMap_comp eA.hom c' n))
  exact (assoc (F.map (HomologicalComplex.homologyMap c n)) MB.inv
    (HomologicalComplex.homologyMap eB.hom n)).symm.trans
      ((congrArg (fun q => q ≫ HomologicalComplex.homologyMap eB.hom n) hn).trans
        ((assoc MA.inv
          (HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map c) n)
          (HomologicalComplex.homologyMap eB.hom n)).trans
            ((congrArg (fun q => MA.inv ≫ q) hcomp).trans
              (assoc MA.inv (HomologicalComplex.homologyMap eA.hom n)
                (HomologicalComplex.homologyMap c' n)).symm)))

/-- The inverse coefficient comparison preserves that same actual cohomology map. -/
theorem map_coefficientRingIso_inv {A : Rep T H} {B : Rep T G}
    (φ : G →* H) (f : Rep.res φ A ⟶ B) (n : ℕ) :
    map φ ((Rep.coefficientRingEquivalence e G).functor.map f) n ≫
        (coefficientRingIso e B n).inv =
      (coefficientRingIso e A n).inv ≫
        (ModuleCat.restrictScalars e.toRingHom).map (map φ f n) := by
  apply (cancel_epi (coefficientRingIso e A n).hom).1
  rw [← assoc, ← coefficientRingIso_map e φ f n, assoc,
    Iso.hom_inv_id, comp_id, Iso.hom_inv_id_assoc]

variable {S : Subgroup G} (A : Rep T S)

/-- The selected native Shapiro hom commutes with the existing coefficient/coinduction isos. -/
theorem coefficientRingIso_coindIso (n : ℕ) :
    (ModuleCat.restrictScalars e.toRingHom).map (coindIso A n).hom ≫
        (coefficientRingIso e A n).hom =
      (coefficientRingIso e (Rep.coind S.subtype A) n).hom ≫
        (functor R G n).map (Rep.coefficientRingCoindIso e S.subtype A).hom ≫
        (coindIso ((Rep.coefficientRingEquivalence e S).functor.obj A) n).hom := by
  have hm : map S.subtype
      ((Rep.coefficientRingEquivalence e S).functor.map (Rep.coindEvaluation S.subtype A)) n =
    (functor R G n).map (Rep.coefficientRingCoindIso e S.subtype A).hom ≫
      map S.subtype
        (Rep.coindEvaluation S.subtype ((Rep.coefficientRingEquivalence e S).functor.obj A))
        n := by
    change HomologicalComplex.homologyMap _ n =
      HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n
    rw [← HomologicalComplex.homologyMap_comp]
    apply congrArg (fun c => HomologicalComplex.homologyMap c n)
    apply HomologicalComplex.hom_ext
    intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  calc
    _ = (ModuleCat.restrictScalars e.toRingHom).map
          (map S.subtype (Rep.coindEvaluation S.subtype A) n) ≫
        (coefficientRingIso e A n).hom :=
      congrArg (fun f => (ModuleCat.restrictScalars e.toRingHom).map f ≫
        (coefficientRingIso e A n).hom) (coindIso_hom_eq_map A n)
    _ = (coefficientRingIso e (Rep.coind S.subtype A) n).hom ≫
        map S.subtype
          ((Rep.coefficientRingEquivalence e S).functor.map
            (Rep.coindEvaluation S.subtype A)) n :=
      coefficientRingIso_map e S.subtype (Rep.coindEvaluation S.subtype A) n
    _ = (coefficientRingIso e (Rep.coind S.subtype A) n).hom ≫
        (functor R G n).map (Rep.coefficientRingCoindIso e S.subtype A).hom ≫
          map S.subtype
            (Rep.coindEvaluation S.subtype ((Rep.coefficientRingEquivalence e S).functor.obj A))
            n :=
      congrArg (fun f => (coefficientRingIso e (Rep.coind S.subtype A) n).hom ≫ f) hm
    _ = _ :=
      congrArg (fun f => (coefficientRingIso e (Rep.coind S.subtype A) n).hom ≫
        (functor R G n).map (Rep.coefficientRingCoindIso e S.subtype A).hom ≫ f)
        (coindIso_hom_eq_map ((Rep.coefficientRingEquivalence e S).functor.obj A) n).symm

/-- The inverse coefficient comparison preserves the same selected native Shapiro hom. -/
theorem coindIso_coefficientRingIso_inv (n : ℕ) :
    ((functor R G n).map (Rep.coefficientRingCoindIso e S.subtype A).hom ≫
        (coindIso ((Rep.coefficientRingEquivalence e S).functor.obj A) n).hom) ≫
      (coefficientRingIso e A n).inv =
    (coefficientRingIso e (Rep.coind S.subtype A) n).inv ≫
      (ModuleCat.restrictScalars e.toRingHom).map (coindIso A n).hom := by
  apply (Iso.comp_inv_eq (coefficientRingIso e A n)).mpr
  exact
    ((Iso.eq_inv_comp (coefficientRingIso e (Rep.coind S.subtype A) n)).mpr
      (coefficientRingIso_coindIso e A n).symm).trans
      (assoc (coefficientRingIso e (Rep.coind S.subtype A) n).inv
        ((ModuleCat.restrictScalars e.toRingHom).map (coindIso A n).hom)
        (coefficientRingIso e A n).hom).symm

end groupCohomology

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
public import Nyll.GaloisCohomology.GroupTheory.CoefficientRingHomologyEquivalence
public import Nyll.SchemeTheory.HomologicalAlgebra.HomologySequenceExactFunctor

/-!
# The actual connecting maps under coefficient equivalence

The existing coefficient comparisons are identity maps on cochains and chains. Their naturality
therefore identifies the short exact sequences of actual complexes. The canonical exact-functor
homology comparison then proves compatibility with the original connecting map, including the
norm boundary in the Tate complex.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Category

namespace groupCohomology

variable {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
  (G : Type u) [Group G]

/-- The identity on actual cochains is natural in every equivariant coefficient map. -/
def coefficientRingComplexNatIso :
    cochainsFunctor S G ⋙
        (ModuleCat.restrictScalars e.toRingHom).mapHomologicalComplex (.up ℕ) ≅
      (Rep.coefficientRingEquivalence e G).functor ⋙ cochainsFunctor R G :=
  NatIso.ofComponents (fun A => coefficientRingComplexIso e A) (by
    intro A B f
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl)

variable {G}

/-- The existing coefficient cohomology comparison commutes with the actual connecting map. -/
theorem coefficientRingIso_δ {X : ShortComplex (Rep.{u} S G)} (hX : X.ShortExact)
    (i j : ℕ) (hij : i + 1 = j) :
    (ModuleCat.restrictScalars e.toRingHom).map (δ hX i j hij) ≫
        (coefficientRingIso e X.X₁ j).hom =
      (coefficientRingIso e X.X₃ i).hom ≫
        δ (hX.map_of_exact (Rep.coefficientRingEquivalence e G).functor) i j hij := by
  let F := ModuleCat.restrictScalars e.toRingHom
  let C := X.map (cochainsFunctor S G)
  let D := (X.map (Rep.coefficientRingEquivalence e G).functor).map (cochainsFunctor R G)
  have hC : C.ShortExact := map_cochainsFunctor_shortExact hX
  have hD : D.ShortExact := map_cochainsFunctor_shortExact
    (hX.map_of_exact (Rep.coefficientRingEquivalence e G).functor)
  let E : C.map (F.mapHomologicalComplex (.up ℕ)) ≅ D :=
    X.mapNatIso (coefficientRingComplexNatIso e G)
  let T := C.map (F.mapHomologicalComplex (.up ℕ))
  let M₁ : T.X₁.homology j ≅ F.obj (C.X₁.homology j) :=
    (C.X₁.sc j).mapHomologyIso F
  let M₃ : T.X₃.homology i ≅ F.obj (C.X₃.homology i) :=
    (C.X₃.sc i).mapHomologyIso F
  let dC : F.obj (C.X₃.homology i) ⟶ F.obj (C.X₁.homology j) :=
    F.map (hC.δ i j hij)
  let dT : T.X₃.homology i ⟶ T.X₁.homology j :=
    (hC.map_of_exact (F.mapHomologicalComplex (.up ℕ))).δ i j hij
  let dD : D.X₃.homology i ⟶ D.X₁.homology j := hD.δ i j hij
  let a₁ : T.X₁.homology j ⟶ D.X₁.homology j :=
    HomologicalComplex.homologyMap E.hom.τ₁ j
  let a₃ : T.X₃.homology i ⟶ D.X₃.homology i :=
    HomologicalComplex.homologyMap E.hom.τ₃ i
  have hm : dT ≫ M₁.hom = M₃.hom ≫ dC := hC.map_δ_eq F i j hij
  have he : dT ≫ a₁ = a₃ ≫ dD :=
    HomologicalComplex.HomologySequence.δ_naturality E.hom
      (hC.map_of_exact (F.mapHomologicalComplex (.up ℕ))) hD i j hij
  change dC ≫ (M₁.inv ≫ a₁) = (M₃.inv ≫ a₃) ≫ dD
  apply (cancel_epi M₃.hom).1
  refine Eq.trans ?_ (Eq.trans he ?_)
  · exact (Category.assoc M₃.hom dC (M₁.inv ≫ a₁)).symm.trans
      ((congrArg (fun f => f ≫ (M₁.inv ≫ a₁)) hm.symm).trans
        ((Category.assoc dT M₁.hom (M₁.inv ≫ a₁)).trans
          (congrArg (fun f => dT ≫ f) (Iso.hom_inv_id_assoc M₁ a₁))))
  · exact ((Category.assoc M₃.hom (M₃.inv ≫ a₃) dD).symm.trans
      (congrArg (fun f => f ≫ dD) (Iso.hom_inv_id_assoc M₃ a₃))).symm

/-- The inverse coefficient comparison retains the same connecting map. -/
theorem δ_coefficientRingIso_inv {X : ShortComplex (Rep.{u} S G)} (hX : X.ShortExact)
    (i j : ℕ) (hij : i + 1 = j) :
    δ (hX.map_of_exact (Rep.coefficientRingEquivalence e G).functor) i j hij ≫
        (coefficientRingIso e X.X₁ j).inv =
      (coefficientRingIso e X.X₃ i).inv ≫
        (ModuleCat.restrictScalars e.toRingHom).map (δ hX i j hij) := by
  apply (cancel_epi (coefficientRingIso e X.X₃ i).hom).1
  rw [← assoc, ← coefficientRingIso_δ e hX i j hij, assoc,
    Iso.hom_inv_id, comp_id, Iso.hom_inv_id_assoc]

end groupCohomology

namespace TateCohomology

variable {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
  (G : Type u) [Group G] [Fintype G]

/-- The same identity on chains and cochains is natural through the actual Tate norm. -/
def coefficientRingComplexNatIso :
    tateComplexFunctor S G ⋙
        (ModuleCat.restrictScalars e.toRingHom).mapHomologicalComplex (.up ℤ) ≅
      (Rep.coefficientRingEquivalence e G).functor ⋙ tateComplexFunctor R G :=
  NatIso.ofComponents (fun A => coefficientRingComplexIso e A) (by
    intro A B f
    apply HomologicalComplex.hom_ext
    intro i
    cases i with
    | ofNat n =>
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        rfl
    | negSucc n =>
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        rfl)

variable {G}

/-- Coefficient comparison preserves the actual Tate connecting map in every degree. -/
theorem coefficientRingIso_δ {X : ShortComplex (Rep.{u} S G)} (hX : X.ShortExact)
    (i : ℤ) :
    (ModuleCat.restrictScalars e.toRingHom).map (δ hX i) ≫
        (coefficientRingIso e X.X₁ (i + 1)).hom =
      (coefficientRingIso e X.X₃ i).hom ≫
        δ (hX.map_of_exact (Rep.coefficientRingEquivalence e G).functor) i := by
  let F := ModuleCat.restrictScalars e.toRingHom
  let C := X.map (tateComplexFunctor S G)
  let D := (X.map (Rep.coefficientRingEquivalence e G).functor).map (tateComplexFunctor R G)
  have hC : C.ShortExact := map_tateComplexFunctor_shortExact hX
  have hD : D.ShortExact := map_tateComplexFunctor_shortExact
    (hX.map_of_exact (Rep.coefficientRingEquivalence e G).functor)
  let E : C.map (F.mapHomologicalComplex (.up ℤ)) ≅ D :=
    X.mapNatIso (coefficientRingComplexNatIso e G)
  let T := C.map (F.mapHomologicalComplex (.up ℤ))
  let M₁ : T.X₁.homology (i + 1) ≅ F.obj (C.X₁.homology (i + 1)) :=
    (C.X₁.sc (i + 1)).mapHomologyIso F
  let M₃ : T.X₃.homology i ≅ F.obj (C.X₃.homology i) :=
    (C.X₃.sc i).mapHomologyIso F
  let dC : F.obj (C.X₃.homology i) ⟶ F.obj (C.X₁.homology (i + 1)) :=
    F.map (hC.δ i (i + 1) rfl)
  let dT : T.X₃.homology i ⟶ T.X₁.homology (i + 1) :=
    (hC.map_of_exact (F.mapHomologicalComplex (.up ℤ))).δ i (i + 1) rfl
  let dD : D.X₃.homology i ⟶ D.X₁.homology (i + 1) := hD.δ i (i + 1) rfl
  let a₁ : T.X₁.homology (i + 1) ⟶ D.X₁.homology (i + 1) :=
    HomologicalComplex.homologyMap E.hom.τ₁ (i + 1)
  let a₃ : T.X₃.homology i ⟶ D.X₃.homology i :=
    HomologicalComplex.homologyMap E.hom.τ₃ i
  have hm : dT ≫ M₁.hom = M₃.hom ≫ dC := hC.map_δ_eq F i (i + 1) rfl
  have he : dT ≫ a₁ = a₃ ≫ dD :=
    HomologicalComplex.HomologySequence.δ_naturality E.hom
      (hC.map_of_exact (F.mapHomologicalComplex (.up ℤ))) hD i (i + 1) rfl
  change dC ≫ (M₁.inv ≫ a₁) = (M₃.inv ≫ a₃) ≫ dD
  apply (cancel_epi M₃.hom).1
  refine Eq.trans ?_ (Eq.trans he ?_)
  · exact (Category.assoc M₃.hom dC (M₁.inv ≫ a₁)).symm.trans
      ((congrArg (fun f => f ≫ (M₁.inv ≫ a₁)) hm.symm).trans
        ((Category.assoc dT M₁.hom (M₁.inv ≫ a₁)).trans
          (congrArg (fun f => dT ≫ f) (Iso.hom_inv_id_assoc M₁ a₁))))
  · exact ((Category.assoc M₃.hom (M₃.inv ≫ a₃) dD).symm.trans
      (congrArg (fun f => f ≫ dD) (Iso.hom_inv_id_assoc M₃ a₃))).symm

/-- The inverse Tate comparison retains the original connecting map in every degree. -/
theorem δ_coefficientRingIso_inv {X : ShortComplex (Rep.{u} S G)} (hX : X.ShortExact)
    (i : ℤ) :
    δ (hX.map_of_exact (Rep.coefficientRingEquivalence e G).functor) i ≫
        (coefficientRingIso e X.X₁ (i + 1)).inv =
      (coefficientRingIso e X.X₃ i).inv ≫
        (ModuleCat.restrictScalars e.toRingHom).map (δ hX i) := by
  apply (cancel_epi (coefficientRingIso e X.X₃ i).hom).1
  rw [← assoc, ← coefficientRingIso_δ e hX i, assoc,
    Iso.hom_inv_id, comp_id, Iso.hom_inv_id_assoc]

end TateCohomology

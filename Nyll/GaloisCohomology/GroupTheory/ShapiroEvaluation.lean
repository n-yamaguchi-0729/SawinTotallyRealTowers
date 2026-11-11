/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.RepresentationTheory.Equiv
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
public import Nyll.GaloisCohomology.GroupTheory.BarResolutionNaturality
public import Nyll.GaloisCohomology.GroupTheory.ProjectiveResolutionComparison

/-!
# The selected native Shapiro map is cochain evaluation

The native Shapiro isomorphism uses the restricted ambient bar resolution. The concrete tuple
map from the subgroup bar resolution is a lift of the identity. Resolution naturality therefore
identifies that selected isomorphism with restriction of cochains followed by evaluation at one.
No equality between separately selected resolutions is assumed.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace Rep

variable {R G H : Type u} [CommRing R] [Group G] [Group H]

/-- The existing restriction/coinduction counit, presented by its actual adjunction map. -/
def coindEvaluation (φ : G →* H) (A : Rep R G) : res φ (coind φ A) ⟶ A :=
  (resCoindHomEquiv.{u} φ (coind φ A) A).symm (𝟙 _)

/-- The actual counit evaluates the same equivariant function at the group identity. -/
theorem coindEvaluation_apply (φ : G →* H) (A : Rep R G) (f : coind φ A) :
    (coindEvaluation φ A).hom f = f.1 1 := rfl

end Rep

namespace groupCohomology

open Rep ClassFieldTower.Cohomology

variable {R G : Type u} [CommRing R] [Group G] {S : Subgroup G} (A : Rep R S)

/-- The native adjunction and the actual subgroup bar map evaluate each original cochain. -/
theorem shapiro_bar_cochains_square :
    ((inhomogeneousCochainsIso (coind S.subtype A)).hom ≫
        (linearYonedaObjResProjectiveResolutionIso (barResolution R G) A).inv) ≫
      resolutionLinearYonedaMap (barResolution R S)
        ((resFunctor S.subtype).mapProjectiveResolution (barResolution R G))
        (barRestrictionResolutionHom R G S) A =
      cochainsMap S.subtype (coindEvaluation S.subtype A) ≫
        (inhomogeneousCochainsIso A).hom := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply free_ext R S A
  intro x
  change ((freeLift R G (coind S.subtype A) f).hom
      ((barMapComponent R S.subtype n).hom
        (Finsupp.single x (MonoidAlgebra.single (1 : S) (1 : R))))).1 1 =
    (freeLift R S A (fun y => (f (S.subtype ∘ y)).1 1)).hom
      (Finsupp.single x (MonoidAlgebra.single (1 : S) (1 : R)))
  rw [barMapComponent_generator]
  change (Representation.freeLift (coind S.subtype A).ρ f
      (Finsupp.single (S.subtype ∘ x) (MonoidAlgebra.single (1 : G) (1 : R)))).1 1 =
    Representation.freeLift A.ρ (fun y => (f (S.subtype ∘ y)).1 1)
      (Finsupp.single x (MonoidAlgebra.single (1 : S) (1 : R)))
  rw [Representation.freeLift_single_single, Representation.freeLift_single_single]
  simp only [map_one, Module.End.one_apply, one_smul]

/-- The existing selected native Shapiro map is restriction followed by evaluation at one. -/
theorem coindIso_hom_eq_map (n : ℕ) :
    (coindIso A n).hom = map S.subtype (coindEvaluation S.subtype A) n := by
  let P : ProjectiveResolution (Rep.trivial R S R) := barResolution R S
  let Q : ProjectiveResolution (Rep.trivial R S R) :=
    (resFunctor S.subtype).mapProjectiveResolution (barResolution R G)
  let c : ProjectiveResolution.Hom P Q (𝟙 _) := barRestrictionResolutionHom R G S
  let e : inhomogeneousCochains A ≅ P.complex.linearYonedaObj R A :=
    inhomogeneousCochainsIso A
  let b : inhomogeneousCochains (coind S.subtype A) ⟶ Q.complex.linearYonedaObj R A :=
    (inhomogeneousCochainsIso (coind S.subtype A)).hom ≫
      (linearYonedaObjResProjectiveResolutionIso (barResolution R G) A).inv
  let d : Q.complex.linearYonedaObj R A ⟶ P.complex.linearYonedaObj R A :=
    resolutionLinearYonedaMap P Q c A
  let F := HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℕ) n
  let qIso : groupCohomology A n ≅ F.obj (Q.complex.linearYonedaObj R A) :=
    groupCohomologyIso A n Q
  have hn : F.map e.hom = qIso.hom ≫ F.map d :=
    (groupCohomologyIso_bar_hom_eq_homologyMap A n).symm.trans
      (groupCohomologyIso_hom_naturality P Q c A n)
  have hq : qIso.inv ≫ F.map e.hom = F.map d :=
    (congrArg (fun f => qIso.inv ≫ f) hn).trans
      (Iso.inv_hom_id_assoc qIso (F.map d))
  have hb : b ≫ d = cochainsMap S.subtype (coindEvaluation S.subtype A) ≫ e.hom :=
    shapiro_bar_cochains_square A
  apply (cancel_mono (F.map e.hom)).mp
  change (F.map b ≫ qIso.inv) ≫ F.map e.hom =
    F.map (cochainsMap S.subtype (coindEvaluation S.subtype A)) ≫ F.map e.hom
  calc
    (F.map b ≫ qIso.inv) ≫ F.map e.hom =
        F.map b ≫ (qIso.inv ≫ F.map e.hom) :=
      Category.assoc (F.map b) qIso.inv (F.map e.hom)
    _ = F.map b ≫ F.map d := congrArg (fun f => F.map b ≫ f) hq
    _ = F.map (b ≫ d) := (F.map_comp b d).symm
    _ = F.map (cochainsMap S.subtype (coindEvaluation S.subtype A) ≫ e.hom) :=
      congrArg (fun f => F.map f) hb
    _ = F.map (cochainsMap S.subtype (coindEvaluation S.subtype A)) ≫ F.map e.hom :=
      F.map_comp (cochainsMap S.subtype (coindEvaluation S.subtype A)) e.hom

end groupCohomology

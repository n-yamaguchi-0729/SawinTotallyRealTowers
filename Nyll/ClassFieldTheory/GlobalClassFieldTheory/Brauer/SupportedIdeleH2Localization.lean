/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.RestrictedAction
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.SPlaces
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.UnramifiedFinitePlaceIntegralBlockH2
public import Nyll.GaloisCohomology.ProP.MultiplicativeBinaryProductH2Evaluation
public import Nyll.GaloisCohomology.ProP.MultiplicativeProductH2
public import Nyll.GaloisCohomology.ProP.MultiplicativeProductH2Evaluation

/-!
# Degree-two localization for supported relative ideles

All archimedean tensor coordinates and the finite tensor coordinates in `S`
detect classes of the actual relative ideles supported in `S` when the finite
places outside `S` are unramified.
-/

@[expose] public section

open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField TensorProduct

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology CyclicCohomology
open AlgebraicNumberTheory.Valuations HilbertRamification LocalClassFieldTheory

variable (K L : Type) [Field K] [NumberField K]
variable [Field L] [NumberField L] [Algebra K L]
variable [FiniteDimensional K L] [IsGalois K L]

local notation "V" => HeightOneSpectrum (𝓞 K)
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "A∞" => (fun v : InfinitePlace K ↦ (InfinitePlace.Completion v ⊗[K] L)ˣ)
local notation "Ain" => (fun v : {v : V // v ∈ S} ↦
  (HeightOneSpectrum.adicCompletion K (Subtype.val v) ⊗[K] L)ˣ)
local notation "Aout" => (fun v : {v : V // v ∉ S} ↦
  relativeLocalTensorDecompositionIntegralUnitSubgroup (K := K) (L := L) (Subtype.val v))

attribute [local instance] scalarTensorUnitsAction finitePlaceScalarTensorUnitsAction
  relativeLocalTensorDecompositionIntegralUnitSubgroupAction piMulDistribMulAction

/-- Evaluate the actual S-place cohomology class in each unrestricted
finite tensor block belonging to S. -/
noncomputable def sPlaceFactorsH2Localization :
    groupCohomology (Rep.ofMulDistribMulAction Gal(L / K)
      (RelativeIdeleSPlaceFactors (K := K) (L := L) S)) 2 →+
      ∀ v : {v : V // v ∈ S},
        groupCohomology (Rep.ofMulDistribMulAction Gal(L / K) (Ain v)) 2 where
  toFun x := piMultiplicativeH2Evaluation Ain
    (prodMultiplicativeH2Evaluation (∀ v, Ain v) (∀ v, Aout v)
      (prodMultiplicativeH2Evaluation (∀ v, A∞ v)
        ((∀ v, Ain v) × (∀ v, Aout v)) x).2).1
  map_zero' := by
    simp only [map_zero, Prod.fst_zero, Prod.snd_zero]
  map_add' x y := by
    simp only [map_add, Prod.fst_add, Prod.snd_add]

/-- Evaluate an S-place factor class in each archimedean tensor block. -/
noncomputable def sPlaceFactorsInfiniteH2Localization :
    groupCohomology (Rep.ofMulDistribMulAction Gal(L / K)
      (RelativeIdeleSPlaceFactors (K := K) (L := L) S)) 2 →+
      ∀ v : InfinitePlace K,
        groupCohomology (Rep.ofMulDistribMulAction Gal(L / K) (A∞ v)) 2 where
  toFun x := piMultiplicativeH2Evaluation A∞
    (prodMultiplicativeH2Evaluation (∀ v, A∞ v)
      ((∀ v, Ain v) × (∀ v, Aout v)) x).1
  map_zero' := by simp only [map_zero, Prod.fst_zero]
  map_add' x y := by simp only [map_add, Prod.fst_add]

omit [NumberField L] in
/-- Outside unramified integral blocks leave the finite coordinates in `S`
and every archimedean coordinate as detectors in degree two. -/
theorem sPlaceFactorsH2_eq_of_localizations
    (hfin : ∀ v : V, v ∉ S → ChosenFinitePlaceIsUnramified (K := K) (L := L) v)
    {x y : groupCohomology (Rep.ofMulDistribMulAction Gal(L / K)
      (RelativeIdeleSPlaceFactors (K := K) (L := L) S)) 2}
    (hfinite : sPlaceFactorsH2Localization K L S x = sPlaceFactorsH2Localization K L S y)
    (hinfinite : sPlaceFactorsInfiniteH2Localization K L S x =
      sPlaceFactorsInfiniteH2Localization K L S y) : x = y := by
  let _ (v : {v : V // v ∉ S}) :
      Subsingleton (groupCohomology (Rep.ofMulDistribMulAction Gal(L / K) (Aout v)) 2) :=
    unramifiedFinitePlaceIntegralBlockH2_subsingleton K L v.1 (hfin v.1 v.2)
  let _ := piMultiplicativeH2_subsingleton (G := Gal(L / K)) Aout
  apply prodMultiplicativeH2Evaluation_injective (G := Gal(L / K))
    (∀ v, A∞ v) ((∀ v, Ain v) × (∀ v, Aout v))
  apply Prod.ext
  · exact piMultiplicativeH2Evaluation_injective (G := Gal(L / K)) A∞ hinfinite
  · apply prodMultiplicativeH2Evaluation_injective (G := Gal(L / K))
      (∀ v, Ain v) (∀ v, Aout v)
    apply Prod.ext
    · exact piMultiplicativeH2Evaluation_injective (G := Gal(L / K)) Ain hfinite
    · exact Subsingleton.elim _ _

attribute [local instance] relativeIdeleLocalTensorDecompositionSupportedSubgroupAction

/-- Supported relative ideles and their S-place factors have equivariantly isomorphic
coefficient representations. -/
def supportedSPlaceFactorsRepIso :
    Rep.ofMulDistribMulAction Gal(L / K)
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S) ≅
    Rep.ofMulDistribMulAction Gal(L / K)
      (RelativeIdeleSPlaceFactors (K := K) (L := L) S) := by
  let e := relativeIdeleSupportedEquivSPlaceFactors (K := K) (L := L) S
  exact Rep.mkIso (Representation.Equiv.mk e.toAdditive.toIntLinearEquiv (by
    intro g
    apply LinearMap.ext
    intro x
    exact congrArg Additive.ofMul
      (relativeIdeleSupportedComponents_smul (K := K) (L := L) S g x.toMul)))

/-- The supported idele decomposition induces the original degree-two cohomology isomorphism. -/
def supportedSPlaceCohomologyIso :
    groupCohomology (Rep.ofMulDistribMulAction Gal(L / K)
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S)) 2 ≅
    groupCohomology (Rep.ofMulDistribMulAction Gal(L / K)
      (RelativeIdeleSPlaceFactors (K := K) (L := L) S)) 2 :=
  (groupCohomology.functor ℤ Gal(L / K) 2).mapIso (supportedSPlaceFactorsRepIso K L S)

/-- The finite tensor-unit projection of a supported relative idele. -/
def supportedSPlaceFiniteRepHom (v : {v : V // v ∈ S}) :
    Rep.ofMulDistribMulAction Gal(L / K)
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S) ⟶
    Rep.ofMulDistribMulAction Gal(L / K) (Ain v) :=
  (supportedSPlaceFactorsRepIso K L S).hom ≫
    secondRepHom (∀ v, A∞ v) ((∀ v, Ain v) × (∀ v, Aout v)) ≫
    firstRepHom (∀ v, Ain v) (∀ v, Aout v) ≫ piMultiplicativeEvaluationRepHom Ain v

/-- The archimedean tensor-unit projection of a supported relative idele. -/
def supportedSPlaceInfiniteRepHom (v : InfinitePlace K) :
    Rep.ofMulDistribMulAction Gal(L / K)
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S) ⟶
    Rep.ofMulDistribMulAction Gal(L / K) (A∞ v) :=
  (supportedSPlaceFactorsRepIso K L S).hom ≫
    firstRepHom (∀ v, A∞ v) ((∀ v, Ain v) × (∀ v, Aout v)) ≫
    piMultiplicativeEvaluationRepHom A∞ v

/-- The integral tensor coordinate representation of an outside supported idèle. -/
def supportedSPlaceOutsideIntegralRepHom (v : {v : V // v ∉ S}) :
    Rep.ofMulDistribMulAction Gal(L / K)
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S) ⟶
    Rep.ofMulDistribMulAction Gal(L / K) (Aout v) :=
  (supportedSPlaceFactorsRepIso K L S).hom ≫
    secondRepHom (∀ v, A∞ v) ((∀ v, Ain v) × (∀ v, Aout v)) ≫
    secondRepHom (∀ v, Ain v) (∀ v, Aout v) ≫ piMultiplicativeEvaluationRepHom Aout v

/-- Outside `S`, the actual finite tensor projection factors through its
integral tensor subgroup. -/
def supportedSPlaceOutsideTensorRepHom (v : {v : V // v ∉ S}) :
    Rep.ofMulDistribMulAction Gal(L / K)
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S) ⟶
    Rep.ofMulDistribMulAction Gal(L / K) (v.1.adicCompletion K ⊗[K] L)ˣ :=
  supportedSPlaceOutsideIntegralRepHom K L S v ≫
    CyclicCohomology.ProfiniteCohomology.Herbrand.equivariantRepHom
      (Aout v).subtype (fun _ _ => rfl)

omit [IsGalois K L] [NumberField L] in
/-- The outside integral factor realizes the original finite coordinate. -/
theorem supportedSPlaceOutsideTensorRepHom_apply (v : {v : V // v ∉ S})
    (x : relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S) :
    supportedSPlaceOutsideTensorRepHom K L S v (Additive.ofMul x) =
      Additive.ofMul (RelativeIdeleGroup.finiteComponent (K := K) (L := L) v.1 x) :=
  rfl

omit [NumberField L] in
/-- At an unramified outside place, every supported idèle `H²` class has
zero image in the actual finite tensor block. -/
theorem supportedSPlaceOutsideTensorH2_eq_zero (v : {v : V // v ∉ S})
    (hv : ChosenFinitePlaceIsUnramified (K := K) (L := L) v.1)
    (x : groupCohomology (Rep.ofMulDistribMulAction Gal(L/K)
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S)) 2) :
    groupCohomology.map (MonoidHom.id (Gal(L / K)))
      (supportedSPlaceOutsideTensorRepHom K L S v) 2 x = 0 := by
  let : Subsingleton (groupCohomology (Rep.ofMulDistribMulAction Gal(L / K) (Aout v)) 2) :=
    unramifiedFinitePlaceIntegralBlockH2_subsingleton K L v.1 hv
  rw [supportedSPlaceOutsideTensorRepHom, groupCohomology.map_id_comp]
  have hz : groupCohomology.map (MonoidHom.id (Gal(L / K)))
      (supportedSPlaceOutsideIntegralRepHom K L S v) 2 x = 0 :=
    Subsingleton.elim _ _
  let j : Rep.ofMulDistribMulAction Gal(L/K) (Aout v) ⟶
      Rep.ofMulDistribMulAction Gal(L/K) (v.1.adicCompletion K ⊗[K] L)ˣ :=
    CyclicCohomology.ProfiniteCohomology.Herbrand.equivariantRepHom
      (Aout v).subtype (fun _ _ => rfl)
  change groupCohomology.map (MonoidHom.id (Gal(L/K))) j 2
    (groupCohomology.map (MonoidHom.id (Gal(L/K)))
    (supportedSPlaceOutsideIntegralRepHom K L S v) 2 x) = 0
  rw [hz, map_zero]

omit [IsGalois K L] [NumberField L] in
/-- Finite projection recovers the original relative idele component. -/
theorem supportedSPlaceFiniteRepHom_apply (v : {v : V // v ∈ S})
    (x : relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S) :
    supportedSPlaceFiniteRepHom K L S v (Additive.ofMul x) =
      Additive.ofMul (RelativeIdeleGroup.finiteComponent (K := K) (L := L) v.1 x) :=
  rfl

omit [IsGalois K L] [NumberField L] in
/-- Archimedean projection recovers the original relative idele component. -/
theorem supportedSPlaceInfiniteRepHom_apply (v : InfinitePlace K)
    (x : relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S) :
    supportedSPlaceInfiniteRepHom K L S v (Additive.ofMul x) =
      Additive.ofMul (RelativeIdeleGroup.infiniteComponent (K := K) (L := L) v x) :=
  rfl

/-- Localize a supported idele degree-two class at all finite places in S. -/
noncomputable def supportedSPlaceH2Localization :
    groupCohomology (Rep.ofMulDistribMulAction Gal(L / K)
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S)) 2 →+
      ∀ v : {v : V // v ∈ S},
        groupCohomology (Rep.ofMulDistribMulAction Gal(L / K) (Ain v)) 2 :=
  (sPlaceFactorsH2Localization K L S).comp
    (supportedSPlaceCohomologyIso K L S).toLinearEquiv.toAddEquiv.toAddMonoidHom

/-- Localize a supported idele degree-two class at every archimedean place. -/
noncomputable def supportedSPlaceInfiniteH2Localization :
    groupCohomology (Rep.ofMulDistribMulAction Gal(L / K)
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S)) 2 →+
      ∀ v : InfinitePlace K,
        groupCohomology (Rep.ofMulDistribMulAction Gal(L / K) (A∞ v)) 2 :=
  (sPlaceFactorsInfiniteH2Localization K L S).comp
    (supportedSPlaceCohomologyIso K L S).toLinearEquiv.toAddEquiv.toAddMonoidHom

omit [IsGalois K L] [NumberField L] in
private theorem sPlaceFactorsH2Localizations_surjective :
    Function.Surjective ((sPlaceFactorsH2Localization K L S).prod
      (sPlaceFactorsInfiniteH2Localization K L S)) := by
  have hFinite := piMultiplicativeH2Evaluation_surjective (G := Gal(L/K)) Ain
  have hInfinite := piMultiplicativeH2Evaluation_surjective (G := Gal(L/K)) A∞
  have hFiniteProduct := prodMultiplicativeH2Evaluation_surjective (G := Gal(L/K))
    (∀ v, Ain v) (∀ v, Aout v)
  have hProduct := prodMultiplicativeH2Evaluation_surjective (G := Gal(L/K))
    (∀ v, A∞ v) ((∀ v, Ain v) × (∀ v, Aout v))
  have hProjection := Function.Surjective.comp (g := Prod.fst)
    (fun x => ⟨(x, 0), rfl⟩) hFiniteProduct
  exact Prod.swap_surjective.comp ((hInfinite.prodMap (hFinite.comp hProjection)).comp hProduct)

omit [IsGalois K L] [NumberField L] in
/-- Any finite `S`-place classes and any archimedean classes are simultaneously
realized by a supported cohomology class. The outside integral coordinates
in this construction are zero. -/
theorem supportedSPlaceH2Localizations_surjective :
    Function.Surjective ((supportedSPlaceH2Localization K L S).prod
      (supportedSPlaceInfiniteH2Localization K L S)) := by
  exact (sPlaceFactorsH2Localizations_surjective K L S).comp
    (supportedSPlaceCohomologyIso K L S).toLinearEquiv.surjective

/-- Outside unramified integral factors make a supported class unique for
any prescribed finite and archimedean cohomology coordinates. -/
def supportedSPlaceH2LocalizationsEquiv
    (hfin : ∀ v : V, v ∉ S → ChosenFinitePlaceIsUnramified (K := K) (L := L) v) :
    groupCohomology (Rep.ofMulDistribMulAction Gal(L / K)
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S)) 2 ≃+
      (∀ v : {v : V // v ∈ S}, groupCohomology (Rep.ofMulDistribMulAction Gal(L / K) (Ain v)) 2) ×
        (∀ v : InfinitePlace K, groupCohomology (Rep.ofMulDistribMulAction Gal(L / K) (A∞ v)) 2) :=
  AddEquiv.ofBijective ((supportedSPlaceH2Localization K L S).prod
    (supportedSPlaceInfiniteH2Localization K L S))
    ⟨fun _ _ h => (supportedSPlaceCohomologyIso K L S).toLinearEquiv.injective
      (sPlaceFactorsH2_eq_of_localizations K L S hfin (congrArg Prod.fst h) (congrArg Prod.snd h)),
      supportedSPlaceH2Localizations_surjective K L S⟩

omit [IsGalois K L] [NumberField L] in
/-- Finite localization is the group cohomology map of the finite projection. -/
theorem supportedSPlaceH2Localization_apply
    (x : groupCohomology (Rep.ofMulDistribMulAction Gal(L/K)
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S)) 2)
    (v : {v : V // v ∈ S}) :
    supportedSPlaceH2Localization K L S x v =
      groupCohomology.map (MonoidHom.id (Gal(L / K)))
        (supportedSPlaceFiniteRepHom K L S v) 2 x := by
  rw [supportedSPlaceFiniteRepHom, groupCohomology.map_id_comp,
    groupCohomology.map_id_comp, groupCohomology.map_id_comp]
  rfl

omit [IsGalois K L] [NumberField L] in
/-- Archimedean localization is the group cohomology map of the archimedean projection. -/
theorem supportedSPlaceInfiniteH2Localization_apply
    (x : groupCohomology (Rep.ofMulDistribMulAction Gal(L/K)
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S)) 2)
    (v : InfinitePlace K) :
    supportedSPlaceInfiniteH2Localization K L S x v =
      groupCohomology.map (MonoidHom.id (Gal(L / K)))
        (supportedSPlaceInfiniteRepHom K L S v) 2 x := by
  rw [supportedSPlaceInfiniteRepHom, groupCohomology.map_id_comp,
    groupCohomology.map_id_comp]
  rfl

omit [NumberField L] in
/-- A supported class vanishes if its finite coordinates in `S` and all its archimedean
coordinates vanish, provided the finite extension is unramified outside `S`. -/
theorem supportedSPlaceH2_eq_zero_of_localizations
    (hfin : ∀ v : V, v ∉ S → ChosenFinitePlaceIsUnramified (K := K) (L := L) v)
    (x : groupCohomology (Rep.ofMulDistribMulAction Gal(L / K)
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S)) 2)
    (hfinite : ∀ v : {v : V // v ∈ S},
      groupCohomology.map (MonoidHom.id (Gal(L / K))) (supportedSPlaceFiniteRepHom K L S v) 2 x = 0)
    (hinfinite : ∀ v : InfinitePlace K,
      groupCohomology.map (MonoidHom.id (Gal(L / K)))
        (supportedSPlaceInfiniteRepHom K L S v) 2 x = 0) :
    x = 0 := by
  have hfinite' :
      supportedSPlaceH2Localization K L S x = supportedSPlaceH2Localization K L S 0 := by
    funext v
    rw [supportedSPlaceH2Localization_apply, map_zero]
    exact hfinite v
  have hinfinite' : supportedSPlaceInfiniteH2Localization K L S x =
      supportedSPlaceInfiniteH2Localization K L S 0 := by
    funext v
    rw [supportedSPlaceInfiniteH2Localization_apply, map_zero]
    exact hinfinite v
  exact (supportedSPlaceCohomologyIso K L S).toLinearEquiv.injective
    (sPlaceFactorsH2_eq_of_localizations K L S hfin hfinite' hinfinite')

end ClassFieldTower.Martinet.Shafarevich

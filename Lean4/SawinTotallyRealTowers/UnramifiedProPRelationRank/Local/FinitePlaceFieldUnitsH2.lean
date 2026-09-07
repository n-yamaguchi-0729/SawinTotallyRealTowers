import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePGroupLocalUnitsH2Structure
import GaloisCohomology.ProP.MultiplicativeInducedShapiro
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceAction
import ClassFieldTheory.AlgebraicNumberTheory.Adele.FinitePlaceTensorBlock

set_option autoImplicit false
/-!
# H² of finite-place field-unit blocks

The actual tensor block is an induced representation. Shapiro and the
chosen decomposition-group equivalence identify its cohomology with the
local field-unit cohomology. Finite Galois p-extensions therefore have
cyclic H² on every finite tensor block, with at most n elements of n-torsion.
-/

open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField TensorProduct ValuativeRel

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology CyclicCohomology
open AlgebraicNumberTheory.Valuations HilbertRamification
open LocalClassFieldTheory LocalFieldTheory

variable (K L : Type) [Field K] [NumberField K]
variable [Field L] [NumberField L] [Algebra K L]
variable [FiniteDimensional K L] [IsGalois K L]

local instance fieldH2DecompositionAction (v : HeightOneSpectrum (𝓞 K)) :
    MulDistribMulAction (ChosenFinitePlaceDecompositionGroup (K := K) (L := L) v)
      (ChosenFinitePlaceLocalizedFieldUnits (K := K) (L := L) v) :=
  chosenFinitePlaceDecompositionGroupLocalUnitsAction (K := K) (L := L) v

local instance fieldH2InducedCommGroup (v : HeightOneSpectrum (𝓞 K)) :
    CommGroup (ChosenFinitePlaceLocalPlaceBlock (K := K) (L := L) v) :=
  Subgroup.toCommGroup _

local instance fieldH2InducedAction (v : HeightOneSpectrum (𝓞 K)) :
    MulDistribMulAction Gal(L / K) (ChosenFinitePlaceLocalPlaceBlock (K := K) (L := L) v) :=
  chosenFinitePlaceLocalPlaceBlockAction (K := K) (L := L) v

local instance fieldH2TensorAction (v : HeightOneSpectrum (𝓞 K)) :
    MulDistribMulAction Gal(L / K) (v.adicCompletion K ⊗[K] L)ˣ :=
  scalarTensorUnitsAction (K := K) (L := L) (A := v.adicCompletion K)

private noncomputable def finiteTensorRepIsoInduced
    (v : HeightOneSpectrum (𝓞 K)) :
    Rep.ofMulDistribMulAction Gal(L / K) (v.adicCompletion K ⊗[K] L)ˣ ≅
      Rep.ofMulDistribMulAction Gal(L / K)
        (ChosenFinitePlaceLocalPlaceBlock (K := K) (L := L) v) := by
  let e := finitePlaceTensorUnitsEquivLocalPlaceBlock (K := K) (L := L) v
    (chosenFinitePlaceExtension (L := L) v)
  exact show Rep.ofMulDistribMulAction Gal(L / K) (v.adicCompletion K ⊗[K] L)ˣ ≅
      Rep.ofMulDistribMulAction Gal(L / K)
        (ChosenFinitePlaceLocalPlaceBlock (K := K) (L := L) v) from
    Rep.mkIso (Representation.Equiv.mk e.toAdditive.toIntLinearEquiv (by
      intro g
      apply LinearMap.ext
      intro x
      exact congrArg Additive.ofMul
        (finitePlaceTensorUnitsEquivLocalPlaceBlock_smul (K := K) (L := L) v
          (chosenFinitePlaceExtension (L := L) v) g x.toMul)))

private noncomputable def chosenFieldCohomologyIso
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    groupCohomology (Rep.ofMulDistribMulAction
      (ChosenFinitePlaceDecompositionGroup (K := K) (L := L) v)
      (ChosenFinitePlaceLocalizedFieldUnits (K := K) (L := L) v)) n ≅
    groupCohomology (Rep.ofAlgebraAutOnUnits
      (ChosenFinitePlaceBaseCompletion (K := K) v)
      (ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v)) n := by
  let C := ChosenFinitePlaceBaseCompletion (K := K) v
  let E := ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v
  let eLocal := decompositionGroupEquivAlgebraicLocalizationAut
    (HeightOneSpectrum.adicAbv K v) (RayClass.adicAbv_isNontrivial v)
    (chosenFinitePlaceExtension (L := L) v)
  let j := groupCohomology.mapIso
    (A := Rep.ofAlgebraAutOnUnits C E)
    (B := Rep.ofMulDistribMulAction
      (ChosenFinitePlaceDecompositionGroup (K := K) (L := L) v)
      (ChosenFinitePlaceLocalizedFieldUnits (K := K) (L := L) v))
    eLocal (LinearEquiv.refl ℤ (Additive Eˣ)) (by
      intro g
      apply LinearMap.ext
      intro x
      rfl) n
  exact j

private noncomputable def tensorCohomologyIsoInduced
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    groupCohomology (Rep.ofMulDistribMulAction Gal(L / K)
      (v.adicCompletion K ⊗[K] L)ˣ) n ≅
    groupCohomology (Rep.ofMulDistribMulAction Gal(L / K)
      (ChosenFinitePlaceLocalPlaceBlock (K := K) (L := L) v)) n :=
  (groupCohomology.functor ℤ Gal(L / K) n).mapIso (finiteTensorRepIsoInduced K L v)

private noncomputable def chosenInducedCohomologyIso
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    groupCohomology (Rep.ofMulDistribMulAction Gal(L / K)
      (ChosenFinitePlaceLocalPlaceBlock (K := K) (L := L) v)) n ≅
    groupCohomology (Rep.ofMulDistribMulAction
      (ChosenFinitePlaceDecompositionGroup (K := K) (L := L) v)
      (ChosenFinitePlaceLocalizedFieldUnits (K := K) (L := L) v)) n :=
  multiplicativeInducedCohomologyIso
    (ChosenFinitePlaceDecompositionGroup (K := K) (L := L) v)
    (ChosenFinitePlaceLocalizedFieldUnits (K := K) (L := L) v) n

/-- The actual finite tensor block has the cohomology of the chosen
local Galois field-unit representation, in every degree. -/
noncomputable def finitePlaceFieldUnitsCohomologyIso
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    groupCohomology (Rep.ofMulDistribMulAction Gal(L / K)
      (v.adicCompletion K ⊗[K] L)ˣ) n ≅
    groupCohomology (Rep.ofAlgebraAutOnUnits
      (ChosenFinitePlaceBaseCompletion (K := K) v)
      (ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v)) n :=
  tensorCohomologyIsoInduced K L v n ≪≫
    chosenInducedCohomologyIso K L v n ≪≫ chosenFieldCohomologyIso K L v n

omit [NumberField L] in
/-- Finite-place tensor H² is finite and cyclic for any finite Galois p-extension. -/
theorem finitePGroupFinitePlaceFieldUnitsH2_finite_isAddCyclic
    (p : ℕ) [Fact p.Prime] (hP : IsPGroup p Gal(L / K))
    (v : HeightOneSpectrum (𝓞 K)) :
    Finite (groupCohomology (Rep.ofMulDistribMulAction Gal(L / K)
      (v.adicCompletion K ⊗[K] L)ˣ) 2) ∧
    IsAddCyclic (groupCohomology (Rep.ofMulDistribMulAction Gal(L / K)
      (v.adicCompletion K ⊗[K] L)ˣ) 2) := by
  let C := ChosenFinitePlaceBaseCompletion (K := K) v
  let E := ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v
  let eLocal := decompositionGroupEquivAlgebraicLocalizationAut
    (HeightOneSpectrum.adicAbv K v) (RayClass.adicAbv_isNontrivial v)
    (chosenFinitePlaceExtension (L := L) v)
  have hLocal : IsPGroup p Gal(E / C) :=
    (hP.to_subgroup (ChosenFinitePlaceDecompositionGroup (K := K) (L := L) v)).of_equiv eLocal
  let i := (finitePlaceFieldUnitsCohomologyIso K L v 2).toLinearEquiv.toAddEquiv
  have : Finite (groupCohomology (Rep.ofAlgebraAutOnUnits C E) 2) :=
    (finitePGroupLocalUnitsH2_finite_natCard_le_finrank C p E hLocal).1
  have : IsAddCyclic (groupCohomology (Rep.ofAlgebraAutOnUnits C E) 2) :=
    finitePGroupLocalUnitsH2_isAddCyclic C p E hLocal
  exact ⟨Finite.of_injective i i.injective,
    isAddCyclic_of_surjective i.symm i.symm.surjective⟩

omit [NumberField L] in
/-- Positive n-torsion in each actual finite-place tensor H² has at most n elements. -/
theorem finitePGroupFinitePlaceFieldUnitsH2_torsion_natCard_le
    (p : ℕ) [Fact p.Prime] (hP : IsPGroup p Gal(L / K))
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (hn : 0 < n) :
    Nat.card {x : groupCohomology (Rep.ofMulDistribMulAction Gal(L / K)
      (v.adicCompletion K ⊗[K] L)ˣ) 2 // n • x = 0} ≤ n := by
  classical
  have hs := finitePGroupFinitePlaceFieldUnitsH2_finite_isAddCyclic K L p hP v
  let := hs.1
  let := hs.2
  let : Fintype (groupCohomology (Rep.ofMulDistribMulAction Gal(L / K)
      (v.adicCompletion K ⊗[K] L)ˣ) 2) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact IsAddCyclic.card_nsmul_eq_zero_le hn

end ClassFieldTower.Martinet.Shafarevich

import GaloisCohomology.Kummer.UnitsCohomologyCongr
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePGroupLocalUnitsH2Cyclic
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.UnramifiedCommonExtension
import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.FiniteUnramifiedField
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionTopology
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnramifiedFrobenius
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false

/-!
# Cyclic unit H² of finite local Galois p-extensions

The unramified field of the same degree supplies the auxiliary cyclic
extension. Its compositum with the given field is unramified of degree
equal to the ramification index. The resulting cyclicity proof transports
from an actual intermediate field in the separable closure to any finite
Galois p-extension.
-/

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology LocalClassFieldTheory LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
open scoped ValuativeRel

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

private theorem standardUnramified_isCyclic (d : ℕ) (hd : 0 < d) :
    IsCyclic Gal((localFiniteUnramifiedField K d hd)/K) := by
  let M := localFiniteUnramifiedField K d hd
  have : IsIntegralClosure 𝒪[M] 𝒪[K] M :=
    localCompleteDVF_integerRing_isIntegralClosure K M
  have : Module.Finite 𝒪[K] 𝒪[M] := localCompleteDVF_integerRing_moduleFinite K M
  exact isCyclic_galoisGroup_of_unramifiedValuation K M

private theorem intermediateFieldUnitsH2_isAddCyclic
    (F : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K F] [IsGalois K F]
    (p : ℕ) [Fact p.Prime] (hP : IsPGroup p Gal(F/K)) :
    IsAddCyclic (groupCohomology (Rep.ofAlgebraAutOnUnits K F) 2) := by
  let : NontriviallyNormedField F := finiteExtensionSpectralNormedField K F
  let : ValuativeRel F := finiteExtensionSpectralValuativeRel K F
  have : IsNonarchimedeanLocalField F := finiteExtensionSpectralIsNonarchimedeanLocalField K F
  have : Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation F) :=
    finiteExtensionSpectralValuation_hasExtension K F
  obtain ⟨he, hsup⟩ := relativeUnramifiedFixedField_ramification_eq_sup_sameDegree K F
  let m : ℕ := (𝓂[F] : Ideal 𝒪[F]).ramificationIdx 𝒪[K]
  let H := finiteAbstractFieldOfGaloisIntermediateField K F
  let N : IntermediateField K (SeparableClosure K) := relativeUnramifiedFixedField K H m he
  have : FiniteDimensional K N := relativeUnramifiedFixedField_absoluteFiniteDimensional K H m he
  have : IsGalois K N := relativeUnramifiedFixedField_actual_isGalois K F m he
  let : Algebra F N := relativeUnramifiedFixedField_actual_algebra K F m he
  have : IsScalarTower K F N := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have : FiniteDimensional F N := FiniteDimensional.right K F N
  have : IsGalois F N := IsGalois.tower_top_of_isGalois K F N
  let : NontriviallyNormedField N := finiteExtensionSpectralNormedField K N
  let : ValuativeRel N := finiteExtensionSpectralValuativeRel K N
  have : IsNonarchimedeanLocalField N := finiteExtensionSpectralIsNonarchimedeanLocalField K N
  have : Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation N) :=
    finiteExtensionSpectralValuation_hasExtension K N
  have : Valuation.HasExtension (ValuativeRel.valuation F) (ValuativeRel.valuation N) :=
    finiteExtensionSpectralValuation_hasExtension_of_tower K F N
  have : Module.Finite 𝒪[F] 𝒪[N] := localCompleteDVF_integerRing_moduleFinite F N
  have : IsUnramifiedValuedExtension F N :=
    relativeUnramifiedFixedField_actual_isUnramifiedValuedExtension K F m he
  let M : IntermediateField K (SeparableClosure K) :=
    localFiniteUnramifiedField K (Module.finrank K F) Module.finrank_pos
  have hMN : M ≤ N := by
    change M ≤ relativeUnramifiedFixedField K H m he
    rw [hsup]
    exact le_sup_right
  let : Algebra M N := (IntermediateField.inclusion hMN).toRingHom.toAlgebra
  have : IsScalarTower K M N := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have : IsCyclic Gal(M/K) := standardUnramified_isCyclic K (Module.finrank K F) Module.finrank_pos
  have hd : Module.finrank F N ∣ (𝓂[F] : Ideal 𝒪[F]).ramificationIdx 𝒪[K] := by
    rw [relativeUnramifiedFixedField_actual_finrank K F m he]
  have hdegree : Module.finrank K F ≤ Module.finrank K M :=
    (localFiniteUnramifiedField_finrank K (Module.finrank K F) Module.finrank_pos).symm.le
  exact finitePGroupLocalUnitsH2_isAddCyclic_of_unramified_tower K F M N p hP hd hdegree

/-- Unit-coefficient H² of every finite local Galois p-extension is cyclic. -/
theorem finitePGroupLocalUnitsH2_isAddCyclic
    (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (hP : IsPGroup p Gal(L/K)) :
    IsAddCyclic (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) := by
  let i : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let e : L ≃ₐ[K] i.fieldRange := i.equivFieldRange
  have : FiniteDimensional K i.fieldRange := e.toLinearEquiv.finiteDimensional
  have : IsGalois K i.fieldRange := e.transfer_galois.mp inferInstance
  have : IsAddCyclic (groupCohomology (Rep.ofAlgebraAutOnUnits K i.fieldRange) 2) :=
    intermediateFieldUnitsH2_isAddCyclic K i.fieldRange p (hP.of_equiv (AlgEquiv.autCongr e))
  let c := (unitsCohomologyCongrTop K L i.fieldRange e 2).toLinearEquiv.toAddEquiv
  exact isAddCyclic_of_surjective c.symm c.symm.surjective

/-- Positive n-torsion in local p-extension unit H² has at most n elements. -/
theorem finitePGroupLocalUnitsH2_torsion_natCard_le
    (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (hP : IsPGroup p Gal(L/K))
    (n : ℕ) (hn : 0 < n) :
    Nat.card {x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 // n • x = 0} ≤ n := by
  classical
  have : Finite (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :=
    (finitePGroupLocalUnitsH2_finite_natCard_le_finrank K p L hP).1
  have : IsAddCyclic (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :=
    finitePGroupLocalUnitsH2_isAddCyclic K p L hP
  let : Fintype (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact IsAddCyclic.card_nsmul_eq_zero_le hn

end ClassFieldTower.Martinet.Shafarevich

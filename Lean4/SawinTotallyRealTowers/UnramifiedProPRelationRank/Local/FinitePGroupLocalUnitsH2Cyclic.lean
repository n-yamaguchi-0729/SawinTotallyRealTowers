import GaloisCohomology.Kummer.FiniteGaloisTowerUnitsH2
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FiniteCyclicLocalUnitsH2
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FiniteCyclicUnramifiedTowerH2Restriction
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePGroupLocalUnitsH2
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false

/-!
# Cyclicity of local p-extension unit H² from an unramified tower

A generator of the cyclic auxiliary field's H² inflates into the kernel
of relative restriction. Middle exactness lifts it to the p-extension's
H², and injectivity preserves its order. The proven cardinality bound
then makes that lifted element a generator.
-/

open CategoryTheory
open scoped ValuativeRel

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology LocalClassFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable (K L M N : Type)
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [Field M] [Field N]
  [Algebra K L] [Algebra L N] [Algebra K N] [IsScalarTower K L N]
  [Algebra K M] [Algebra M N] [IsScalarTower K M N]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeRel N] [TopologicalSpace N] [IsNonarchimedeanLocalField N]
  [FiniteDimensional K L] [IsGalois K L] [FiniteDimensional L N] [IsGalois K N]
  [FiniteDimensional K M] [IsGalois K M] [IsCyclic Gal(M/K)]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [Valuation.HasExtension (ValuativeRel.valuation L) (ValuativeRel.valuation N)]
  [Module.Finite 𝒪[L] 𝒪[N]] [IsUnramifiedValuedExtension L N]
  (p : ℕ) [Fact p.Prime] (hP : IsPGroup p Gal(L/K))
  (hd : Module.finrank L N ∣ (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K])
  (hdegree : Module.finrank K L ≤ Module.finrank K M)

include hP hd hdegree

/-- An actual unramified auxiliary tower proves cyclicity of the unit H²
of a finite local Galois p-extension. -/
theorem finitePGroupLocalUnitsH2_isAddCyclic_of_unramified_tower :
    IsAddCyclic (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) := by
  have : FiniteDimensional K N := FiniteDimensional.trans K L N
  have : IsGalois L N := IsGalois.tower_top_of_isGalois K L N
  obtain ⟨hFinite, hcard⟩ := finitePGroupLocalUnitsH2_finite_natCard_le_finrank K p L hP
  have : Finite (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) := hFinite
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(M/K))
  let e : groupCohomology (Rep.ofAlgebraAutOnUnits K M) 2 ≃+ Additive Gal(M/K) :=
    finiteCyclicLocalUnitsH2AddEquivGalois K M g hg
  let c : groupCohomology (Rep.ofAlgebraAutOnUnits K M) 2 := e.symm (Additive.ofMul g)
  have hcOrder : addOrderOf c = Module.finrank K M :=
    (e.symm.addOrderOf_eq (Additive.ofMul g)).trans
      ((addOrderOf_ofMul_eq_orderOf g).trans
        ((orderOf_eq_card_of_forall_mem_zpowers hg).trans
          (IsGalois.card_aut_eq_finrank K M)))
  have hcZero : (finiteGaloisTowerUnitsH2Restriction K L N).hom
      ((finiteGaloisTowerUnitsH2Inflation K M N).hom c) = 0 :=
    congrArg (fun f : groupCohomology (Rep.ofAlgebraAutOnUnits K M) 2 ⟶
      groupCohomology (Rep.ofAlgebraAutOnUnits L N) 2 ↦ f.hom c)
      (finiteCyclicTowerUnitsH2_inflation_restriction_eq_zero K L M N hd)
  obtain ⟨b, hb⟩ := finiteGaloisTowerUnitsH2Restriction_ker_le_inflation_range K L N hcZero
  have hbOrder : addOrderOf b = addOrderOf c := by
    calc
      addOrderOf b = addOrderOf ((finiteGaloisTowerUnitsH2Inflation K L N).hom b) :=
        (addOrderOf_injective (finiteGaloisTowerUnitsH2Inflation K L N).hom.toAddMonoidHom
          (finiteGaloisTowerUnitsH2Inflation_injective K L N) b).symm
      _ = addOrderOf ((finiteGaloisTowerUnitsH2Inflation K M N).hom c) :=
        congrArg addOrderOf hb
      _ = addOrderOf c :=
        addOrderOf_injective (finiteGaloisTowerUnitsH2Inflation K M N).hom.toAddMonoidHom
          (finiteGaloisTowerUnitsH2Inflation_injective K M N) c
  apply isAddCyclic_of_card_le_addOrderOf b
  rw [hbOrder, hcOrder]
  exact hcard.trans hdegree

/-- Positive n-torsion has at most n elements in the resulting actual local H². -/
theorem finitePGroupLocalUnitsH2_torsion_natCard_le_of_unramified_tower
    (n : ℕ) (hn : 0 < n) :
    Nat.card {x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 // n • x = 0} ≤ n := by
  classical
  have : Finite (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :=
    (finitePGroupLocalUnitsH2_finite_natCard_le_finrank K p L hP).1
  have : IsAddCyclic (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :=
    finitePGroupLocalUnitsH2_isAddCyclic_of_unramified_tower K L M N p hP hd hdegree
  let : Fintype (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact IsAddCyclic.card_nsmul_eq_zero_le hn

end ClassFieldTower.Martinet.Shafarevich

import GaloisCohomology.ProP.FiniteCyclicH2TateH0
import ClassFieldTheory.LocalClassFieldTheory.Finite.Unramified.Cohomology

set_option autoImplicit false
/-!
# Integer-unit H² in an actual unramified local extension

The canonical unramified Frobenius and the existing unit-norm theorem
identify degree-two cohomology of the actual integer-unit representation
with a zero Tate norm quotient.  In particular every two-cocycle has an
integer-unit primitive, including in residue characteristic dividing the
extension degree.
-/

open CategoryTheory
open scoped ValuativeRel

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology
open LocalClassFieldTheory LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable (K L : Type) [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L] [IsGalois K L]
variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
variable [IsNonarchimedeanLocalField L]
variable [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
variable [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
variable [IsUnramifiedValuedExtension K L]

-- Fix the canonical integer-unit action once for both endpoints.
local instance : MulDistribMulAction Gal(L / K) 𝒪[L]ˣ :=
  galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L

/-- The actual integer-unit representation of a finite unramified local
extension has zero degree-two cohomology. -/
theorem unramifiedLocalIntegerUnitsH2_subsingleton :
    Subsingleton (groupCohomology (Rep.ofMulDistribMulAction Gal(L / K) 𝒪[L]ˣ) 2) := by
  let _ := AlgEquiv.fintype K L
  let _ : Subsingleton (HerbrandH0 Gal(L / K) 𝒪[L]ˣ) :=
    (unramified_units_tateCohomology_and_norm_surjective K L).1.1
  let e := finiteCyclicGroupH2IsoTateHZero
      (Rep.ofMulDistribMulAction Gal(L / K) 𝒪[L]ˣ)
      (arithmeticFrobeniusOfUnramifiedValuation K L)
      (arithmeticFrobeniusOfUnramifiedValuation_generates K L) ≪≫
    tateH0IsoHerbrandH0 (G := Gal(L / K)) (A := 𝒪[L]ˣ)
  exact Function.Injective.subsingleton e.toLinearEquiv.injective

/-- Every actual integer-unit two-cocycle in an unramified local extension
has an integer-unit one-cochain primitive. -/
theorem unramifiedLocalIntegerUnitsTwoCocycle_isCoboundary :
    ∀ c : groupCohomology.cocycles₂ (Rep.ofMulDistribMulAction Gal(L / K) 𝒪[L]ˣ),
      ∃ b : Gal(L / K) → Additive 𝒪[L]ˣ,
        (groupCohomology.d₁₂ (Rep.ofMulDistribMulAction Gal(L / K) 𝒪[L]ˣ)).hom b = c.1 := by
  let _ := unramifiedLocalIntegerUnitsH2_subsingleton K L
  intro c
  exact (groupCohomology.H2π_eq_zero_iff c).1 (Subsingleton.elim _ _)

end ClassFieldTower.Martinet.Shafarevich

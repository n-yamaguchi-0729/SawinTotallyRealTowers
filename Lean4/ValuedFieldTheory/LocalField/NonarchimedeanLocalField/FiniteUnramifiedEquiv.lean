import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.LocalRing.RingHom.Basic

set_option autoImplicit false
/-!
# Unramifiedness across an actual finite local-field equivalence

Integrality produces the integer-ring equivalence from the field equivalence.
Transport of the actual maximal-ideal equality then preserves ramification
index one. No valuation-preservation certificate is assumed: integral-closure
membership supplies it. The two extension towers are fixed explicitly, with
no new data instances and one local formally-unramified proof instance.
-/

open scoped ValuativeRel
noncomputable section
namespace ClassFieldTower.Martinet.Shafarevich
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable (K L M : Type) [Field K] [ValuativeRel K]
  [Field L] [ValuativeRel L] [Field M] [ValuativeRel M]
  [Algebra K L] [Algebra K M]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L] [IsIntegralClosure 𝒪[M] 𝒪[K] M]

private theorem finiteLocalAlgEquiv_mem_integerRing (e : L ≃ₐ[K] M) (x : 𝒪[L]) :
    e (x : L) ∈ 𝒪[M] := by
  have hx : IsIntegral 𝒪[K] (x : L) :=
    (IsIntegralClosure.isIntegral_iff (A := 𝒪[L]) (R := 𝒪[K]) (B := L)).2 ⟨x, rfl⟩
  have hy : IsIntegral 𝒪[K] (e (x : L)) := IsIntegral.map e.toAlgHom hx
  obtain ⟨y, hy⟩ :=
    (IsIntegralClosure.isIntegral_iff (A := 𝒪[M]) (R := 𝒪[K]) (B := M)).1 hy
  exact hy ▸ y.property

variable
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation M)]

/-- Restriction of a field equivalence to the actual integral closures. -/
def finiteLocalIntegerAlgEquiv (e : L ≃ₐ[K] M) : 𝒪[L] ≃ₐ[𝒪[K]] 𝒪[M] where
  toFun x := ⟨e (x : L), finiteLocalAlgEquiv_mem_integerRing K L M e x⟩
  invFun x := ⟨e.symm (x : M), finiteLocalAlgEquiv_mem_integerRing K M L e.symm x⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)
  map_mul' x y := Subtype.ext (e.map_mul x y)
  map_add' x y := Subtype.ext (e.map_add x y)
  commutes' x := Subtype.ext (e.commutes (x : K))

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [FiniteDimensional K L] [FiniteDimensional K M]
  [Module.Finite 𝒪[K] 𝒪[L]] [Module.Finite 𝒪[K] 𝒪[M]]

/-- Actual unramifiedness transports under a finite local-field equivalence. -/
theorem isUnramifiedValuedExtension_of_algEquiv (e : L ≃ₐ[K] M)
    [IsUnramifiedValuedExtension K M] : IsUnramifiedValuedExtension K L := by
  let ei := finiteLocalIntegerAlgEquiv K L M e
  have hmap : Ideal.map (algebraMap 𝒪[K] 𝒪[L]) (𝓂[K] : Ideal 𝒪[K]) =
      (𝓂[L] : Ideal 𝒪[L]) := by
    have h := congrArg (Ideal.map ei.symm.toRingHom)
      (maximalIdeal_map_eq_maximalIdeal_of_unramifiedValuation K M)
    rw [Ideal.map_map, show ei.symm.toRingHom.comp (algebraMap 𝒪[K] 𝒪[M]) =
      algebraMap 𝒪[K] 𝒪[L] from RingHom.ext (fun x => ei.symm.commutes x),
      IsLocalRing.map_maximalIdeal_of_surjective ei.symm.toRingHom ei.symm.surjective] at h
    exact h
  let : Algebra.FormallyUnramified 𝒪[K] 𝒪[L] :=
    Algebra.FormallyUnramified.iff_map_maximalIdeal_eq.mpr
      ⟨Algebra.IsAlgebraic.isSeparable_of_perfectField, hmap⟩
  exact ⟨Ideal.ramificationIdx_eq_one _ _⟩

end ClassFieldTower.Martinet.Shafarevich

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.EverywhereUnramifiedProPCompositum
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

set_option autoImplicit false
/-!
# Finite support in the maximal everywhere-unramified pro-p compositum

Finite-dimensional intermediate fields are compact in the lattice of
intermediate fields.  Consequently, an inclusion into the maximal compositum
already factors through a supremum of finitely many bundled finite extensions.
-/

open scoped NumberField

noncomputable section

universe u v

namespace ClassFieldTower.Martinet

/-- A finite-dimensional intermediate field is a compact element of the
complete lattice of intermediate fields. -/
theorem finiteDimensional_intermediateField_isCompactElement
    {F : Type u} {E : Type v}
    [Field F] [Field E] [Algebra F E]
    (L : IntermediateField F E) [FiniteDimensional F L] :
    IsCompactElement L := by
  have hEss : Algebra.EssFiniteType F L := inferInstance
  obtain ⟨s, hs⟩ := IntermediateField.essFiniteType_iff.mp hEss
  rw [← hs]
  exact IntermediateField.adjoin_finset_isCompactElement s

/-- A finite-dimensional intermediate field below a supremum is already
below a finite sub-supremum. -/
theorem finiteDimensional_le_iSup_exists_finset
    {F : Type u} {E : Type v} {I : Type*}
    [Field F] [Field E] [Algebra F E]
    (L : IntermediateField F E) [FiniteDimensional F L]
    (f : I → IntermediateField F E)
    (hL : L ≤ ⨆ i, f i) :
    ∃ s : Finset I, L ≤ ⨆ i ∈ s, f i := by
  exact CompleteLattice.IsCompactElement.exists_finset_of_le_iSup
    (IntermediateField F E)
    (finiteDimensional_intermediateField_isCompactElement L) f hL

/-- A finite-dimensional intermediate field below the maximal compositum is
already below the supremum of finitely many bundled extensions. -/
theorem finiteDimensional_le_maximalEverywhereUnramifiedProP_exists_finset
    (F : Type u) [Field F] [NumberField F]
    (p : ℕ) [Fact p.Prime]
    (L : IntermediateField F (AlgebraicClosure F))
    [FiniteDimensional F L]
    (hL : L ≤ maximalEverywhereUnramifiedProP F p) :
    ∃ s : Finset (FiniteEverywhereUnramifiedProPExtension F p),
      L ≤ ⨆ E ∈ s, E.field := by
  rw [maximalEverywhereUnramifiedProP_eq_iSup_extension] at hL
  exact finiteDimensional_le_iSup_exists_finset L
    (fun E : FiniteEverywhereUnramifiedProPExtension F p ↦ E.field) hL

end ClassFieldTower.Martinet

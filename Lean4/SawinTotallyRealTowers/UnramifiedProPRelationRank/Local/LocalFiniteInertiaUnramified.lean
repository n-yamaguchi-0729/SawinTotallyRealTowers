import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.InertiaUnramifiedExtension
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramifiedEquiv

set_option autoImplicit false
/-!
# Inertia-trivial finite embeddings give actual unramified local extensions

The image of the supplied finite field embedding is constructed inside the
local separable closure. Inertia fixes that actual intermediate field; the
spectral criterion applies there, and the resulting unramifiedness is moved
back to the original valued extension using its integral closure.

Instance audit: the original `K → L` tower is inherited. The image has its
single intermediate-field `K`-algebra and one canonical spectral norm/valuation
pair; all remaining local instances are finiteness, Galois, or valuation-
compatibility proofs. No second algebra path or valuation on one target is
introduced, and the spectral setup occurs only once.
-/

open scoped ValuativeRel
noncomputable section
namespace ClassFieldTower.Martinet.Shafarevich
open LocalFieldTheory LocalClassFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable (K L : Type)
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [Module.Finite 𝒪[K] 𝒪[L]] [IsIntegralClosure 𝒪[L] 𝒪[K] L]

/-- Pointwise inertia-triviality on a finite embedding forces actual
valuation-ring ramification index one. -/
theorem localFiniteExtension_isUnramified_of_inertiaFixes
    (f : L →ₐ[K] SeparableClosure K)
    (hf : ∀ sigma ∈ (localResidueDegree K).toMonoidHom.ker,
      ∀ x : L, sigma (f x) = f x) : IsUnramifiedValuedExtension K L := by
  let E := f.fieldRange
  let e : L ≃ₐ[K] E := f.equivFieldRange
  let _ : FiniteDimensional K E := e.toLinearEquiv.finiteDimensional
  let _ : IsGalois K E := IsGalois.of_algEquiv e
  let _ : NontriviallyNormedField E := finiteExtensionSpectralNormedField K E
  let _ : ValuativeRel E := finiteExtensionSpectralValuativeRel K E
  let _ : IsNonarchimedeanLocalField E := finiteExtensionSpectralIsNonarchimedeanLocalField K E
  let _ : Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation E) :=
    finiteExtensionSpectralValuation_hasExtension K E
  let _ : Module.Finite 𝒪[K] 𝒪[E] := localCompleteDVF_integerRing_moduleFinite K E
  let _ : IsIntegralClosure 𝒪[E] 𝒪[K] E := localCompleteDVF_integerRing_isIntegralClosure K E
  have hfix : (localResidueDegree K).toMonoidHom.ker ≤ E.fixingSubgroup := by
    intro sigma hsigma x
    obtain ⟨y, hy⟩ := x.property
    change sigma x.val = x.val
    rw [← hy]
    exact hf sigma hsigma y
  let _ : IsUnramifiedValuedExtension K E :=
    localIntermediateField_isUnramified_of_inertia_le K E hfix
  exact isUnramifiedValuedExtension_of_algEquiv K L E e

end ClassFieldTower.Martinet.Shafarevich

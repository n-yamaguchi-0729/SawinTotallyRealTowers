import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceH2Localization
import ClassFieldTheory.AlgebraicNumberTheory.Galois.CyclicPrimeSubextension
import ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.FinitePlace
import ValuedFieldTheory.Ramification.HilbertRamification.DecompositionGroup
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.Normal.Defs

set_option autoImplicit false

/-!
# Absolute decomposition at a completely split finite place

Restrict the chosen absolute valuation to the actual finite Galois layer.
An absolute decomposition automorphism preserves this restricted valuation
class. Complete splitting makes its decomposition group trivial, independently
of the chosen exact extension of the base absolute value.
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTower.Sawin

open ClassFieldTower.Martinet.Shafarevich AlgebraicNumberTheory.Valuations

/-- At a completely split place, every element of the actual absolute
decomposition subgroup restricts trivially to the finite Galois layer. -/
theorem finitePlaceAbsoluteDecomposition_restrictNormal_eq_one_of_splitsCompletely
    (F : Type) [Field F] [NumberField F]
    (M : FiniteGaloisIntermediateField F (AlgebraicClosure F))
    (v : HeightOneSpectrum (𝓞 F))
    (hsplit : FinitePlaceSplitsCompletely (K := F) (L := M) v)
    (σ : finitePlaceAbsoluteDecompositionGroup F v) :
    AlgEquiv.restrictNormalHom M σ.1 = 1 := by
  let w := finitePlaceAbsoluteValueExtension F v
  let wM := restrictAbsoluteValueExtensionToIntermediate
    (HeightOneSpectrum.adicAbv F v) w M.toIntermediateField
  have hmem : σ.1.restrictNormal M ∈
      HilbertRamification.absoluteValueDecompositionGroup F wM.1 := by
    intro x
    change w.1 (algebraMap M (AlgebraicClosure F) (σ.1.restrictNormal M x)) < 1 ↔
      w.1 (algebraMap M (AlgebraicClosure F) x) < 1
    rw [AlgEquiv.restrictNormal_commutes]
    exact σ.property (algebraMap M (AlgebraicClosure F) x)
  have hbot : HilbertRamification.absoluteValueDecompositionGroup F wM.1 = ⊥ :=
    absoluteValueDecompositionGroup_eq_bot_independent_extension
      (HeightOneSpectrum.adicAbv F v) (RayClass.adicAbv_isNontrivial v)
      (chosenFinitePlaceExtension (L := M) v) wM hsplit
  exact Subgroup.mem_bot.mp (hbot ▸ hmem)

end ClassFieldTower.Sawin

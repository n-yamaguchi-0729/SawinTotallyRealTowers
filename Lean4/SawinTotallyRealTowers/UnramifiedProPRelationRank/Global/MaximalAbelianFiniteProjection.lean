import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MaximalAbelianGlobalArtin

set_option autoImplicit false
/-!
# Finite projections detect maximal-abelian Artin values

The existing infinite-Galois inverse-limit equivalence detects equality
of maximal-abelian automorphisms on finite Galois intermediate fields.
On the Artin side, projection at a finite one-place idele is the actual
chosen finite-place Artin symbol. These two interfaces close the finite
part of local-global Artin comparison without a new comparison assumption.
-/

open NumberField IsDedekindDomain
open scoped NumberField
noncomputable section
namespace ClassFieldTower.Martinet.Shafarevich
open GlobalClassFieldTheory.Reciprocity

variable (F : Type) [Field F] [NumberField F]

omit [NumberField F] in
/-- Equality in the maximal-abelian Galois group is detected by all finite
Galois restriction maps, by the existing inverse-limit equivalence. -/
theorem maximalAbelianGalois_ext_of_finite_restrictions
    (sigma tau : Gal(_root_.maximalAbelianExtension F/F))
    (h : ∀ E : FiniteGaloisIntermediateField F (_root_.maximalAbelianExtension F),
      AlgEquiv.restrictNormalHom E sigma = AlgEquiv.restrictNormalHom E tau) :
    sigma = tau := by
  apply (InfiniteGalois.continuousMulEquivToLimit F (_root_.maximalAbelianExtension F)).injective
  apply Subtype.ext
  funext E
  exact h E.unop

/-- The finite projection of a maximal-abelian Artin value at a one-place
idele is the actual chosen finite-place Artin symbol. -/
theorem maximalAbelianGlobalArtin_finitePlace_finiteProjection
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ)
    (E : FiniteGaloisIntermediateField F (_root_.maximalAbelianExtension F)) :
    let : NumberField E := NumberField.of_module_finite F E
    AlgEquiv.restrictNormalHom E
      (maximalAbelianGlobalArtin F (IdeleGroup.finitePlaceIdeleClass v a)) =
      chosenFinitePlaceArtinMonoidHom (K := F) (L := E) v a := by
  let : NumberField E := NumberField.of_module_finite F E
  exact (maximalAbelianGlobalArtin_finiteProjection F (IdeleGroup.finitePlaceIdele v a) E).trans
    (globalArtinMonoidHom_finitePlaceIdele (K := F) (L := E) v a)

end ClassFieldTower.Martinet.Shafarevich

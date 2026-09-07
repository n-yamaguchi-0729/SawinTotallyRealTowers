import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.LocalAbsoluteArtinEmbedding
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SemilinearNaturality

set_option autoImplicit false
/-!
# Semilinear transport of actual absolute Artin representatives

Finite Artin naturality supplies the action on every finite abelian extension.
The profinite finite-quotient realization then identifies the absolute value.
The valuation certificate is supplied for the actual completion comparison by
`FinitePlaceCompletionValuationCompatibility`.
-/

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open LocalClassFieldTheory
open scoped IsMulCommutative

variable (K K' : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']

private theorem absoluteLocalArtin_semilinear_finite_action
    (c : K ≃+* K') (e : AlgebraicClosure K ≃+* AlgebraicClosure K')
    (he : ∀ x : K, e (algebraMap K (AlgebraicClosure K) x) =
      algebraMap K' (AlgebraicClosure K') (c x))
    (hc : SemilinearValuationCompatible K K' c)
    (a : Kˣ) (sigma : Gal(AlgebraicClosure K / K))
    (hsigma : (QuotientGroup.mk (show Field.absoluteGaloisGroup K from sigma) :
      Field.absoluteGaloisGroupAbelianization K) = absoluteLocalArtinMap K a)
    (L : Type) [Field L] [Algebra K' L]
    [FiniteDimensional K' L] [IsAbelianGalois K' L]
    (i : L →ₐ[K'] AlgebraicClosure K') (z : L) :
    e (sigma (e.symm (i z))) =
      i (abelianLocalArtinMonoidHom K' L (Units.map c.toMonoidHom a) z) := by
  let _ : Algebra K K' := c.toRingHom.toAlgebra
  let _ : Algebra K L := ((algebraMap K' L).comp c.toRingHom).toAlgebra
  let _ : IsScalarTower K K' L := IsScalarTower.of_algebraMap_eq' rfl
  let _ : FiniteDimensional K K' :=
    Module.Finite.of_surjective (Algebra.linearMap K K') c.surjective
  let _ : FiniteDimensional K L := Module.Finite.trans K' L
  let _ : IsGalois K L := IsGalois.of_equiv_equiv
    (f := c.symm) (g := RingEquiv.refl L) (by
      ext x
      change algebraMap K' L (c (c.symm x)) = algebraMap K' L x
      rw [c.apply_symm_apply])
  let g := semilinearGaloisGroupCongr K K' L L c (RingEquiv.refl L) (fun _ ↦ rfl)
  let _ : IsAbelianGalois K L :=
    { is_comm.comm := fun s t ↦ g.injective (by rw [map_mul, map_mul]; exact mul_comm _ _) }
  let j : L →ₐ[K] AlgebraicClosure K :=
    { toRingHom := e.symm.toRingHom.comp i.toRingHom
      commutes' := by
        intro x
        change e.symm (i (algebraMap K' L (c x))) = algebraMap K (AlgebraicClosure K) x
        rw [i.commutes, ← he, e.symm_apply_apply] }
  have h := congrArg e (absoluteLocalArtinMap_lift_action K L j a sigma hsigma z)
  change e (sigma (e.symm (i z))) = e (e.symm (i (abelianLocalArtinMonoidHom K L a z))) at h
  rw [e.apply_symm_apply] at h
  have hArtin := abelianLocalArtinMonoidHom_semilinear_action K K' L L
    c (RingEquiv.refl L) (fun _ ↦ rfl) hc a z
  change abelianLocalArtinMonoidHom K L a z =
    abelianLocalArtinMonoidHom K' L (Units.map c.toMonoidHom a) z at hArtin
  exact h.trans (congrArg i hArtin)

/-- Conjugating an actual absolute Artin representative gives the actual
Artin representative after a valuation-compatible base-field equivalence. -/
theorem absoluteLocalArtinMap_semilinear_lift
    (c : K ≃+* K') (e : AlgebraicClosure K ≃+* AlgebraicClosure K')
    (he : ∀ x : K, e (algebraMap K (AlgebraicClosure K) x) =
      algebraMap K' (AlgebraicClosure K') (c x))
    (hc : SemilinearValuationCompatible K K' c)
    (a : Kˣ) (sigma : Gal(AlgebraicClosure K / K))
    (hsigma : (QuotientGroup.mk (show Field.absoluteGaloisGroup K from sigma) :
      Field.absoluteGaloisGroupAbelianization K) = absoluteLocalArtinMap K a) :
    (QuotientGroup.mk (show Field.absoluteGaloisGroup K' from
      semilinearGaloisGroupCongr K K' (AlgebraicClosure K) (AlgebraicClosure K')
        c e he sigma) : Field.absoluteGaloisGroupAbelianization K') =
      absoluteLocalArtinMap K' (Units.map c.toMonoidHom a) := by
  let tau := semilinearGaloisGroupCongr K K'
    (AlgebraicClosure K) (AlgebraicClosure K') c e he sigma
  let a' := Units.map c.toMonoidHom a
  apply (separableToStandardAbsoluteAbelianizationEquiv K').symm.injective
  rw [separableToStandardAbsoluteAbelianizationEquiv_symm_artinMap]
  change (QuotientGroup.mk (standardToSeparableAbsoluteGaloisEquiv K' tau) :
    localAbsoluteAbelianProfinite K') = separableAbsoluteLocalArtinMap K' a'
  apply (absoluteGaloisAbelianizationLimitEquiv K').injective
  apply Subtype.ext
  funext N
  change QuotientGroup.mk' N.toSubgroup
    (QuotientGroup.mk (standardToSeparableAbsoluteGaloisEquiv K' tau) :
      localAbsoluteAbelianProfinite K') =
    QuotientGroup.mk' N.toSubgroup (separableAbsoluteLocalArtinMap K' a')
  apply (absoluteFiniteQuotientEquiv K' N).injective
  change absoluteFiniteQuotientEquiv K' N
      (QuotientGroup.mk (QuotientGroup.mk
        (standardToSeparableAbsoluteGaloisEquiv K' tau) : localAbsoluteAbelianProfinite K')) =
    absoluteFiniteQuotientEquiv K' N
      (QuotientGroup.mk' N.toSubgroup (separableAbsoluteLocalArtinMap K' a'))
  rw [absoluteFiniteQuotientEquiv_mk_mk, separableAbsoluteLocalArtinMap_finiteProjection]
  change AlgEquiv.restrictNormalHom (absoluteFiniteQuotientField K' N)
      (standardToSeparableAbsoluteGaloisEquiv K' tau) =
    absoluteFiniteQuotientEquiv K' N ((absoluteFiniteQuotientEquiv K' N).symm
      (abelianLocalArtinMap K' (absoluteFiniteQuotientField K' N) a'))
  rw [ContinuousMulEquiv.apply_symm_apply]
  let E := absoluteFiniteQuotientField K' N
  have hmap : abelianLocalArtinMap K' E a' = abelianLocalArtinMonoidHom K' E a' := by
    change (abelianLocalArtinMap K' E).toMonoidHom a' = _
    rw [abelianLocalArtinMap_toMonoidHom]
  rw [hmap]
  ext z
  let i : E →ₐ[K'] AlgebraicClosure K' :=
    (separableClosure K' (AlgebraicClosure K')).val.comp E.val
  have hr := congrArg (fun x : SeparableClosure K' ↦ (x : AlgebraicClosure K'))
    (AlgEquiv.restrictNormal_commutes (standardToSeparableAbsoluteGaloisEquiv K' tau) E z)
  exact hr.trans
    (absoluteLocalArtin_semilinear_finite_action K K' c e he hc a sigma hsigma E i z)

end ClassFieldTower.Martinet.Shafarevich

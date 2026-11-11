/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseNaturality

/-!
# Semilinear naturality of the specified Artin map in independent universes

The existing norm-restriction square is applied to the degree-one base extension
specified by the field equivalence. Its norm is the inverse field equivalence,
and actual restriction is inverse conjugation. Thus the result compares the
same Artin maps and the original field actions.
-/

@[expose] public section

noncomputable section

namespace LocalClassFieldTheory.Universe

open LocalFieldTheory
open scoped ValuativeRel

universe u v w x

/-- Conjugating an extension by a base-algebra equivalence preserves the actual Artin map,
independently of the universes of the base and the two extension fields. -/
theorem abelianLocalArtinMonoidHom_autCongr
    (K : Type u) (L : Type v) (M : Type w)
    [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsAbelianGalois K L] [IsAbelianGalois K M] (e : L ≃ₐ[K] M) :
    (AlgEquiv.autCongr e).toMonoidHom.comp (abelianLocalArtinMonoidHom K L) =
      abelianLocalArtinMonoidHom K M := by
  let : Algebra M L := e.symm.toRingHom.toAlgebra
  let : IsScalarTower K M L :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro a
      exact (e.symm.commutes a).symm)
  have he : AlgEquiv.restrictNormalHom M = (AlgEquiv.autCongr e).toMonoidHom := by
    apply MonoidHom.ext
    intro σ
    apply AlgEquiv.ext
    intro a
    apply e.symm.injective
    calc
      e.symm ((AlgEquiv.restrictNormalHom M σ) a) = σ (e.symm a) :=
        AlgEquiv.restrictNormal_commutes σ M a
      _ = e.symm ((AlgEquiv.autCongr e σ) a) :=
        (e.symm_apply_apply (σ (e.symm a))).symm
  rw [← he]
  exact abelianLocalArtinMonoidHom_restrict_tower K M L

/-- The actual finite abelian local Artin map commutes with simultaneous
semilinear equivalences of the base local field and the target extension.

The valuation-extension condition says that the local-field valuation on
`K'`, pulled back through `eK`, is the valuation on `K`.  It is the genuine
valued-field compatibility needed by norm--restriction, rather than an
assumption of the desired Artin equality. -/
theorem abelianLocalArtinMonoidHom_semilinear_conjugation
    (K : Type u) (K' : Type v) (L : Type w) (L' : Type x)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field K'] [ValuativeRel K'] [TopologicalSpace K']
    [IsNonarchimedeanLocalField K']
    [Field L] [Field L']
    [Algebra K L] [Algebra K' L']
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional K' L'] [IsAbelianGalois K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (hcomm : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x))
    (hExt : SemilinearValuationCompatible K K' eK) :
    (semilinearGaloisGroupCongr K K' L L' eK eL hcomm).toMonoidHom.comp
        (abelianLocalArtinMonoidHom K L) =
      (abelianLocalArtinMonoidHom K' L').comp
        (Units.map eK.toMonoidHom) := by
  let : Algebra K K' := eK.toRingHom.toAlgebra
  change
    (ValuativeRel.valuation K).HasExtension
      (ValuativeRel.valuation K') at hExt
  let : Algebra K L' :=
    ((algebraMap K' L').comp eK.toRingHom).toAlgebra
  let : Algebra L L' := eL.toRingHom.toAlgebra
  let : IsScalarTower K K' L' :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K L L' :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro x
      exact (hcomm x).symm)
  let eKAlg : K ≃ₐ[K] K' :=
    { eK with
      commutes' := fun _ => rfl }
  let : FiniteDimensional K K' :=
    FiniteDimensional.of_surjective
      eKAlg.toLinearMap eKAlg.surjective
  let : Algebra.IsSeparable K K' :=
    AlgEquiv.Algebra.isSeparable eKAlg
  let :
      (ValuativeRel.valuation K).HasExtension
        (ValuativeRel.valuation K') :=
    hExt
  let conjugation :=
    semilinearGaloisGroupCongr K K' L L' eK eL hcomm
  let restriction :
      Gal(L' / K') →* Gal(L / K) :=
    (AlgEquiv.restrictNormalHom L).comp
      (AlgEquiv.restrictScalarsHom K)
  have hrestriction (τ : Gal(L' / K')) :
      restriction τ = conjugation.symm τ := by
    apply AlgEquiv.ext
    intro x
    apply eL.injective
    calc
      eL (restriction τ x) =
          τ (eL x) := by
        exact
          AlgEquiv.restrictNormal_commutes
            ((AlgEquiv.restrictScalarsHom K) τ) L x
      _ = eL (conjugation.symm τ x) := by
        exact (congrArg (fun σ : Gal(L' / K') => σ (eL x))
          (conjugation.apply_symm_apply τ)).symm.trans
          (semilinearGaloisGroupCongr_apply_equiv
            K K' L L' eK eL hcomm (conjugation.symm τ) x)
  have hnorm (a : Kˣ) :
      normUnits K K' (Units.map eK.toMonoidHom a) = a := by
    apply Units.ext
    change Algebra.norm K (eK (a : K)) = (a : K)
    have hnorm := Algebra.norm_eq_of_equiv_equiv
      (RingEquiv.refl K) eK (by
        apply RingHom.ext
        intro x
        rfl) (a : K)
    change Algebra.norm K (a : K) = Algebra.norm K (eK (a : K)) at hnorm
    rw [Algebra.norm_self] at hnorm
    exact hnorm.symm
  have hnaturality :=
    abelianLocalArtinMonoidHom_norm_restriction K K' L L'
  apply MonoidHom.ext
  intro a
  have hpoint :=
    DFunLike.congr_fun hnaturality
      (Units.map eK.toMonoidHom a)
  change
    restriction
        (abelianLocalArtinMonoidHom K' L'
          (Units.map eK.toMonoidHom a)) =
      abelianLocalArtinMonoidHom K L
        (normUnits K K' (Units.map eK.toMonoidHom a)) at hpoint
  rw [hrestriction, hnorm] at hpoint
  change
    conjugation (abelianLocalArtinMonoidHom K L a) =
      abelianLocalArtinMonoidHom K' L'
        (Units.map eK.toMonoidHom a)
  calc
    conjugation (abelianLocalArtinMonoidHom K L a) =
        conjugation
          (conjugation.symm
            (abelianLocalArtinMonoidHom K' L'
              (Units.map eK.toMonoidHom a))) :=
      congrArg conjugation hpoint.symm
    _ =
        abelianLocalArtinMonoidHom K' L'
          (Units.map eK.toMonoidHom a) :=
      conjugation.apply_symm_apply _

/-- Pointwise Galois-automorphism form of semilinear naturality for the
abelian local Artin map.  Concrete consumers should use this opaque generic
boundary instead of specializing `DFunLike.congr_fun` to a large dependent
local-field instance tower. -/
theorem abelianLocalArtinMonoidHom_semilinear_conjugation_apply
    (K : Type u) (K' : Type v) (L : Type w) (L' : Type x)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field K'] [ValuativeRel K'] [TopologicalSpace K']
    [IsNonarchimedeanLocalField K']
    [Field L] [Field L']
    [Algebra K L] [Algebra K' L']
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional K' L'] [IsAbelianGalois K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (hcomm : ∀ x : K,
      eL (algebraMap K L x) = algebraMap K' L' (eK x))
    (hExt : SemilinearValuationCompatible K K' eK)
    (u : Kˣ) :
    semilinearGaloisGroupCongr K K' L L' eK eL hcomm
        (abelianLocalArtinMonoidHom K L u) =
      abelianLocalArtinMonoidHom K' L'
        (Units.map eK.toMonoidHom u) :=
  DFunLike.congr_fun
    (abelianLocalArtinMonoidHom_semilinear_conjugation
      K K' L L' eK eL hcomm hExt) u

/-- Triviality transports backwards through a semilinear equivalence of local
Artin data.  Keeping the injectivity calculation generic prevents concrete
finite-place instance towers from entering consumer proof terms. -/
theorem abelianLocalArtinMonoidHom_eq_one_of_semilinear
    (K : Type u) (K' : Type v) (L : Type w) (L' : Type x)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field K'] [ValuativeRel K'] [TopologicalSpace K']
    [IsNonarchimedeanLocalField K']
    [Field L] [Field L']
    [Algebra K L] [Algebra K' L']
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional K' L'] [IsAbelianGalois K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (hcomm : ∀ x : K,
      eL (algebraMap K L x) = algebraMap K' L' (eK x))
    (hExt : SemilinearValuationCompatible K K' eK)
    (u : Kˣ)
    (htrivial :
      abelianLocalArtinMonoidHom K' L'
          (Units.map eK.toMonoidHom u) = 1) :
    abelianLocalArtinMonoidHom K L u = 1 := by
  let conjugation :=
    semilinearGaloisGroupCongr K K' L L' eK eL hcomm
  apply conjugation.injective
  calc
    conjugation (abelianLocalArtinMonoidHom K L u) =
        abelianLocalArtinMonoidHom K' L'
          (Units.map eK.toMonoidHom u) :=
      abelianLocalArtinMonoidHom_semilinear_conjugation_apply
        K K' L L' eK eL hcomm hExt u
    _ = 1 := htrivial
    _ = conjugation 1 := (map_one conjugation).symm

/-- Pointwise form of semilinear naturality for the abelian local Artin map.

This theorem keeps the equality of Galois automorphisms and its dependent
instance tower behind an opaque generic boundary.  Concrete consumers can
transport the action on one element without specializing and then reducing
the full monoid-hom equality. -/
theorem abelianLocalArtinMonoidHom_semilinear_action
    (K : Type u) (K' : Type v) (L : Type w) (L' : Type x)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field K'] [ValuativeRel K'] [TopologicalSpace K']
    [IsNonarchimedeanLocalField K']
    [Field L] [Field L']
    [Algebra K L] [Algebra K' L']
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional K' L'] [IsAbelianGalois K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (hcomm : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x))
    (hExt : SemilinearValuationCompatible K K' eK)
    (u : Kˣ) (z : L) :
    eL (abelianLocalArtinMonoidHom K L u z) =
      abelianLocalArtinMonoidHom K' L'
        (Units.map eK.toMonoidHom u) (eL z) := by
  have hArtin :=
    DFunLike.congr_fun
      (abelianLocalArtinMonoidHom_semilinear_conjugation
        K K' L L' eK eL hcomm hExt) u
  calc
    eL (abelianLocalArtinMonoidHom K L u z) =
        semilinearGaloisGroupCongr
          K K' L L' eK eL hcomm
          (abelianLocalArtinMonoidHom K L u) (eL z) :=
      (semilinearGaloisGroupCongr_apply_equiv
        K K' L L' eK eL hcomm
        (abelianLocalArtinMonoidHom K L u) z).symm
    _ = abelianLocalArtinMonoidHom K' L'
          (Units.map eK.toMonoidHom u) (eL z) :=
      congrArg (fun sigma : Gal(L' / K') => sigma (eL z)) hArtin

end LocalClassFieldTheory.Universe

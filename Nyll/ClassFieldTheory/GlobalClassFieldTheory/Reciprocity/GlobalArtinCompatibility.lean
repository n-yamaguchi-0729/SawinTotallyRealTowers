/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalArtinFiniteSupportApproximation
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.SeparableClosurePadicLift
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.FinitePadicCyclicData
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.FinitePadicAuxiliaryField
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.Factorization
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfiniteLocalGlobalArtinCompatibility
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.TopologicalGlobalNormResidue
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.NumberFieldNormResidue
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Basic
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.SinglePlace

/-!
# Compatibility of the global Artin map with global reciprocity

For a finite abelian extension of number fields, the preliminary global
Artin map is the product of the chosen local Artin maps.  The finite-place
and infinite-place compatibility theorems identify every one-place factor
with the canonical global norm-residue map.

Only finitely many finite local Artin factors of an idele are nontrivial.
The finite-support approximation theorem replaces an arbitrary idele by
the product of those one-place ideles modulo an ordinary idèle norm.
It follows that the preliminary global Artin map is exactly the pullback
of the canonical norm-residue map along `I_K → C_K`.

In particular, the local product is trivial on every principal idele.
The global Artin map therefore descends to the idele class group, where
it is the canonical surjective reciprocity homomorphism and has the
genuine idele-class norm range as its kernel.
-/



@[expose] public section

open scoped NumberField BigOperators IsMulCommutative
open NumberField IsDedekindDomain
open IdeleGroup RelativeIdeleGroup

noncomputable section

universe u v

namespace GlobalClassFieldTheory
namespace Reciprocity

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The canonical Artin map on the standard principal quotient gives the
product of the actual local Artin factors on every idèle. -/
theorem standardNumberFieldArtin_comp_toStandardClass_eq_globalArtin :
    (standardNumberFieldArtinContinuousMonoidHom K L).toMonoidHom.comp
        (IdeleGroup.toStandardClass K) = globalArtinMonoidHom (K := K) (L := L) := by
  apply MonoidHom.ext
  intro a
  let p := IdeleGroup.toStandardClass K
  let f := (standardNumberFieldArtinContinuousMonoidHom K L).toMonoidHom
  let a₀ := artinFiniteSupportApproximation (K := K) (L := L) a
  let n := standardNumberFieldNormResidueEquivOfEmbedding K L
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L)
  let e : Gal(L/K) ≃* Group.Abelianization Gal(L/K) := Group.Abelianization.equivOfComm
  have hc := globalNormClassFromIdele_eq_artinFiniteSupportApproximation (K := K) (L := L) a
  have hApprox : f (p a) = f (p a₀) := congrArg (fun c => e.symm (n c)) hc
  change f (p a) = globalArtinMonoidHom (K := K) (L := L) a
  calc
    _ = f (p a₀) := hApprox
    _ = globalArtinMonoidHom (K := K) (L := L) a₀ := by
      dsimp only [a₀]
      rw [artinFiniteSupportApproximation]
      simp only [map_mul, map_prod]
      apply congrArg₂ (· * ·)
      · apply Finset.prod_congr rfl
        intro v _
        change globalNormResidueMonoidHom K L (p _) = globalArtinMonoidHom (K := K) (L := L) _
        rw [globalArtinMonoidHom_infinitePlaceIdele]
        exact DFunLike.congr_fun
          (globalNormResidueMonoidHom_comp_infinitePlaceIdeleClass (K := K) (L := L) v)
          (IdeleGroup.infiniteComponent v a)
      · apply Finset.prod_congr rfl
        intro v _
        change globalNormResidueMonoidHom K L (p _) = globalArtinMonoidHom (K := K) (L := L) _
        rw [globalArtinMonoidHom_finitePlaceIdele]
        exact DFunLike.congr_fun
          (globalNormResidueMonoidHom_comp_finitePlaceIdeleClass (K := K) (L := L) v.1)
          (IdeleGroup.finiteComponent v.1 a)
    _ = _ := (globalArtinMonoidHom_eq_artinFiniteSupportApproximation
      (K := K) (L := L) a).symm

/-- The chosen local Artin product is trivial on every principal
idele.  This is the global Artin product formula with the geometric
Frobenius normalization used by the local maps.
The inverse arithmetic normalization is exposed in `ArithmeticNormalization`. -/
@[simp]
theorem globalArtinMonoidHom_principalIdele
    (x : Kˣ) :
    globalArtinMonoidHom
        (K := K) (L := L)
        (IdeleGroup.principalIdele K x) =
      1 := by
  have h := DFunLike.congr_fun
    (standardNumberFieldArtin_comp_toStandardClass_eq_globalArtin (K := K) (L := L))
    (IdeleGroup.principalIdele K x)
  rw [← h]
  change standardNumberFieldArtinContinuousMonoidHom K L
    (IdeleGroup.toStandardClass K (IdeleGroup.principalIdele K x)) = 1
  rw [IdeleGroup.toStandardClass_principalIdele, map_one]

/-- Expanded form of the global product formula: the product of all
chosen infinite local symbols and the finite-support product of all
chosen finite local symbols of a principal idele is one. -/
theorem chosenLocalArtin_product_principalIdele
    (x : Kˣ) :
    (∏ v : InfinitePlace K,
        chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v
          (IdeleGroup.infiniteComponent v
            (IdeleGroup.principalIdele K x))) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K),
        chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v
          (IdeleGroup.finiteComponent v
            (IdeleGroup.principalIdele K x)) =
      1 := by
  rw [← globalArtinMonoidHom_apply]
  exact
    globalArtinMonoidHom_principalIdele
      (K := K) (L := L) x

/-- Evaluation of the descended Artin homomorphism on an idele
representative recovers the chosen-local-factor product. -/
theorem globalNormResidueMonoidHom_mk
    (a : IdeleGroup K) :
    globalNormResidueMonoidHom K L
        (IdeleGroup.toStandardClass K a) =
      globalArtinMonoidHom (K := K) (L := L) a := by
  exact DFunLike.congr_fun
    (standardNumberFieldArtin_comp_toStandardClass_eq_globalArtin (K := K) (L := L)) a

end Reciprocity
end GlobalClassFieldTheory

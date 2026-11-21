/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalArtinCompatibility
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerAlgEquivNaturality
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.MathlibAbsoluteGaloisBaseEquiv

/-!
# Finite global Artin maps under compatible field equivalences

The actual norm--restriction square, specialized to degree-one field towers,
proves semilinear naturality on each idèle class. No kernel characterization
is used to identify the values of the maps.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory.Reciprocity

universe u v w x

variable {K : Type u} {L : Type v}
  [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsAbelianGalois K L]

/-- Descent of the existing idèle norm--restriction square to idèle classes. -/
theorem globalIdeleClassArtinMonoidHom_norm_restriction
    {M : Type w} {N : Type x}
    [Field M] [NumberField M] [Field N] [NumberField N]
    [Algebra K M] [Algebra M N] [Algebra K N] [IsScalarTower K M N]
    [Algebra L N] [IsScalarTower K L N] [IsAbelianGalois M N] :
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K)).comp
        (globalNormResidueMonoidHom M N) =
      (globalNormResidueMonoidHom K L).comp
        (_root_.ideleClassNorm K M) := by
  apply MonoidHom.ext
  intro c
  obtain ⟨a, rfl⟩ := IdeleGroup.toStandardClass_surjective M c
  change
    ((AlgEquiv.restrictNormalHom L).comp (AlgEquiv.restrictScalarsHom K))
        (globalNormResidueMonoidHom M N
          (IdeleGroup.toStandardClass M a)) =
      globalNormResidueMonoidHom K L
        (_root_.ideleClassNorm K M
          (IdeleGroup.toStandardClass M a))
  rw [globalNormResidueMonoidHom_mk, ideleClassNorm_mk,
    globalNormResidueMonoidHom_mk]
  exact DFunLike.congr_fun
    (globalArtinMonoidHom_norm_restriction (K := K) (L := L)
      (K' := M) (L' := N)) a

/-- The finite Artin norm square on standard idèle classes of the original fields. -/
theorem standardNumberFieldArtin_norm_restriction
    {M : Type w} {N : Type x}
    [Field M] [NumberField M] [Field N] [NumberField N]
    [Algebra K M] [Algebra M N] [Algebra K N] [IsScalarTower K M N]
    [Algebra L N] [IsScalarTower K L N] [IsAbelianGalois M N]
    (c : NumberField.IdeleClassGroup (𝓞 M) M) :
    AlgEquiv.restrictNormalHom L
        ((standardNumberFieldArtinContinuousMonoidHom M N c).restrictScalars K) =
      standardNumberFieldArtinContinuousMonoidHom K L (NumberField.IdeleClassGroup.norm K M c) := by
  exact DFunLike.congr_fun
    (globalIdeleClassArtinMonoidHom_norm_restriction
      (K := K) (L := L) (M := M) (N := N)) c

private theorem globalIdeleClassArtinMonoidHom_norm_self
    (c : IdeleClassGroup K) :
    globalNormResidueMonoidHom K L
        (_root_.ideleClassNorm K K c) =
      globalNormResidueMonoidHom K L c := by
  have h := DFunLike.congr_fun
    (globalIdeleClassArtinMonoidHom_norm_restriction
      (K := K) (L := L) (M := K) (N := L)) c
  have hrestrict (σ : Gal(L / K)) : AlgEquiv.restrictScalarsHom K σ = σ :=
    AlgEquiv.ext fun _ => rfl
  simpa only [MonoidHom.comp_apply, AlgEquiv.restrictNormalHom_id,
    MonoidHom.id_apply, hrestrict] using h.symm

/-- Compatible equivalences of the actual base and extension fields intertwine
finite global Artin maps on every idèle class by semilinear conjugation. -/
theorem globalIdeleClassArtinMonoidHom_semilinear
    {M : Type w} {N : Type x}
    [Field M] [NumberField M] [Field N] [NumberField N]
    [Algebra M N] [IsAbelianGalois M N]
    (e : K ≃ₐ[ℚ] M) (E : L ≃ₐ[ℚ] N)
    (hE : ∀ a : K, E (algebraMap K L a) = algebraMap M N (e a))
    (c : IdeleClassGroup K) :
    ClassFieldTheory.semilinearGaloisEquiv e.toRingEquiv E.toRingEquiv hE
        (globalNormResidueMonoidHom K L c) =
      globalNormResidueMonoidHom M N (ideleClassCongr e c) := by
  let : Algebra K M := e.toRingHom.toAlgebra
  let : Algebra L N := E.toRingHom.toAlgebra
  let : Algebra K N := ((algebraMap M N).comp e.toRingHom).toAlgebra
  have : IsScalarTower K M N := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower K L N := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact (hE a).symm)
  have hnorm :
      _root_.ideleClassNorm K M (ideleClassCongr e c) =
        _root_.ideleClassNorm K K c := by
    have h := ideleClassCongr_ideleClassNorm
      (K := K) (L := K) (K' := K) (L' := M)
      (AlgEquiv.refl : K ≃ₐ[ℚ] K) e (fun _ => rfl) c
    rw [ideleClassCongr_refl] at h
    exact h.symm
  let σ := globalNormResidueMonoidHom M N (ideleClassCongr e c)
  have hrestrict := DFunLike.congr_fun
    (globalIdeleClassArtinMonoidHom_norm_restriction
      (K := K) (L := L) (M := M) (N := N)) (ideleClassCongr e c)
  change AlgEquiv.restrictNormalHom L (AlgEquiv.restrictScalarsHom K σ) =
      globalNormResidueMonoidHom K L
        (_root_.ideleClassNorm K M (ideleClassCongr e c)) at hrestrict
  rw [hnorm, globalIdeleClassArtinMonoidHom_norm_self] at hrestrict
  apply AlgEquiv.ext
  intro y
  obtain ⟨z, rfl⟩ := E.surjective y
  change E ((globalNormResidueMonoidHom K L c)
      (E.symm (E z))) = σ (E z)
  rw [E.symm_apply_apply]
  have hvalue := congrArg (fun τ : Gal(L/K) => E (τ z)) hrestrict
  have hcommutes := AlgEquiv.restrictNormal_commutes
    (AlgEquiv.restrictScalarsHom K σ) L z
  change E (AlgEquiv.restrictNormalHom L (AlgEquiv.restrictScalarsHom K σ) z) =
      σ (E z) at hcommutes
  exact hvalue.symm.trans hcommutes

end GlobalClassFieldTheory.Reciprocity

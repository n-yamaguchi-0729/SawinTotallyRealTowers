/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.StandardFieldInclusion
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.RelativeNormComparison
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerAlgEquivNaturality
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Equiv
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.Equiv

/-!
# Standard idele classes and the relative tensor presentation

The single scalar-extension comparison respects the actual inclusion, norm,
and conjugation maps. Arithmetic consumers share these comparison squares.
-/

@[expose] public section

open scoped NumberField TensorProduct

noncomputable section

namespace NumberField.IdeleClassGroup

universe u v

variable (K : Type u) (L : Type v)
  [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

omit [FiniteDimensional K L] in
/-- The relative Galois action on the standard principal quotient is field transport. -/
@[reducible] def relativeGaloisAction :
    MulDistribMulAction (L ≃ₐ[K] L) (IdeleClassGroup (𝓞 L) L) :=
  actionOfFieldHom (AlgEquiv.restrictScalarsHom ℚ)

/-- The actual scalar-extension comparison with the standard principal quotient. -/
abbrev relativeClassComparison :
    RelativeIdeleGroup.ClassGroup K L ≃* IdeleClassGroup (𝓞 L) L :=
  relativeIdeleClassBaseChangeMulEquiv (K := K) (L := L)

omit [FiniteDimensional K L] in
private theorem restrictScalars_refl_commutes (σ : L ≃ₐ[K] L) (x : K) :
    (σ.restrictScalars ℚ) (algebraMap K L x) =
      algebraMap K L ((AlgEquiv.refl : K ≃ₐ[ℚ] K) x) :=
  σ.commutes x

omit [FiniteDimensional K L] in
private theorem relativeCongr_eq_conjugation (σ : L ≃ₐ[K] L)
    (z : RelativeAdeleRing K L) :
    relativeAdeleCongrOfAlgEquiv (AlgEquiv.refl : K ≃ₐ[ℚ] K)
        (σ.restrictScalars ℚ) (restrictScalars_refl_commutes K L σ) z =
      RelativeIdeleGroup.conjugation K L σ z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
      simp only [map_add, hx, hy]
  | tmul a x =>
      calc
        _ = adeleCongr (AlgEquiv.refl : K ≃ₐ[ℚ] K) a ⊗ₜ[K] σ x :=
          relativeAdeleCongrOfAlgEquiv_tmul _ _ (restrictScalars_refl_commutes K L σ) a x
        _ = a ⊗ₜ[K] σ x := congrArg (fun y : AdeleRing (𝓞 K) K => y ⊗ₜ[K] σ x)
          (adeleCongr_refl a)
        _ = _ := (RelativeIdeleGroup.conjugation_tmul K L σ a x).symm

attribute [local instance] RelativeIdeleGroup.relativeIdeleMulDistribMulAction in
/-- The standard idele comparison preserves the original top-field conjugation. -/
theorem relativeIdeleBaseChange_smul (σ : L ≃ₐ[K] L) (a : RelativeIdeleGroup K L) :
    relativeIdeleBaseChangeMulEquiv (K := K) (L := L) (σ • a) =
      ideleCongr (σ.restrictScalars ℚ) (relativeIdeleBaseChangeMulEquiv (K := K) (L := L) a) := by
  rw [← relativeIdeleBaseChangeMulEquiv_congrOfAlgEquiv
    (AlgEquiv.refl : K ≃ₐ[ℚ] K) (σ.restrictScalars ℚ) (restrictScalars_refl_commutes K L σ)]
  apply congrArg (relativeIdeleBaseChangeMulEquiv (K := K) (L := L))
  apply Units.ext
  exact (relativeCongr_eq_conjugation K L σ a).symm

omit [FiniteDimensional K L] in
private theorem relativeClassCongr_eq_smul (σ : L ≃ₐ[K] L)
    (c : RelativeIdeleGroup.ClassGroup K L) :
    relativeIdeleClassCongrOfAlgEquiv (AlgEquiv.refl : K ≃ₐ[ℚ] K)
        (σ.restrictScalars ℚ) (restrictScalars_refl_commutes K L σ) c = σ • c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  let q := QuotientGroup.mk' (RelativeIdeleGroup.principalSubgroup K L)
  let eK : K ≃ₐ[ℚ] K := AlgEquiv.refl
  let eL := σ.restrictScalars ℚ
  let h := restrictScalars_refl_commutes K L σ
  have hu : relativeIdeleCongrOfAlgEquiv eK eL h a = σ • a := by
    apply Units.ext
    exact relativeCongr_eq_conjugation K L σ (a : RelativeAdeleRing K L)
  change relativeIdeleClassCongrOfAlgEquiv eK eL h (q a) = σ • q a
  calc
    _ = q (relativeIdeleCongrOfAlgEquiv eK eL h a) :=
      relativeIdeleClassCongrOfAlgEquiv_mk eK eL h a
    _ = q (σ • a) := congrArg q hu
    _ = _ := (RelativeIdeleGroup.smul_class_mk K L σ a).symm

/-- The comparison intertwines relative conjugation with standard field transport. -/
theorem relativeClassComparison_conjugation (σ : L ≃ₐ[K] L)
    (c : RelativeIdeleGroup.ClassGroup K L) :
    relativeClassComparison K L (σ • c) =
      congr (σ.restrictScalars ℚ) (relativeClassComparison K L c) := by
  let eK : K ≃ₐ[ℚ] K := AlgEquiv.refl
  let eL := σ.restrictScalars ℚ
  let h := restrictScalars_refl_commutes K L σ
  calc
    _ = relativeClassComparison K L (relativeIdeleClassCongrOfAlgEquiv eK eL h c) :=
      congrArg (relativeClassComparison K L) (relativeClassCongr_eq_smul K L σ c).symm
    _ = _ := relativeIdeleClassBaseChangeMulEquiv_congrOfAlgEquiv eK eL h c

omit [FiniteDimensional K L] in
/-- Scalar inclusion commutes with the relative-to-standard comparison. -/
theorem fieldInclusion_relativeClassComparison (a : _root_.IdeleClassGroup K) :
    fieldInclusion K L a =
      relativeClassComparison K L (RelativeIdeleGroup.classInclusion K L a) :=
  (relativeIdeleClassBaseChangeMulEquiv_classInclusion (K := K) (L := L) a).symm

/-- The standard norm is the same determinant norm on the relative quotient. -/
theorem norm_relativeClassComparison (c : RelativeIdeleGroup.ClassGroup K L) :
    norm K L (relativeClassComparison K L c) =
      RelativeIdeleGroup.classNorm K L c :=
  ordinaryIdeleClassNorm_relativeIdeleClassBaseChange (K := K) (L := L) c

section CompatibleNorm

variable {K' L' : Type*} [Field K'] [NumberField K'] [Field L'] [NumberField L']
  [Algebra K' L'] [FiniteDimensional K' L']

/-- Transport of both fields in a compatible algebra square preserves the
same standard determinant norm. -/
theorem norm_congr_of_compatible (eK : K ≃ₐ[ℚ] K') (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x))
    (c : IdeleClassGroup (𝓞 L) L) :
    congr eK (norm K L c) = norm K' L' (congr eL c) := by
  obtain ⟨d, rfl⟩ := (relativeClassComparison K L).surjective c
  have hTop := relativeIdeleClassBaseChangeMulEquiv_congrOfAlgEquiv eK eL h d
  change relativeClassComparison K' L' (relativeIdeleClassCongrOfAlgEquiv eK eL h d) =
    congr eL (relativeClassComparison K L d) at hTop
  rw [← hTop, norm_relativeClassComparison, norm_relativeClassComparison]
  exact relativeIdeleClassCongrOfAlgEquiv_ideleClassNorm eK eL h d

/-- The norm subgroup transports along the actual compatible field equivalences. -/
theorem norm_range_map_congr_of_compatible (eK : K ≃ₐ[ℚ] K') (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x)) :
    (norm K L).range.map (congr eK).toMonoidHom = (norm K' L').range := by
  ext y
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨congr eL c, (norm_congr_of_compatible K L eK eL h c).symm⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨d, rfl⟩ := (congr eL).surjective c
    exact ⟨norm K L d, ⟨d, rfl⟩, norm_congr_of_compatible K L eK eL h d⟩

end CompatibleNorm

end NumberField.IdeleClassGroup

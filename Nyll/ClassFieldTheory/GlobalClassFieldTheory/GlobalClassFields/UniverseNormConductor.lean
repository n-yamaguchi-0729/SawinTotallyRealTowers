/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormConductor
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivIdeleClassTopology
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.SmallModel
public import Nyll.ClassFieldTheory.Algebra.ShrinkFiniteExtension

/-!
# The actual norm conductor in independent universes

Compatible small field models preserve the determinant norm on the original
idele classes. Transport of its open image therefore supplies a defining
modulus for the original subgroup, with no change to the norm map.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace GlobalClassFieldTheory.GlobalClassFields

universe u v

variable (K : Type u) (L : Type v) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The genuine ordinary norm image is open for independently sized fields. -/
theorem ideleClassNorm_range_isOpen_universe :
    IsOpen (((_root_.ideleClassNorm K L).range :
      Subgroup (IdeleClassGroup K)) : Set (IdeleClassGroup K)) := by
  let : Small.{0} K := ClassFieldTheory.numberField_small K
  let : Small.{0} L := ClassFieldTheory.numberField_small L
  let : NumberField (Shrink.{0} K) := ClassFieldTheory.numberField_shrink K
  let : NumberField (Shrink.{0} L) := ClassFieldTheory.numberField_shrink L
  let : Algebra (Shrink.{0} K) (Shrink.{0} L) := HasseArf.shrinkAlgebra K L
  let : FiniteDimensional (Shrink.{0} K) (Shrink.{0} L) :=
    HasseArf.shrink_finiteDimensional K L
  let : IsGalois (Shrink.{0} K) (Shrink.{0} L) :=
    IsGalois.of_equiv_equiv (f := (Shrink.ringEquiv K).symm)
      (g := (Shrink.ringEquiv L).symm) (HasseArf.shrinkAlgebra_commutes K L)
  let eK : K ≃ₐ[ℚ] Shrink.{0} K := (Shrink.ringEquiv K).symm.toRatAlgEquiv
  let eL : L ≃ₐ[ℚ] Shrink.{0} L := (Shrink.ringEquiv L).symm.toRatAlgEquiv
  have hcomm (a : K) : eL (algebraMap K L a) =
      algebraMap (Shrink.{0} K) (Shrink.{0} L) (eK a) :=
    (DFunLike.congr_fun (HasseArf.shrinkAlgebra_commutes K L) a).symm
  let e := ideleClassCongrContinuousMulEquiv eK
  have hmap := ordinaryIdeleClassNorm_range_map_congrOfAlgEquiv eK eL hcomm
  have hpre : (((_root_.ideleClassNorm K L).range : Subgroup (IdeleClassGroup K)) :
      Set (IdeleClassGroup K)) =
      e ⁻¹' (((_root_.ideleClassNorm (Shrink.{0} K) (Shrink.{0} L)).range :
        Subgroup (IdeleClassGroup (Shrink.{0} K))) :
          Set (IdeleClassGroup (Shrink.{0} K))) := by
    ext c
    change c ∈ (_root_.ideleClassNorm K L).range ↔
      ideleClassCongr eK c ∈
        (_root_.ideleClassNorm (Shrink.{0} K) (Shrink.{0} L)).range
    rw [← hmap]
    constructor
    · intro hc
      exact ⟨c, hc, rfl⟩
    · rintro ⟨d, hd, hdc⟩
      have hdc' : d = c := (ideleClassCongr eK).injective hdc
      exact hdc' ▸ hd
  rw [hpre]
  exact (ideleClassNorm_range_isOpen
    (K := Shrink.{0} K) (L := Shrink.{0} L)).preimage e.continuous

/-- The original norm subgroup is conductorial; only the proof of the
existence of a defining modulus is transported. -/
def ideleClassNormConductorialSubgroup_universe : ConductorialSubgroup K :=
  ⟨(_root_.ideleClassNorm K L).range,
    RayClass.exists_congruenceSubgroup_le_of_isOpen _
      (ideleClassNorm_range_isOpen_universe K L)⟩

/-- In universe zero this is the same conductorial subgroup, including
the original norm map, by proof irrelevance. -/
theorem ideleClassNormConductorialSubgroup_universe_eq_native
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E] :
    ideleClassNormConductorialSubgroup_universe F E =
      ideleClassNormConductorialSubgroup (K := F) (L := E) := rfl

end GlobalClassFieldTheory.GlobalClassFields

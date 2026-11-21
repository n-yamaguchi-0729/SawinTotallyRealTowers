/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitFiniteEmbedding
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.StandardGaloisDescent
public import Nyll.GaloisCohomology.Kummer.Abstract.KummerDelta
public import Nyll.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup

/-!
# Fixed-point descent in the standard idele-class limit

A fixed limit class has a representative at a common finite normal level.
Injectivity makes that representative Galois fixed, and actual finite
idele-class descent identifies it with a class of the fixed field.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory.Reciprocity

universe u

variable (K : Type u) [Field K] [NumberField K]

noncomputable local instance directLimitScalarAction :
    SMul Gal(SeparableClosure K/K) (ideleClassDirectLimit K) :=
  ideleClassDirectLimitSMul K

/-- Every fixed limit class comes from the standard class group of its
finite intermediate field. The finite descent is the actual Hilbert-90
idele-class descent. -/
theorem directLimit_fixed_exists_ideleClass
    (F : IntermediateField K (SeparableClosure K)) [FiniteDimensional K F]
    (z : ideleClassDirectLimit K)
    (hz_fixed : ∀ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K,
      σ ∈ F.fixingSubgroup → σ • z = z) :
    ∃ c : NumberField.IdeleClassGroup (𝓞 F) F,
      intermediateIdeleClassToDirectLimit K F c = z := by
  classical
  obtain ⟨E, c, hzc⟩ := DirectLimit.exists_eq_mk
    (F := fun E : FiniteGaloisIntermediateField K (SeparableClosure K) =>
      NumberField.IdeleClassGroup (𝓞 E) E)
    (f := fun _ _ h => finiteIdeleClassTransition K h) z
  let U : FiniteGaloisIntermediateField K (SeparableClosure K) :=
    E ⊔ finiteIdeleClassNormalClosure K F
  let hEU : E ≤ U := le_sup_left
  let hFU : F ≤ U.toIntermediateField := (IntermediateField.le_normalClosure F).trans le_sup_right
  let d : NumberField.IdeleClassGroup (𝓞 U) U := finiteIdeleClassEmbedding K hEU c
  have hzU : z = finiteIdeleClassToDirectLimit K U d :=
    hzc.trans (ideleClassDirectLimit_mk_apply K c hEU).symm
  let : Algebra F U.toIntermediateField := (IntermediateField.inclusion hFU).toRingHom.toAlgebra
  let : IsScalarTower K F U.toIntermediateField := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower ℚ F U.toIntermediateField :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let : FiniteDimensional F U := FiniteDimensional.right K F U
  let : IsGalois F U := IsGalois.tower_top_of_isGalois K F U
  have hd_fixed (η : U ≃ₐ[F] U) :
      NumberField.IdeleClassGroup.congr (η.restrictScalars ℚ) d = d := by
    let τ : U ≃ₐ[K] U := η.restrictScalars K
    obtain ⟨σ, hσU⟩ := (AlgEquiv.restrictNormalHom_surjective
      (F := K) (K₁ := U) (E := SeparableClosure K)) τ
    have hσF : σ ∈ F.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      let x : F := ⟨y, hy⟩
      have hres := DFunLike.congr_fun hσU (algebraMap F U x)
      calc
        σ y = σ ((algebraMap F U x : U) : SeparableClosure K) := rfl
        _ = (((AlgEquiv.restrictNormalHom U σ) (algebraMap F U x) : U) :
            SeparableClosure K) :=
          (AlgEquiv.restrictNormal_commutes σ U (algebraMap F U x)).symm
        _ = ((η (algebraMap F U x) : U) : SeparableClosure K) :=
          congrArg Subtype.val hres
        _ = ((algebraMap F U x : U) : SeparableClosure K) :=
          congrArg Subtype.val (η.commutes x)
        _ = y := rfl
    have hzσ := hz_fixed σ hσF
    change (ideleClassDirectLimitSMul K).smul σ z = z at hzσ
    rw [hzU, finiteIdeleClassToDirectLimit_smul] at hzσ
    have hdσ := finiteIdeleClassToDirectLimit_injective K U hzσ
    have hrestrict : finiteIdeleClassAutomorphism K U σ = η.restrictScalars ℚ :=
      congrArg (fun e : U ≃ₐ[K] U => e.restrictScalars ℚ) hσU
    change NumberField.IdeleClassGroup.congr (finiteIdeleClassAutomorphism K U σ) d = d at hdσ
    exact (congrArg (fun e : U ≃ₐ[ℚ] U => NumberField.IdeleClassGroup.congr e d)
      hrestrict.symm).trans hdσ
  obtain ⟨q, hq⟩ :=
    (NumberField.IdeleClassGroup.mem_range_fieldInclusion_iff_fixed F U d).2 hd_fixed
  refine ⟨q, ?_⟩
  rw [intermediateIdeleClassToDirectLimit_of_le K U hFU q]
  change finiteIdeleClassToDirectLimit K U
    (NumberField.IdeleClassGroup.fieldInclusion F U q) = z
  rw [hq]
  exact hzU.symm

/-- Standard additive idele classes map to the corresponding actual fixed
part of the one coefficient representation. -/
def intermediateIdeleClassToFixed
    (F : IntermediateField K (SeparableClosure K)) [FiniteDimensional K F] :
    Additive (NumberField.IdeleClassGroup (𝓞 F) F) →+
      KummerTheory.ambientFixedAddSubgroup (ideleClassRepresentation K)
        (RamificationTheory.closedFixingSubgroup K (SeparableClosure K) F) :=
  (MonoidHom.toAdditive (intermediateIdeleClassToDirectLimit K F)).codRestrict
    (KummerTheory.ambientFixedAddSubgroup (ideleClassRepresentation K)
      (RamificationTheory.closedFixingSubgroup K (SeparableClosure K) F)) (by
        intro c
        refine (KummerTheory.mem_ambientFixedAddSubgroup_iff _ _ _).mpr ?_
        intro σ
        exact congrArg Additive.ofMul
          (intermediateIdeleClassToDirectLimit_fixed K F σ.1 σ.2 (Additive.toMul c)))

/-- Injectivity of the actual finite-level inclusion remains injectivity in
the corresponding fixed part. -/
theorem intermediateIdeleClassToFixed_injective
    (F : IntermediateField K (SeparableClosure K)) [FiniteDimensional K F] :
    Function.Injective (intermediateIdeleClassToFixed K F) := by
  intro a b h
  apply Additive.toMul.injective
  apply intermediateIdeleClassToDirectLimit_injective K F
  exact congrArg (fun x => Additive.toMul x.1) h

/-- Actual finite descent supplies every element of the fixed part. -/
theorem intermediateIdeleClassToFixed_surjective
    (F : IntermediateField K (SeparableClosure K)) [FiniteDimensional K F] :
    Function.Surjective (intermediateIdeleClassToFixed K F) := by
  intro x
  let z : ideleClassDirectLimit K := Additive.toMul x.1
  have hz_fixed (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
      (hσ : σ ∈ F.fixingSubgroup) : σ • z = z := by
    have hfixed := x.2 ⟨σ, hσ⟩
    change Additive.ofMul (σ • z) = Additive.ofMul z at hfixed
    exact Additive.ofMul.injective hfixed
  obtain ⟨c, hc⟩ := directLimit_fixed_exists_ideleClass K F z hz_fixed
  refine ⟨Additive.ofMul c, ?_⟩
  apply Subtype.ext
  change Additive.ofMul (intermediateIdeleClassToDirectLimit K F c) = x.1
  rw [hc]
  exact ofMul_toMul x.1

/-- The fixed part over any finite intermediate field is its actual standard
idele class group, through the canonical inclusion into the same limit. -/
def ideleClassEquivFixed
    (F : IntermediateField K (SeparableClosure K)) [FiniteDimensional K F] :
    Additive (NumberField.IdeleClassGroup (𝓞 F) F) ≃+
      KummerTheory.ambientFixedAddSubgroup (ideleClassRepresentation K)
        (RamificationTheory.closedFixingSubgroup K (SeparableClosure K) F) :=
  AddEquiv.ofBijective (intermediateIdeleClassToFixed K F)
    ⟨intermediateIdeleClassToFixed_injective K F,
      intermediateIdeleClassToFixed_surjective K F⟩

end GlobalClassFieldTheory.Reciprocity

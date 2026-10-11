/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.Kummer.SingleRadical
import Nyll.ValuedFieldTheory.LocalField.Unramified.RamificationIndexTower

/-!
# Ramification in towers of radical extensions

The ramification index is the cardinality of the actual
value-group quotient.  This file records its multiplicativity in a tower and
then applies the one-radical calculation successively.
-/

noncomputable section

universe u

namespace AlgebraicNumberTheory
namespace Valuations

open scoped IntermediateField

section ResidueTower

variable {K M L : Type u} [Field K] [Field M] [Field L]
variable [Algebra K M] [Algebra M L] [Algebra K L]
variable [IsScalarTower K M L]

/-- The residue-field map of a valued tower is the composite of the two
successive residue-field maps. -/
theorem tameResidueFieldMap_comp_in_tower
    (v : LubinTate.Valuations.ExponentialValuation K)
    (u : LubinTate.Valuations.ExponentialValuation M)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hKM : ∀ a : K, u (algebraMap K M a) = v a)
    (hML : ∀ a : M, w (algebraMap M L a) = u a)
    (hKL : ∀ a : K, w (algebraMap K L a) = v a) :
    tameResidueFieldMap v w hKL =
      (tameResidueFieldMap u w hML).comp
        (tameResidueFieldMap v u hKM) := by
  let iKM := unramifiedValuationRingValuationRingMap v u hKM
  let iML := unramifiedValuationRingValuationRingMap u w hML
  let iKL := unramifiedValuationRingValuationRingMap v w hKL
  let : IsLocalHom iKM :=
    unramifiedValuationRingValuationRingMap_isLocalHom v u hKM
  let : IsLocalHom iML :=
    unramifiedValuationRingValuationRingMap_isLocalHom u w hML
  let : IsLocalHom iKL :=
    unramifiedValuationRingValuationRingMap_isLocalHom v w hKL
  have hi : iKL = iML.comp iKM := by
    ext x
    exact IsScalarTower.algebraMap_apply K M L (x : K)
  change IsLocalRing.ResidueField.map iKL =
    (IsLocalRing.ResidueField.map iML).comp
      (IsLocalRing.ResidueField.map iKM)
  simpa only [hi] using
    (IsLocalRing.ResidueField.map_comp iKM iML)

/-- Surjectivity of the composite residue map implies surjectivity onto an
intermediate residue field. -/
theorem tameResidueFieldMap_surjective_left_of_comp
    (v : LubinTate.Valuations.ExponentialValuation K)
    (u : LubinTate.Valuations.ExponentialValuation M)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hKM : ∀ a : K, u (algebraMap K M a) = v a)
    (hML : ∀ a : M, w (algebraMap M L a) = u a)
    (hKL : ∀ a : K, w (algebraMap K L a) = v a)
    (hres : Function.Surjective (tameResidueFieldMap v w hKL)) :
    Function.Surjective (tameResidueFieldMap v u hKM) := by
  let fKM := tameResidueFieldMap v u hKM
  let fML := tameResidueFieldMap u w hML
  let fKL := tameResidueFieldMap v w hKL
  have hf : fKL = fML.comp fKM :=
    tameResidueFieldMap_comp_in_tower v u w hKM hML hKL
  intro y
  obtain ⟨x, hx⟩ := hres (fML y)
  refine ⟨x, ?_⟩
  apply fML.injective
  calc
    fML (fKM x) = (fML.comp fKM) x := rfl
    _ = fKL x := by rw [← hf]
    _ = fML y := hx

/-- Surjectivity of the composite residue map also implies surjectivity of
the second map in the tower. -/
theorem tameResidueFieldMap_surjective_right_of_comp
    (v : LubinTate.Valuations.ExponentialValuation K)
    (u : LubinTate.Valuations.ExponentialValuation M)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hKM : ∀ a : K, u (algebraMap K M a) = v a)
    (hML : ∀ a : M, w (algebraMap M L a) = u a)
    (hKL : ∀ a : K, w (algebraMap K L a) = v a)
    (hres : Function.Surjective (tameResidueFieldMap v w hKL)) :
    Function.Surjective (tameResidueFieldMap u w hML) := by
  let fKM := tameResidueFieldMap v u hKM
  let fML := tameResidueFieldMap u w hML
  let fKL := tameResidueFieldMap v w hKL
  have hf : fKL = fML.comp fKM :=
    tameResidueFieldMap_comp_in_tower v u w hKM hML hKL
  intro y
  obtain ⟨x, hx⟩ := hres y
  refine ⟨fKM x, ?_⟩
  calc
    fML (fKM x) = (fML.comp fKM) x := rfl
    _ = fKL x := by rw [← hf]
    _ = y := hx

/-- Finite-dimensionality transported from the quotient-induced residue
module to the module induced by the chosen residue-field map. -/
private theorem residueFiniteDimensional_for_tameResidueFieldMap
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E]
    (v : LubinTate.Valuations.ExponentialValuation F)
    (w : LubinTate.Valuations.ExponentialValuation E)
    (hExt : ∀ a : F, w (algebraMap F E a) = v a) :
    let V := LubinTate.Valuations.exponentialValuationSubring v
    let W := LubinTate.Valuations.exponentialValuationSubring w
    let k := IsLocalRing.ResidueField V
    let ell := IsLocalRing.ResidueField W
    let f : k →+* ell := tameResidueFieldMap v w hExt
    letI : Algebra k ell := f.toAlgebra
    FiniteDimensional k ell := by
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let i := unramifiedValuationRingValuationRingMap v w hExt
  let : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
  let k := IsLocalRing.ResidueField V
  let ell := IsLocalRing.ResidueField W
  let f : k →+* ell := tameResidueFieldMap v w hExt
  let : Algebra k ell := f.toAlgebra
  let algebraModule : Module k ell :=
    (inferInstance : Algebra k ell).toModule
  let : Algebra V W := i.toAlgebra
  let residueModule : Module k ell :=
    @IsLocalRing.ResidueField.instModule
      V W _ _ _ _ (i.toAlgebra) inferInstance
  have hfinite :
      @FiniteDimensional k ell _ _ residueModule :=
    residueExtension_finiteDimensional_of_finiteDimensional
      v w hExt
  have hmodule : residueModule = algebraModule := by
    apply Module.ext
    funext r x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
    rfl
  change @FiniteDimensional k ell _ _ algebraModule
  rw [← hmodule]
  exact hfinite

/-- The residue degree is the finrank for the algebra induced by the chosen
residue-field map. -/
private theorem exponentialResidueDegree_eq_finrank_tameResidueFieldMap
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (v : LubinTate.Valuations.ExponentialValuation F)
    (w : LubinTate.Valuations.ExponentialValuation E)
    (hExt : ∀ a : F, w (algebraMap F E a) = v a) :
    let V := LubinTate.Valuations.exponentialValuationSubring v
    let W := LubinTate.Valuations.exponentialValuationSubring w
    let k := IsLocalRing.ResidueField V
    let ell := IsLocalRing.ResidueField W
    let f : k →+* ell := tameResidueFieldMap v w hExt
    letI : Algebra k ell := f.toAlgebra
    exponentialResidueDegree v w hExt = Module.finrank k ell := by
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let k := IsLocalRing.ResidueField V
  let ell := IsLocalRing.ResidueField W
  let f : k →+* ell := tameResidueFieldMap v w hExt
  let : Algebra k ell := f.toAlgebra
  let algebraModule : Module k ell :=
    (inferInstance : Algebra k ell).toModule
  let i := exponentialValuationRingMap v w hExt
  let : IsLocalHom i :=
    exponentialValuationRingMap_isLocalHom v w hExt
  let : Algebra V W := i.toAlgebra
  let residueModule : Module k ell :=
    @IsLocalRing.ResidueField.instModule
      V W _ _ _ _ (i.toAlgebra) inferInstance
  have hmodule : residueModule = algebraModule := by
    apply Module.ext
    funext r x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
    rfl
  change @Module.finrank k ell _ _ residueModule =
    @Module.finrank k ell _ _ algebraModule
  rw [hmodule]

/-- The actual residue degree is multiplicative in a finite valued-field
tower. -/
theorem exponentialResidueDegree_mul_in_tower
    [FiniteDimensional K M] [FiniteDimensional M L]
    [FiniteDimensional K L]
    (v : LubinTate.Valuations.ExponentialValuation K)
    (u : LubinTate.Valuations.ExponentialValuation M)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hKM : ∀ a : K, u (algebraMap K M a) = v a)
    (hML : ∀ a : M, w (algebraMap M L a) = u a)
    (hKL : ∀ a : K, w (algebraMap K L a) = v a) :
    exponentialResidueDegree v u hKM * exponentialResidueDegree u w hML =
      exponentialResidueDegree v w hKL := by
  let k := IsLocalRing.ResidueField (LubinTate.Valuations.exponentialValuationSubring v)
  let m := IsLocalRing.ResidueField (LubinTate.Valuations.exponentialValuationSubring u)
  let ell := IsLocalRing.ResidueField (LubinTate.Valuations.exponentialValuationSubring w)
  let fKM := tameResidueFieldMap v u hKM
  let fML := tameResidueFieldMap u w hML
  let fKL := tameResidueFieldMap v w hKL
  let : Algebra k m := fKM.toAlgebra
  let : Algebra m ell := fML.toAlgebra
  let : Algebra k ell := fKL.toAlgebra
  let : IsScalarTower k m ell := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change fKL x = fML (fKM x)
    have hf := tameResidueFieldMap_comp_in_tower
      v u w hKM hML hKL
    exact DFunLike.congr_fun hf x
  let : FiniteDimensional k m :=
    residueFiniteDimensional_for_tameResidueFieldMap v u hKM
  let : FiniteDimensional m ell :=
    residueFiniteDimensional_for_tameResidueFieldMap u w hML
  let : FiniteDimensional k ell :=
    residueFiniteDimensional_for_tameResidueFieldMap v w hKL
  calc
    exponentialResidueDegree v u hKM * exponentialResidueDegree u w hML =
        Module.finrank k m * Module.finrank m ell := by
      rw [exponentialResidueDegree_eq_finrank_tameResidueFieldMap,
        exponentialResidueDegree_eq_finrank_tameResidueFieldMap]
    _ = Module.finrank k ell := Module.finrank_mul_finrank k m ell
    _ = exponentialResidueDegree v w hKL :=
      (exponentialResidueDegree_eq_finrank_tameResidueFieldMap v w hKL).symm

/-- A surjective actual residue-field map has residue degree one. -/
theorem exponentialResidueDegree_eq_one_of_surjective
    [FiniteDimensional K L]
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hres : Function.Surjective (tameResidueFieldMap v w hExt)) :
    exponentialResidueDegree v w hExt = 1 := by
  let k := IsLocalRing.ResidueField (LubinTate.Valuations.exponentialValuationSubring v)
  let ell := IsLocalRing.ResidueField (LubinTate.Valuations.exponentialValuationSubring w)
  let f := tameResidueFieldMap v w hExt
  let : Algebra k ell := f.toAlgebra
  let : FiniteDimensional k ell :=
    residueFiniteDimensional_for_tameResidueFieldMap v w hExt
  let e : k ≃ₗ[k] ell := LinearEquiv.ofBijective
    (Algebra.linearMap k ell) ⟨(algebraMap k ell).injective, hres⟩
  calc
    exponentialResidueDegree v w hExt = Module.finrank k ell :=
      exponentialResidueDegree_eq_finrank_tameResidueFieldMap v w hExt
    _ = 1 := by
      rw [← e.finrank_eq]
      exact Module.finrank_self k

end ResidueTower

section IntermediateResidue

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- If the residue map to the ambient field is onto, then so is the residue
map to every intermediate field. -/
theorem tameResidueFieldMap_surjective_to_intermediate
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hres : Function.Surjective (tameResidueFieldMap v w hExt))
    (E : IntermediateField K L) :
    Function.Surjective
      (tameResidueFieldMap v (exponentialValuationRestrict w E)
        (exponentialValuationRestrict_extends v w hExt E)) := by
  let wE := exponentialValuationRestrict w E
  let hKE : ∀ a : K, wE (algebraMap K E a) = v a :=
    exponentialValuationRestrict_extends v w hExt E
  let hEL : ∀ a : E, w (algebraMap E L a) = wE a := by
    intro a
    rfl
  exact tameResidueFieldMap_surjective_left_of_comp
    v wE w hKE hEL hExt hres

end IntermediateResidue

section RadicalTower

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L]

/-- Successively adjoining finitely many prime-to-`p` radicals over a
Henselian field, with no residue-field extension, gives a totally ramified
extension.  This is the degree calculation used in tame radical generation. -/
theorem exponentialRamificationIndex_eq_finrank_of_radical_family
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (hp : PositiveResidueCharacteristic v)
    (hres : Function.Surjective (tameResidueFieldMap v w hExt))
    (r : ℕ) (m : Fin r → ℕ) (a : Fin r → K) (α : Fin r → L)
    (hmpos : ∀ i, 0 < m i)
    (hmcop : ∀ i, Nat.Coprime (m i) (residueCharacteristic v))
    (hpow : ∀ i, α i ^ m i = algebraMap K L (a i))
    (hgen : IntermediateField.adjoin K (Set.range α) = ⊤) :
    exponentialRamificationIndex v w = Module.finrank K L := by
  classical
  let S : Finset L := Finset.univ.image α
  have hS : (↑S : Set L) = Set.range α := by
    ext x
    simp [S]
  let P : IntermediateField K L → Prop := fun E ↦
    exponentialRamificationIndex v (exponentialValuationRestrict w E) =
      Module.finrank K E
  have hbase : P ⊥ := by
    let w0 := exponentialValuationRestrict w
      (⊥ : IntermediateField K L)
    let h0 : ∀ x : K, w0 (algebraMap K (⊥ : IntermediateField K L) x) =
        v x := exponentialValuationRestrict_extends v w hExt ⊥
    obtain ⟨_hfinite, hUnram⟩ :=
      finiteUnramifiedSubextension_bot v w hExt hhens
    have he : exponentialRamificationIndex v w0 = 1 :=
      exponentialRamificationIndex_eq_one_of_finiteUnramifiedExtension
        v w0 h0 hUnram
    change exponentialRamificationIndex v w0 =
      Module.finrank K (⊥ : IntermediateField K L)
    simpa using he
  have hstep : ∀ (E : IntermediateField K L), ∀ x ∈ S,
      P E → P ((E⟮x⟯).restrictScalars K) := by
    intro E x hx hPE
    rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
    by_cases hα0 : α i = 0
    · simpa [hα0, P] using hPE
    · let F : IntermediateField E L := E⟮α i⟯
      let u := exponentialValuationRestrict w E
      let z := exponentialValuationRestrict w F
      let hKE : ∀ b : K, u (algebraMap K E b) = v b :=
        exponentialValuationRestrict_extends v w hExt E
      let hEF : ∀ b : E, z (algebraMap E F b) = u b := by
        intro b
        rfl
      let hKF : ∀ b : K, z (algebraMap K F b) = v b := by
        intro b
        change w (algebraMap K L b) = v b
        exact hExt b
      have hhensE : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
          (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring u).valuation :=
        henselianValuation_of_algebraic_extension v u hKE hhens
      have hcharE : residueCharacteristic v =
          residueCharacteristic u :=
        residueCharacteristic_eq_of_exact_extension v u hKE
      have hpE : PositiveResidueCharacteristic u := by
        change residueCharacteristic u ≠ 0
        rw [← hcharE]
        exact hp
      have hresKF : Function.Surjective (tameResidueFieldMap v z hKF) := by
        let ER : IntermediateField K L := F.restrictScalars K
        have hresER :=
          tameResidueFieldMap_surjective_to_intermediate
            v w hExt hres ER
        exact hresER
      have hresEF : Function.Surjective (tameResidueFieldMap u z hEF) :=
        tameResidueFieldMap_surjective_right_of_comp
          v u z hKE hEF hKF hresKF
      let alphaF : F := ⟨α i, IntermediateField.subset_adjoin E
        ({α i} : Set L) (Set.mem_singleton (α i))⟩
      have halphaF0 : alphaF ≠ 0 := by
        intro hzero
        apply hα0
        exact congrArg Subtype.val hzero
      have hgenF : IntermediateField.adjoin E
          ({alphaF} : Set F) = ⊤ := by
        apply (IntermediateField.lift_injective F)
        rw [IntermediateField.lift_adjoin_simple,
          IntermediateField.lift_top]
      have hpowF : alphaF ^ m i =
          algebraMap E F (algebraMap K E (a i)) := by
        apply Subtype.ext
        change α i ^ m i = algebraMap K L (a i)
        exact hpow i
      have hcopE : Nat.Coprime (m i)
          (residueCharacteristic u) := by
        rw [← hcharE]
        exact hmcop i
      have hEFdegree : exponentialRamificationIndex u z =
          Module.finrank E F :=
        exponentialRamificationIndex_eq_finrank_of_single_radical
          u z hEF hhensE hpE hresEF alphaF halphaF0 hgenF
          (m i) (hmpos i) hcopE (algebraMap K E (a i)) hpowF
      have htower : exponentialRamificationIndex v u *
          exponentialRamificationIndex u z = exponentialRamificationIndex v z :=
        exponentialRamificationIndex_mul_in_tower v u z hKE hEF
      change exponentialRamificationIndex v z = Module.finrank K F
      calc
        exponentialRamificationIndex v z =
            exponentialRamificationIndex v u * exponentialRamificationIndex u z :=
          htower.symm
        _ = Module.finrank K E * Module.finrank E F := by
          rw [hPE, hEFdegree]
        _ = Module.finrank K F := Module.finrank_mul_finrank K E F
  have hPS : P (IntermediateField.adjoin K (↑S : Set L)) :=
    IntermediateField.induction_on_adjoin_finset S P hbase hstep
  rw [hS, hgen] at hPS
  let wTop := exponentialValuationRestrict w
    (⊤ : IntermediateField K L)
  have hvalueTop : exponentialValueSubgroup wTop =
      exponentialValueSubgroup w := by
    ext s
    constructor
    · rintro ⟨x, hx0, hxValue⟩
      have hxL0 : (x : L) ≠ 0 := by
        intro hx
        exact hx0 (Subtype.ext hx)
      exact ⟨(x : L), hxL0, hxValue⟩
    · rintro ⟨x, hx0, hxValue⟩
      let xTop : (⊤ : IntermediateField K L) := ⟨x, Set.mem_univ x⟩
      have hxTop0 : xTop ≠ 0 := by
        intro hx
        exact hx0 (congrArg Subtype.val hx)
      exact ⟨xTop, hxTop0, hxValue⟩
  have heTop : exponentialRamificationIndex v wTop =
      exponentialRamificationIndex v w := by
    unfold exponentialRamificationIndex ExponentialValueGroupQuotient
    rw [hvalueTop]
  change exponentialRamificationIndex v wTop =
    Module.finrank K (⊤ : IntermediateField K L) at hPS
  rw [heTop] at hPS
  simpa using hPS

end RadicalTower

end Valuations
end AlgebraicNumberTheory

end

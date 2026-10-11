/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.Kummer.Tower
import Nyll.ValuedFieldTheory.LocalField.Unramified.ResidueLifting
import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.Book.FiniteTameDegree

/-!
# Converse radical criterion for finite tame extensions

The declarations here complete the production radical API: a finite family
of prime-to-residue-characteristic radicals over the maximal unramified
subextension gives a finite tame extension.
-/

noncomputable section

universe u

namespace AlgebraicNumberTheory.Valuations

open scoped IntermediateField

/-- Over the maximal unramified subextension, every separable residue root
in the ambient residue field descends to the base residue field. -/
theorem maximalUnramifiedSubextension_separableResidueRootLifts
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation) :
    let T := maximalUnramifiedSubextension v w hExt
    let wT := exponentialValuationRestrict w T
    let hTL : ∀ a : T, w (algebraMap T L a) = wT a := by
      intro a
      rfl
    SeparableResidueRootLifts wT w hTL := by
  classical
  let T := maximalUnramifiedSubextension v w hExt
  let wT := exponentialValuationRestrict w T
  let hKT := exponentialValuationRestrict_extends v w hExt T
  let hTL : ∀ a : T, w (algebraMap T L a) = wT a := by
    intro a
    rfl
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let VT := LubinTate.Valuations.exponentialValuationSubring wT
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let iKT := unramifiedValuationRingValuationRingMap v wT hKT
  let iKL := unramifiedValuationRingValuationRingMap v w hExt
  let : IsLocalHom iKT :=
    unramifiedValuationRingValuationRingMap_isLocalHom v wT hKT
  let : IsLocalHom iKL :=
    unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
  let k := IsLocalRing.ResidueField V
  let kT := IsLocalRing.ResidueField VT
  let ell := IsLocalRing.ResidueField W
  let : Algebra k kT := (IsLocalRing.ResidueField.map iKT).toAlgebra
  let : Algebra k ell := (IsLocalRing.ResidueField.map iKL).toAlgebra
  let g : kT →ₐ[k] ell := restrictedResidueAlgHomToAmbient v w hExt T
  let : Algebra kT ell := g.toAlgebra
  let : IsScalarTower k kT ell :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (g.commutes x).symm
  have hrange : g.fieldRange = separableClosure k ell := by
    simpa [g] using
      maximalUnramifiedSubextension_residue_fieldRange_eq_separableClosure
        v w hExt hhens
  let : Algebra.IsSeparable k kT := ⟨fun x ↦ by
    apply (isSeparable_map_iff g g.injective).mp
    apply mem_separableClosure_iff.mp
    rw [← hrange]
    exact ⟨x, rfl⟩⟩
  change ∀ (y : ell) (P : Polynomial kT), P.Separable →
    (P.map (tameResidueFieldMap wT w hTL)).eval y = 0 →
      ∃ c : kT, tameResidueFieldMap wT w hTL c = y
  intro y P hPsep hPy
  have hmap : tameResidueFieldMap wT w hTL = g.toRingHom := by rfl
  have halg : algebraMap kT ell = g.toRingHom := by rfl
  have hySepT : IsSeparable kT y := by
    apply hPsep.of_dvd (minpoly.dvd kT y ?_)
    rw [Polynomial.aeval_def]
    rw [← Polynomial.eval_map, halg, ← hmap]
    exact hPy
  have hySep : IsSeparable k y :=
    IsSeparable.of_algebra_isSeparable_of_isSeparable k hySepT
  have hyRange : y ∈ g.fieldRange := by
    rw [hrange]
    exact mem_separableClosure_iff.mpr hySep
  rcases hyRange with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  rw [hmap]
  exact hc

section ResidueRootTower

variable {K M L : Type u} [Field K] [Field M] [Field L]
variable [Algebra K M] [Algebra M L] [Algebra K L]
variable [IsScalarTower K M L]

/-- Descent of separable residue roots passes to the left part of a tower. -/
theorem separableResidueRootLifts_to_left_in_tower
    (v : LubinTate.Valuations.ExponentialValuation K)
    (u : LubinTate.Valuations.ExponentialValuation M)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hKM : ∀ a : K, u (algebraMap K M a) = v a)
    (hML : ∀ a : M, w (algebraMap M L a) = u a)
    (hKL : ∀ a : K, w (algebraMap K L a) = v a)
    (hlifts : SeparableResidueRootLifts v w hKL) :
    SeparableResidueRootLifts v u hKM := by
  let k := IsLocalRing.ResidueField (LubinTate.Valuations.exponentialValuationSubring v)
  let m := IsLocalRing.ResidueField (LubinTate.Valuations.exponentialValuationSubring u)
  let ell := IsLocalRing.ResidueField (LubinTate.Valuations.exponentialValuationSubring w)
  let fKM : k →+* m := tameResidueFieldMap v u hKM
  let fML : m →+* ell := tameResidueFieldMap u w hML
  let fKL : k →+* ell := tameResidueFieldMap v w hKL
  have hf : fKL = fML.comp fKM :=
    tameResidueFieldMap_comp_in_tower v u w hKM hML hKL
  change ∀ (y : m) (P : Polynomial k), P.Separable →
    (P.map fKM).eval y = 0 → ∃ c, fKM c = y
  intro y P hP hPy
  have hPyL : (P.map fKL).eval (fML y) = 0 := by
    have hmap : P.map fKL = (P.map fKM).map fML := by
      rw [hf, Polynomial.map_map]
    calc
      (P.map fKL).eval (fML y) =
          ((P.map fKM).map fML).eval (fML y) := by rw [hmap]
      _ = fML ((P.map fKM).eval y) :=
        Polynomial.eval_map_apply (p := P.map fKM) fML y
      _ = 0 := by rw [hPy, map_zero]
  obtain ⟨c, hc⟩ := hlifts (fML y) P hP hPyL
  refine ⟨c, ?_⟩
  apply fML.injective
  calc
    fML (fKM c) = (fML.comp fKM) c := rfl
    _ = fKL c := by rw [← hf]
    _ = fML y := hc

/-- If the lower residue map is onto, descent of separable residue roots
passes to the right part of the tower. -/
theorem separableResidueRootLifts_to_right_of_surjective_left
    (v : LubinTate.Valuations.ExponentialValuation K)
    (u : LubinTate.Valuations.ExponentialValuation M)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hKM : ∀ a : K, u (algebraMap K M a) = v a)
    (hML : ∀ a : M, w (algebraMap M L a) = u a)
    (hKL : ∀ a : K, w (algebraMap K L a) = v a)
    (hlifts : SeparableResidueRootLifts v w hKL)
    (hsurj : Function.Surjective (tameResidueFieldMap v u hKM)) :
    SeparableResidueRootLifts u w hML := by
  let k := IsLocalRing.ResidueField (LubinTate.Valuations.exponentialValuationSubring v)
  let m := IsLocalRing.ResidueField (LubinTate.Valuations.exponentialValuationSubring u)
  let ell := IsLocalRing.ResidueField (LubinTate.Valuations.exponentialValuationSubring w)
  let f : k →+* m := tameResidueFieldMap v u hKM
  let g : m →+* ell := tameResidueFieldMap u w hML
  let d : k →+* ell := tameResidueFieldMap v w hKL
  have hd : d = g.comp f :=
    tameResidueFieldMap_comp_in_tower v u w hKM hML hKL
  let e : k ≃+* m := RingEquiv.ofBijective f ⟨f.injective, hsurj⟩
  change ∀ (y : ell) (P : Polynomial m), P.Separable →
    (P.map g).eval y = 0 → ∃ c, g c = y
  intro y P hP hPy
  let Q : Polynomial k := P.map e.symm
  have hQsep : Q.Separable := hP.map
  have hQroot : (Q.map d).eval y = 0 := by
    have hpoly : Q.map d = P.map g := by
      ext n
      dsimp [Q]
      rw [Polynomial.coeff_map, Polynomial.coeff_map, Polynomial.coeff_map]
      rw [hd]
      change g (f (e.symm (P.coeff n))) = g (P.coeff n)
      change g (e (e.symm (P.coeff n))) = g (P.coeff n)
      rw [e.apply_symm_apply]
    rw [hpoly]
    exact hPy
  obtain ⟨c, hc⟩ := hlifts y Q hQsep hQroot
  refine ⟨f c, ?_⟩
  calc
    g (f c) = (g.comp f) c := rfl
    _ = d c := by rw [← hd]
    _ = y := hc

end ResidueRootTower

/-- A valued extension of field degree one has trivial value-group and
residue-field extensions. -/
theorem exponentialRamificationIndex_eq_one_and_residueFieldMap_surjective_of_finrank_eq_one
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hdegree : Module.finrank K L = 1) :
    exponentialRamificationIndex v w = 1 ∧
      Function.Surjective (tameResidueFieldMap v w hExt) := by
  have hfund := ramificationInvariants_fundamental_inequality v w hExt
  rw [hdegree] at hfund
  have hepos : 0 < exponentialRamificationIndex v w := by
    let : Finite (ExponentialValueGroupQuotient v w) :=
      exponentialValueGroupQuotient_finite_of_finiteDimensional v w hExt
    let : AddCommGroup (ExponentialValueGroupQuotient v w) := by
      unfold ExponentialValueGroupQuotient
      infer_instance
    unfold exponentialRamificationIndex
    exact Nat.card_pos
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
  have hfinite : @FiniteDimensional k ell _ _ residueModule :=
    residueExtension_finiteDimensional_of_finiteDimensional v w hExt
  have hmodule : residueModule = algebraModule := by
    apply Module.ext
    funext r x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
    rfl
  have hfiniteAlgebra : @FiniteDimensional k ell _ _ algebraModule := by
    rw [← hmodule]
    exact hfinite
  let : Module k ell := algebraModule
  let : FiniteDimensional k ell := hfiniteAlgebra
  have hdegreeFinrank :
      exponentialResidueDegree v w hExt = Module.finrank k ell := by
    let ib := exponentialValuationRingMap v w hExt
    let : IsLocalHom ib := exponentialValuationRingMap_isLocalHom v w hExt
    let : Algebra V W := ib.toAlgebra
    let residueModule : Module k ell :=
      @IsLocalRing.ResidueField.instModule
        V W _ _ _ _ (ib.toAlgebra) inferInstance
    have hResidueModule : residueModule = algebraModule := by
      apply Module.ext
      funext r x
      obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
      obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
      rfl
    change @Module.finrank k ell _ _ residueModule =
      @Module.finrank k ell _ _ algebraModule
    rw [hResidueModule]
  have hfpos : 0 < exponentialResidueDegree v w hExt := by
    rw [hdegreeFinrank]
    exact Module.finrank_pos
  have he : exponentialRamificationIndex v w = 1 := by
    apply Nat.le_antisymm
    · exact (Nat.le_mul_of_pos_right _ hfpos).trans hfund
    · exact hepos
  have hf : exponentialResidueDegree v w hExt = 1 := by
    apply Nat.le_antisymm
    · exact (Nat.le_mul_of_pos_left _ hepos).trans hfund
    · exact hfpos
  refine ⟨he, ?_⟩
  change Function.Surjective f
  intro y
  have hfinrank : Module.finrank k ell = 1 :=
    hdegreeFinrank.symm.trans hf
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero' (1 : ell) one_ne_zero).mp hfinrank y
  refine ⟨c, ?_⟩
  change algebraMap k ell c = y
  simpa [Algebra.smul_def] using hc

/-- A finite prime-to-characteristic radical family is totally ramified,
has unchanged residue field, and has degree prime to the residue
characteristic. -/
theorem radicalFamily_totalRamified_surjective_coprime_of_separableResidue
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (hp : PositiveResidueCharacteristic v)
    (hlifts : SeparableResidueRootLifts v w hExt)
    (r : ℕ) (m : Fin r → ℕ) (a : Fin r → K) (α : Fin r → L)
    (hmpos : ∀ i, 0 < m i)
    (hmcop : ∀ i, Nat.Coprime (m i) (residueCharacteristic v))
    (hpow : ∀ i, α i ^ m i = algebraMap K L (a i))
    (hgen : IntermediateField.adjoin K (Set.range α) = ⊤) :
    exponentialRamificationIndex v w = Module.finrank K L ∧
      Function.Surjective (tameResidueFieldMap v w hExt) ∧
        Nat.Coprime (Module.finrank K L) (residueCharacteristic v) := by
  classical
  let S : Finset L := Finset.univ.image α
  have hS : (↑S : Set L) = Set.range α := by
    ext x
    simp [S]
  let P : IntermediateField K L → Prop := fun E ↦
    let u := exponentialValuationRestrict w E
    let hKE := exponentialValuationRestrict_extends v w hExt E
    exponentialRamificationIndex v u = Module.finrank K E ∧
      Function.Surjective (tameResidueFieldMap v u hKE) ∧
        Nat.Coprime (Module.finrank K E) (residueCharacteristic v)
  have hbase : P ⊥ := by
    let w0 := exponentialValuationRestrict w (⊥ : IntermediateField K L)
    let h0 : ∀ x : K, w0 (algebraMap K (⊥ : IntermediateField K L) x) = v x :=
      exponentialValuationRestrict_extends v w hExt ⊥
    have hdegree0 : Module.finrank K (⊥ : IntermediateField K L) = 1 := by simp
    obtain ⟨he0, hres0⟩ :=
      exponentialRamificationIndex_eq_one_and_residueFieldMap_surjective_of_finrank_eq_one
        v w0 h0 hdegree0
    change exponentialRamificationIndex v w0 =
        Module.finrank K (⊥ : IntermediateField K L) ∧
      Function.Surjective (tameResidueFieldMap v w0 h0) ∧
        Nat.Coprime (Module.finrank K (⊥ : IntermediateField K L))
          (residueCharacteristic v)
    exact ⟨he0.trans hdegree0.symm, hres0, by simp⟩
  have hstep : ∀ (E : IntermediateField K L), ∀ x ∈ S,
      P E → P ((E⟮x⟯).restrictScalars K) := by
    intro E x hx hPE
    rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
    by_cases hα0 : α i = 0
    · simpa [hα0, P] using hPE
    · let F : IntermediateField E L := IntermediateField.adjoin E ({α i} : Set L)
      let u := exponentialValuationRestrict w E
      let z := exponentialValuationRestrict w F
      let hKE : ∀ b : K, u (algebraMap K E b) = v b :=
        exponentialValuationRestrict_extends v w hExt E
      let hEL : ∀ b : E, w (algebraMap E L b) = u b := by intro b; rfl
      let hEF : ∀ b : E, z (algebraMap E F b) = u b := by intro b; rfl
      let hFL : ∀ b : F, w (algebraMap F L b) = z b := by intro b; rfl
      let hKF : ∀ b : K, z (algebraMap K F b) = v b := by
        intro b
        change w (algebraMap K L b) = v b
        exact hExt b
      change exponentialRamificationIndex v u = Module.finrank K E ∧
          Function.Surjective (tameResidueFieldMap v u hKE) ∧
            Nat.Coprime (Module.finrank K E) (residueCharacteristic v) at hPE
      rcases hPE with ⟨heE, hresE, hcopE⟩
      have hhensE : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
          (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring u).valuation :=
        henselianValuation_of_algebraic_extension v u hKE hhens
      have hcharE : residueCharacteristic v = residueCharacteristic u :=
        residueCharacteristic_eq_of_exact_extension v u hKE
      have hpE : PositiveResidueCharacteristic u := by
        change residueCharacteristic u ≠ 0
        rw [← hcharE]
        exact hp
      have hliftsEL : SeparableResidueRootLifts u w hEL :=
        separableResidueRootLifts_to_right_of_surjective_left
          v u w hKE hEL hExt hlifts hresE
      have hliftsEF : SeparableResidueRootLifts u z hEF :=
        separableResidueRootLifts_to_left_in_tower u z w hEF hFL hEL hliftsEL
      let alphaF : F := ⟨α i, IntermediateField.subset_adjoin E
        ({α i} : Set L) (Set.mem_singleton (α i))⟩
      have halphaF0 : alphaF ≠ 0 := by
        intro hzero
        apply hα0
        exact congrArg Subtype.val hzero
      have hgenF : IntermediateField.adjoin E ({alphaF} : Set F) = ⊤ := by
        apply (IntermediateField.lift_injective F)
        rw [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top]
      have hpowF : alphaF ^ m i = algebraMap E F (algebraMap K E (a i)) := by
        apply Subtype.ext
        exact hpow i
      have hcopExponentE : Nat.Coprime (m i) (residueCharacteristic u) := by
        rw [← hcharE]
        exact hmcop i
      let : AddCommGroup (ExponentialValueGroupQuotient u z) := by
        unfold ExponentialValueGroupQuotient
        infer_instance
      have heEF : exponentialRamificationIndex u z = Module.finrank E F :=
        exponentialRamificationIndex_eq_finrank_of_single_radical_of_separableResidue
          u z hEF hhensE hpE hliftsEF alphaF halphaF0 hgenF
          (m i) (hmpos i) hcopExponentE (algebraMap K E (a i)) hpowF
      have hresEF : Function.Surjective (tameResidueFieldMap u z hEF) :=
        tameResidueFieldMap_surjective_of_single_radical_of_separableResidue
          u z hEF hhensE hpE hliftsEF alphaF halphaF0 hgenF
          (m i) (hmpos i) hcopExponentE (algebraMap K E (a i)) hpowF
      have hdegreeEF : Module.finrank E F =
          addOrderOf (exponentialValueCoset u z alphaF halphaF0) :=
        finrank_eq_addOrderOf_valueCoset_of_single_radical_of_separableResidue
          u z hEF hhensE hpE hliftsEF alphaF halphaF0 hgenF
          (m i) (hmpos i) hcopExponentE (algebraMap K E (a i)) hpowF
      have horderDvd : addOrderOf (exponentialValueCoset u z alphaF halphaF0) ∣ m i :=
        exponentialValueCoset_addOrderOf_dvd_exponent_of_pow_eq_base
          u z hEF alphaF halphaF0 (m i) (algebraMap K E (a i)) hpowF
      have hcopEF : Nat.Coprime (Module.finrank E F) (residueCharacteristic v) := by
        rw [hdegreeEF]
        exact Nat.Coprime.of_dvd_left horderDvd (hmcop i)
      have heTower : exponentialRamificationIndex v u *
          exponentialRamificationIndex u z = exponentialRamificationIndex v z :=
        exponentialRamificationIndex_mul_in_tower v u z hKE hEF
      have hresKF : Function.Surjective (tameResidueFieldMap v z hKF) := by
        rw [tameResidueFieldMap_comp_in_tower v u z hKE hEF hKF]
        exact hresEF.comp hresE
      change exponentialRamificationIndex v z = Module.finrank K F ∧
          Function.Surjective (tameResidueFieldMap v z hKF) ∧
            Nat.Coprime (Module.finrank K F) (residueCharacteristic v)
      refine ⟨?_, hresKF, ?_⟩
      · calc
          exponentialRamificationIndex v z = exponentialRamificationIndex v u *
              exponentialRamificationIndex u z := heTower.symm
          _ = Module.finrank K E * Module.finrank E F := by rw [heE, heEF]
          _ = Module.finrank K F := Module.finrank_mul_finrank K E F
      · rw [← Module.finrank_mul_finrank K E F]
        exact hcopE.mul_left hcopEF
  have hPS : P (IntermediateField.adjoin K (↑S : Set L)) :=
    IntermediateField.induction_on_adjoin_finset S P hbase hstep
  rw [hS, hgen] at hPS
  let Top : IntermediateField K L := ⊤
  let wTop := exponentialValuationRestrict w Top
  let hKTop : ∀ b : K, wTop (algebraMap K Top b) = v b :=
    exponentialValuationRestrict_extends v w hExt Top
  let hTopL : ∀ b : Top, w (algebraMap Top L b) = wTop b := by intro b; rfl
  change exponentialRamificationIndex v wTop = Module.finrank K Top ∧
      Function.Surjective (tameResidueFieldMap v wTop hKTop) ∧
        Nat.Coprime (Module.finrank K Top) (residueCharacteristic v) at hPS
  rcases hPS with ⟨heTop, hresTop, hcopTop⟩
  have hdegreeTopL : Module.finrank Top L = 1 := by simp [Top]
  obtain ⟨heTopL, hresTopL⟩ :=
    exponentialRamificationIndex_eq_one_and_residueFieldMap_surjective_of_finrank_eq_one
      wTop w hTopL hdegreeTopL
  have heTower : exponentialRamificationIndex v wTop *
      exponentialRamificationIndex wTop w = exponentialRamificationIndex v w :=
    exponentialRamificationIndex_mul_in_tower v wTop w hKTop hTopL
  have hresWhole : Function.Surjective (tameResidueFieldMap v w hExt) := by
    rw [tameResidueFieldMap_comp_in_tower v wTop w hKTop hTopL hExt]
    exact hresTopL.comp hresTop
  refine ⟨?_, hresWhole, ?_⟩
  · calc
      exponentialRamificationIndex v w = exponentialRamificationIndex v wTop *
          exponentialRamificationIndex wTop w := heTower.symm
      _ = Module.finrank K Top * 1 := by rw [heTop, heTopL]
      _ = Module.finrank K L := by simp [Top]
  · simpa [Top] using hcopTop

/-- Generation over the maximal unramified subextension by a finite
prime-to-characteristic radical family implies finite tame ramification. -/
theorem finiteTamelyRamifiedExtension_of_generatedOverMaximalUnramifiedByRadicals
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (hp : PositiveResidueCharacteristic v)
    (hrad : GeneratedOverMaximalUnramifiedByRadicals v w hExt) :
    FiniteTamelyRamifiedExtension v w hExt := by
  classical
  let T := maximalUnramifiedSubextension v w hExt
  let wT := exponentialValuationRestrict w T
  let hKT : ∀ b : K, wT (algebraMap K T b) = v b :=
    exponentialValuationRestrict_extends v w hExt T
  let hTL : ∀ b : T, w (algebraMap T L b) = wT b := by
    intro b
    rfl
  have hhensT : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring wT).valuation :=
    henselianValuation_of_algebraic_extension v wT hKT hhens
  have hcharT : residueCharacteristic v = residueCharacteristic wT :=
    residueCharacteristic_eq_of_exact_extension v wT hKT
  have hpT : PositiveResidueCharacteristic wT := by
    change residueCharacteristic wT ≠ 0
    rw [← hcharT]
    exact hp
  have hliftsTL : SeparableResidueRootLifts wT w hTL :=
    maximalUnramifiedSubextension_separableResidueRootLifts v w hExt hhens
  change GeneratedByRadicalsPrimeTo T (residueCharacteristic v) at hrad
  rcases hrad with ⟨r, m, a, alpha, hmpos, hmcop, hpow, hgen⟩
  have hmcopT : ∀ i, Nat.Coprime (m i) (residueCharacteristic wT) := by
    intro i
    rw [← hcharT]
    exact hmcop i
  obtain ⟨_heTL, hresTL, hcopTL⟩ :=
    radicalFamily_totalRamified_surjective_coprime_of_separableResidue
      wT w hTL hhensT hpT hliftsTL r m a alpha
      hmpos hmcopT hpow hgen
  have hTUnram : FiniteUnramifiedExtension v wT hKT :=
    maximalUnramifiedSubextension_finiteUnramified v w hExt hhens
  have hsep : ResidueExtensionIsSeparable v w hExt := by
    let k := IsLocalRing.ResidueField
      (LubinTate.Valuations.exponentialValuationSubring v)
    let kT := IsLocalRing.ResidueField
      (LubinTate.Valuations.exponentialValuationSubring wT)
    let ell := IsLocalRing.ResidueField
      (LubinTate.Valuations.exponentialValuationSubring w)
    let fKT : k →+* kT := tameResidueFieldMap v wT hKT
    let fTL : kT →+* ell := tameResidueFieldMap wT w hTL
    let fKL : k →+* ell := tameResidueFieldMap v w hExt
    let : Algebra k kT := fKT.toAlgebra
    let : Algebra kT ell := fTL.toAlgebra
    let : Algebra k ell := fKL.toAlgebra
    have hf : fKL = fTL.comp fKT :=
      tameResidueFieldMap_comp_in_tower v wT w hKT hTL hExt
    let : IsScalarTower k kT ell :=
      IsScalarTower.of_algebraMap_eq fun x ↦ by
        change fKL x = fTL (fKT x)
        exact DFunLike.congr_fun hf x
    have hsepKT : Algebra.IsSeparable k kT :=
      finiteUnramifiedExtension_residue_isSeparable v wT hKT hTUnram
    let eTL : kT ≃+* ell :=
      RingEquiv.ofBijective fTL ⟨fTL.injective, hresTL⟩
    have hsepTL : Algebra.IsSeparable kT ell := by
      let : Algebra.IsSeparable kT kT := inferInstance
      refine Algebra.IsSeparable.of_equiv_equiv (RingEquiv.refl kT) eTL ?_
      ext x
      rfl
    let : Algebra.IsSeparable k kT := hsepKT
    let : Algebra.IsSeparable kT ell := hsepTL
    change Algebra.IsSeparable k ell
    exact Algebra.IsSeparable.trans k kT ell
  refine ⟨hp, hsep, ?_⟩
  change Nat.Coprime (Module.finrank T L) (residueCharacteristic v)
  rw [hcharT]
  exact hcopTL

end AlgebraicNumberTheory.Valuations

end

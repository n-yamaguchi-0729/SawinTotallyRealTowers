/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.Kummer.TameRadicalGeneration
import Nyll.ValuedFieldTheory.LocalField.Unramified.BaseChange
import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.Book.RadicalConverse
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Compositum

/-!
# Finite tame base change for exponential valuations

This file constructs the maximal-unramified inclusion and transported
radical presentation used by finite tame base change.  All dependencies are
production CFT and SchemeTheory APIs.
-/

noncomputable section

universe u

namespace TameAbhyankar

open AlgebraicNumberTheory.Valuations
open DiscreteValuationField.FieldCompositum

/-- Finite unramifiedness is invariant under a valuation-preserving algebra
equivalence. -/
private theorem finiteUnramifiedExtension_algEquiv
    {K A B : Type*} [Field K] [Field A] [Field B]
    [Algebra K A] [Algebra K B] [FiniteDimensional K A]
    (e : A ≃ₐ[K] B)
    (v : LubinTate.Valuations.ExponentialValuation K)
    (wA : LubinTate.Valuations.ExponentialValuation A)
    (wB : LubinTate.Valuations.ExponentialValuation B)
    (hKA : ∀ a : K, wA (algebraMap K A a) = v a)
    (hKB : ∀ a : K, wB (algebraMap K B a) = v a)
    (he : ∀ x : A, wB (e x) = wA x)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (hA : FiniteUnramifiedExtension v wA hKA) :
    letI : FiniteDimensional K B := e.toLinearEquiv.finiteDimensional
    FiniteUnramifiedExtension v wB hKB := by
  classical
  let : FiniteDimensional K B := e.toLinearEquiv.finiteDimensional
  let V := LubinTate.Valuations.exponentialValuationSubring v
  obtain ⟨a, F, haGen, hFfield, _hFresidueMinpoly,
      hFreduction, _haSeparable⟩ :=
    exists_primitive_lift_minpoly_of_finiteUnramifiedExtension
      v wA hKA hhens hA
  let aB : LubinTate.Valuations.exponentialValuationSubring wB :=
    ⟨e (a : A), by
      change (0 : WithTop ℝ) ≤ wB (e (a : A))
      rw [he]
      exact a.property⟩
  have haGenBIF : IntermediateField.adjoin K ({(aB : B)} : Set B) = ⊤ := by
    rw [show (aB : B) = e (a : A) from rfl]
    rw [← Set.image_singleton]
    change IntermediateField.adjoin K
      (e.toAlgHom '' ({(a : A)} : Set A)) = ⊤
    rw [← IntermediateField.adjoin_map, haGen]
    ext x
    constructor
    · intro _hx
      trivial
    · intro _hx
      exact ⟨e.symm x, by simp, e.apply_symm_apply x⟩
  have haGenB : Algebra.adjoin K ({(aB : B)} : Set B) = ⊤ := by
    apply Algebra.adjoin_eq_top_of_intermediateField
      (fun x _hx ↦ Algebra.IsAlgebraic.isAlgebraic x)
    exact haGenBIF
  have hFmonic : F.Monic := by
    have hmappedMonic : (F.map V.subtype).Monic := by
      rw [hFfield]
      exact minpoly.monic (Algebra.IsIntegral.isIntegral (a : A))
    exact (V.subtype_injective.monic_map_iff (p := F)).2 hmappedMonic
  have hFrootA :
      (F.map ((algebraMap K A).comp V.subtype)).eval (a : A) = 0 := by
    have hmin : Polynomial.aeval (a : A) (minpoly K (a : A)) = 0 :=
      minpoly.aeval K (a : A)
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] at hmin
    have hpoly :
        F.map ((algebraMap K A).comp V.subtype) =
          (F.map V.subtype).map (algebraMap K A) := by
      rw [Polynomial.map_map]
    rw [hpoly, hFfield]
    exact hmin
  have hFmapB :
      F.map ((algebraMap K B).comp V.subtype) =
        (F.map ((algebraMap K A).comp V.subtype)).map
          e.toRingEquiv.toRingHom := by
    rw [Polynomial.map_map]
    apply Polynomial.ext
    intro n
    simp only [Polynomial.coeff_map, RingHom.coe_comp, Function.comp_apply]
    exact (e.commutes (F.coeff n : K)).symm
  have hFrootB :
      (F.map ((algebraMap K B).comp V.subtype)).eval (aB : B) = 0 := by
    rw [hFmapB]
    change ((F.map ((algebraMap K A).comp V.subtype)).map
      e.toRingEquiv.toRingHom).eval (e (a : A)) = 0
    calc
      _ = e ((F.map ((algebraMap K A).comp V.subtype)).eval (a : A)) :=
        Polynomial.eval_map_apply e.toRingEquiv.toRingHom (a : A)
      _ = e 0 := congrArg e hFrootA
      _ = 0 := map_zero e
  exact finiteUnramifiedExtension_of_primitive_separable_integral_model
    v wB hKB hhens aB F hFmonic hFrootB hFreduction haGenB

/-- An element of the lower maximal unramified subextension maps into the
upper maximal unramified subextension of the actual compositum. -/
theorem maximalUnramifiedSubextension_mem_commonTop_maximal
    {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω]
    (L K' : IntermediateField K Ω) [FiniteDimensional K L]
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation Ω)
    (hExt : ∀ a : K, w (algebraMap K Ω a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (x : maximalUnramifiedSubextension v
      (exponentialValuationRestrict w L)
      (exponentialValuationRestrict_extends v w hExt L)) :
    let Top := (L ⊔ K' : IntermediateField K Ω)
    let wRight := exponentialValuationRestrict w K'
    let wTop := exponentialValuationRestrict w Top
    let hRightTop : ∀ a : K', wTop (algebraMap K' Top a) = wRight a := by
      intro a
      rfl
    let xTop : Top :=
      IntermediateField.inclusion (show L ≤ Top from le_sup_left) (x : L)
    xTop ∈ maximalUnramifiedSubextension wRight wTop hRightTop := by
  classical
  let Top := (L ⊔ K' : IntermediateField K Ω)
  let wLeft := exponentialValuationRestrict w L
  let wRight := exponentialValuationRestrict w K'
  let wTop := exponentialValuationRestrict w Top
  let hLeft := exponentialValuationRestrict_extends v w hExt L
  let hBaseRight := exponentialValuationRestrict_extends v w hExt K'
  let hRightTop : ∀ a : K', wTop (algebraMap K' Top a) = wRight a := by
    intro a
    rfl
  let xTop : Top :=
    IntermediateField.inclusion (show L ≤ Top from le_sup_left) (x : L)
  let algRightTop : Algebra K' Top := inferInstance
  have hhensRight : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring wRight).valuation :=
    henselianValuation_of_algebraic_extension v wRight hBaseRight hhens
  obtain ⟨E, hxE, hE⟩ :=
    exists_finiteUnramifiedSubextension_of_mem_maximal
      v wLeft hLeft hhens x.property
  rcases hE with ⟨hfinE, hEunramified⟩
  let : FiniteDimensional K E := hfinE
  let EΩ : IntermediateField K Ω := E.map L.val
  let hfinEΩ : FiniteDimensional K EΩ :=
    finiteDimensional_map_val_of_finiteDimensional L E
  let : FiniteDimensional K EΩ := hfinEΩ
  let wE := exponentialValuationRestrict wLeft E
  let hKE := exponentialValuationRestrict_extends v wLeft hLeft E
  let wEΩ := exponentialValuationRestrict w EΩ
  let hKEΩ := exponentialValuationRestrict_extends v w hExt EΩ
  let eEΩ : E ≃ₐ[K] EΩ := IntermediateField.equivMap E L.val
  have heVal : ∀ y : E, wEΩ (eEΩ y) = wE y := by
    intro y
    rfl
  have hEΩunramified : FiniteUnramifiedExtension v wEΩ hKEΩ :=
    finiteUnramifiedExtension_algEquiv
      eEΩ v wE wEΩ hKE hKEΩ heVal hhens hEunramified
  let A : IntermediateField K Ω := EΩ ⊔ K'
  let wA := exponentialValuationRestrict w A
  let hRightA : ∀ a : K', wA (algebraMap K' A a) = wRight a := by
    intro a
    rfl
  let hfinA : FiniteDimensional K' A :=
    finiteDimensional_sup_over_right_of_left EΩ K'
  let : FiniteDimensional K' A := hfinA
  have hAunramified : FiniteUnramifiedExtension wRight wA hRightA :=
    finiteUnramifiedExtension_commonTop_of_baseChange
      EΩ K' v w hExt hhens hEΩunramified
  have hEΩleL : EΩ ≤ L := map_val_le_self L E
  have hAleTop : A ≤ Top :=
    sup_le (hEΩleL.trans le_sup_left) le_sup_right
  have hxEΩ : (x : Ω) ∈ EΩ := ⟨(x : L), hxE, rfl⟩
  have hxA : (x : Ω) ∈ A := (show EΩ ≤ A from le_sup_left) hxEΩ
  let : Algebra K' Ω := K'.val.toAlgebra
  let : Algebra K' Top := algRightTop
  let topValRight : Top →ₐ[K'] Ω :=
    { toRingHom := Top.val.toRingHom
      commutes' := by intro a; rfl }
  let ARight : IntermediateField K' Ω :=
    IntermediateField.extendScalars (show K' ≤ A from le_sup_right)
  let F : IntermediateField K' Top := ARight.comap topValRight
  let : Algebra K' F := F.toSubalgebra.algebra
  let : Module K' F := Algebra.toModule
  let eHom : F →ₐ[K'] A :=
    { toRingHom :=
        { toFun := fun z ↦ ⟨(((z : F) : Top) : Ω), z.property⟩
          map_one' := by apply Subtype.ext; rfl
          map_mul' := by intro y z; apply Subtype.ext; rfl
          map_zero' := by apply Subtype.ext; rfl
          map_add' := by intro y z; apply Subtype.ext; rfl }
      commutes' := by intro a; apply Subtype.ext; rfl }
  have heHomBijective : Function.Bijective eHom := by
    constructor
    · intro y z hyz
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun t : A ↦ (t : Ω)) hyz
    · intro y
      let yTop : Top := ⟨(y : Ω), hAleTop y.property⟩
      let yF : F := ⟨yTop, y.property⟩
      refine ⟨yF, ?_⟩
      apply Subtype.ext
      rfl
  let eFA : F ≃ₐ[K'] A := AlgEquiv.ofBijective eHom heHomBijective
  let hfinF : FiniteDimensional K' F := eFA.symm.toLinearEquiv.finiteDimensional
  let : FiniteDimensional K' F := hfinF
  let wF := exponentialValuationRestrict wTop F
  let hRightF : ∀ a : K', wF (algebraMap K' F a) = wRight a :=
    exponentialValuationRestrict_extends wRight wTop hRightTop F
  have heFAVal : ∀ y : A, wF (eFA.symm y) = wA y := by
    intro y
    change w ((((eFA.symm y : F) : Top) : Ω)) = w (y : Ω)
    apply congrArg w
    have heCoe (z : F) : ((eFA z : A) : Ω) = ((z : F) : Top) := by rfl
    calc
      (((eFA.symm y : F) : Top) : Ω) = ((eFA (eFA.symm y) : A) : Ω) :=
        (heCoe (eFA.symm y)).symm
      _ = (y : Ω) := congrArg (fun z : A ↦ (z : Ω)) (eFA.apply_symm_apply y)
  have hFunramified : FiniteUnramifiedExtension wRight wF hRightF :=
    finiteUnramifiedExtension_algEquiv
      eFA.symm wRight wA wF hRightA hRightF heFAVal hhensRight hAunramified
  have hFsub : FiniteUnramifiedSubextension wRight wTop hRightTop F :=
    ⟨hfinF, hFunramified⟩
  have hFle := finiteUnramifiedSubextension_le_maximal
    wRight wTop hRightTop hFsub
  apply hFle
  change ((xTop : Top) : Ω) ∈ A
  exact hxA

/-- The radical presentation of a finite tame extension survives finite base
change to the actual compositum. -/
theorem generatedOverMaximalUnramifiedByRadicals_commonTop_of_finiteTame
    {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω]
    (L K' : IntermediateField K Ω) [FiniteDimensional K L]
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation Ω)
    (hExt : ∀ a : K, w (algebraMap K Ω a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (hTame : FiniteTamelyRamifiedExtension v
      (exponentialValuationRestrict w L)
      (exponentialValuationRestrict_extends v w hExt L)) :
    let Top := (L ⊔ K' : IntermediateField K Ω)
    let wRight := exponentialValuationRestrict w K'
    let wTop := exponentialValuationRestrict w Top
    let hRightTop : ∀ a : K', wTop (algebraMap K' Top a) = wRight a := by
      intro a
      rfl
    letI : FiniteDimensional K' Top :=
      finiteDimensional_sup_over_right_of_left L K'
    GeneratedOverMaximalUnramifiedByRadicals wRight wTop hRightTop := by
  classical
  let Top := (L ⊔ K' : IntermediateField K Ω)
  let wLeft := exponentialValuationRestrict w L
  let wRight := exponentialValuationRestrict w K'
  let wTop := exponentialValuationRestrict w Top
  let hLeft := exponentialValuationRestrict_extends v w hExt L
  let hBaseRight := exponentialValuationRestrict_extends v w hExt K'
  let hRightTop : ∀ a : K', wTop (algebraMap K' Top a) = wRight a := by
    intro a
    rfl
  let : FiniteDimensional K' Top :=
    finiteDimensional_sup_over_right_of_left L K'
  let T := maximalUnramifiedSubextension v wLeft hLeft
  let TTop := maximalUnramifiedSubextension wRight wTop hRightTop
  let iL : L →ₐ[K] Top :=
    IntermediateField.inclusion (show L ≤ Top from le_sup_left)
  have hrad : GeneratedOverMaximalUnramifiedByRadicals v wLeft hLeft :=
    generatedOverMaximalUnramifiedByRadicals_of_finiteTame
      v wLeft hLeft hhens hTame
  change GeneratedByRadicalsPrimeTo T (residueCharacteristic v) at hrad
  rcases hrad with ⟨r, m, a, alpha, hmpos, hmcop, hpow, hgen⟩
  have haTopMem (i : Fin r) : iL (a i : L) ∈ TTop :=
    maximalUnramifiedSubextension_mem_commonTop_maximal
      L K' v w hExt hhens (a i)
  let aTop : Fin r → TTop := fun i ↦ ⟨iL (a i : L), haTopMem i⟩
  let alphaTop : Fin r → Top := fun i ↦ iL (alpha i)
  have hchar : residueCharacteristic v = residueCharacteristic wRight :=
    residueCharacteristic_eq_of_exact_extension v wRight hBaseRight
  have hpowTop (i : Fin r) :
      alphaTop i ^ m i = algebraMap TTop Top (aTop i) := by
    change iL (alpha i) ^ m i = algebraMap TTop Top (aTop i)
    rw [← map_pow, hpow i]
    rfl
  have hgenAlg : Algebra.adjoin T (Set.range alpha) =
      (⊤ : Subalgebra T L) := by
    let : FiniteDimensional T L := inferInstance
    let : Algebra.IsAlgebraic T L := Algebra.IsAlgebraic.of_finite T L
    exact Algebra.adjoin_eq_top_of_intermediateField
      (fun x _hx ↦ Algebra.IsAlgebraic.isAlgebraic x) hgen
  let S : Subalgebra TTop Top := Algebra.adjoin TTop (Set.range alphaTop)
  have hS : S = ⊤ := by
    apply Algebra.eq_top_iff.2
    intro z
    have hz : z ∈ Algebra.adjoin K' (Set.range iL) := by
      rw [sup_right_adjoin_left_range_eq_top (K := K) (Ω := Ω) L K']
      trivial
    exact Algebra.adjoin_induction
      (R := K') (A := Top) (s := Set.range iL)
      (p := fun y _hy ↦ y ∈ S)
      (fun y hy ↦ by
        rcases hy with ⟨x, rfl⟩
        have hx : x ∈ Algebra.adjoin T (Set.range alpha) := by
          rw [hgenAlg]
          trivial
        exact Algebra.adjoin_induction
          (R := T) (A := L) (s := Set.range alpha)
          (p := fun y _hy ↦ iL y ∈ S)
          (fun y hy ↦ by
            rcases hy with ⟨i, rfl⟩
            exact Algebra.subset_adjoin ⟨i, rfl⟩)
          (fun t ↦ by
            let tTop : TTop :=
              ⟨iL (t : L),
                maximalUnramifiedSubextension_mem_commonTop_maximal
                  L K' v w hExt hhens t⟩
            have ht : iL (algebraMap T L t) = algebraMap TTop Top tTop := by rfl
            change iL (algebraMap T L t) ∈ S
            rw [ht]
            exact S.algebraMap_mem tTop)
          (fun y₁ y₂ _ _ hy₁ hy₂ ↦ by simpa [map_add] using S.add_mem hy₁ hy₂)
          (fun y₁ y₂ _ _ hy₁ hy₂ ↦ by simpa [map_mul] using S.mul_mem hy₁ hy₂)
          hx)
      (fun b ↦ by
        let bTop : TTop := algebraMap K' TTop b
        have hb : algebraMap K' Top b = algebraMap TTop Top bTop :=
          (IsScalarTower.algebraMap_apply K' TTop Top b).symm
        change algebraMap K' Top b ∈ S
        rw [hb]
        exact S.algebraMap_mem bTop)
      (fun y₁ y₂ _ _ hy₁ hy₂ ↦ S.add_mem hy₁ hy₂)
      (fun y₁ y₂ _ _ hy₁ hy₂ ↦ S.mul_mem hy₁ hy₂)
      hz
  have hgenTop : IntermediateField.adjoin TTop (Set.range alphaTop) =
      (⊤ : IntermediateField TTop Top) := by
    let : FiniteDimensional TTop Top := inferInstance
    let : Algebra.IsAlgebraic TTop Top := Algebra.IsAlgebraic.of_finite TTop Top
    exact (IntermediateField.adjoin_eq_top_iff).2 hS
  change GeneratedByRadicalsPrimeTo TTop (residueCharacteristic wRight)
  refine ⟨r, m, aTop, alphaTop, hmpos, ?_, hpowTop, hgenTop⟩
  intro i
  rw [← hchar]
  exact hmcop i

/-- A finite tame exponential-valued extension remains finite tame after
finite base change to the actual compositum. -/
theorem finiteTamelyRamifiedExtension_commonTop_of_baseChange
    {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω]
    (L K' : IntermediateField K Ω) [FiniteDimensional K L]
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation Ω)
    (hExt : ∀ a : K, w (algebraMap K Ω a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (hTame : FiniteTamelyRamifiedExtension v
      (exponentialValuationRestrict w L)
      (exponentialValuationRestrict_extends v w hExt L)) :
    let Top := (L ⊔ K' : IntermediateField K Ω)
    let wRight := exponentialValuationRestrict w K'
    let wTop := exponentialValuationRestrict w Top
    let hRightTop : ∀ a : K', wTop (algebraMap K' Top a) = wRight a := by
      intro a
      rfl
    letI : FiniteDimensional K' Top :=
      finiteDimensional_sup_over_right_of_left L K'
    FiniteTamelyRamifiedExtension wRight wTop hRightTop := by
  let Top := (L ⊔ K' : IntermediateField K Ω)
  let wRight := exponentialValuationRestrict w K'
  let wTop := exponentialValuationRestrict w Top
  let hBaseRight := exponentialValuationRestrict_extends v w hExt K'
  let hRightTop : ∀ a : K', wTop (algebraMap K' Top a) = wRight a := by
    intro a
    rfl
  let : FiniteDimensional K' Top :=
    finiteDimensional_sup_over_right_of_left L K'
  have hhensRight : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring wRight).valuation :=
    henselianValuation_of_algebraic_extension v wRight hBaseRight hhens
  have hchar : residueCharacteristic v = residueCharacteristic wRight :=
    residueCharacteristic_eq_of_exact_extension v wRight hBaseRight
  have hpRight : PositiveResidueCharacteristic wRight := by
    change residueCharacteristic wRight ≠ 0
    rw [← hchar]
    exact hTame.1
  have hrad : GeneratedOverMaximalUnramifiedByRadicals wRight wTop hRightTop :=
    generatedOverMaximalUnramifiedByRadicals_commonTop_of_finiteTame
      L K' v w hExt hhens hTame
  exact finiteTamelyRamifiedExtension_of_generatedOverMaximalUnramifiedByRadicals
    wRight wTop hRightTop hhensRight hpRight hrad

end TameAbhyankar

end

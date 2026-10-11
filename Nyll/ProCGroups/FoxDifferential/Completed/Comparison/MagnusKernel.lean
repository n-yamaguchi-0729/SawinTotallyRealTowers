/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Discrete.KernelBoundary.MagnusComparison
import Nyll.ProCGroups.FoxDifferential.Discrete.KernelBoundary.Quotient
import Nyll.ProCGroups.FoxDifferential.Discrete.FoxCalculus.Boundary
import Nyll.ProCGroups.FoxDifferential.Completed.Comparison.DiscreteCompletion
import Mathlib.Basic.Finite.Defs

/-!
# Fox Differential / Completed / Comparison / Magnus Kernel

This module transfers discrete Magnus-kernel criteria through finite algebraic stages and
completed Fox differential coordinates.
-/

namespace CrowellExactSequence

noncomputable section

open FoxDifferential

variable {X : Type} {H : Type}
variable [Group H] [Finite X]

local instance : Fintype X := Fintype.ofFinite X
local instance : DecidableEq X := Classical.decEq X

/--
The finite-stage Magnus reverse inclusion in residue-universal form. For the finite quotient
\(F/N\), vanishing of the residue universal Fox differential modulo \(n\) forces a kernel word
into \([N,N]N^n\).
-/
theorem mem_foxCommutatorPowerSubgroup_of_residueUniversalDifferential_eq_zero
    (N : Subgroup (FreeGroup X)) [N.Normal] {n : ℕ} (hn : 0 < n)
    {w : FreeGroup X} (hwN : w ∈ N)
    (hres :
      FoxDifferential.residueUniversalDifferential n (QuotientGroup.mk' N) w = 0) :
    w ∈ FoxDifferential.foxCommutatorPowerSubgroup
      (F := FreeGroup X) N n := by
  let Hq := FoxDifferential.foxAlgebraicStageTargetQuotient (X := X) N
  let ψ : FreeGroup X →* Hq := QuotientGroup.mk' N
  have hψ : Function.Surjective ψ := by
    intro q
    rcases QuotientGroup.mk'_surjective N q with ⟨g, hg⟩
    exact ⟨g, hg⟩
  obtain ⟨y, hy⟩ :=
    FoxDifferential.exists_eq_nsmul_relFreeFoxDeriv_of_residueUnivDiff_eq_zero
      (X := X) N w hres
  have hder :
      FoxDifferential.FoxCalculus.relativeFreeGroupFoxDerivative (H := Hq) X ψ w = n • y :=
    by simpa [Hq, ψ] using hy
  have hwker : w ∈ ψ.ker := by
    change ψ w = 1
    exact (QuotientGroup.eq_one_iff (N := N) w).2 hwN
  have hboundary_derivative :
      FoxDifferential.FoxCalculus.relativeFreeGroupFoxBoundary (H := Hq) X ψ
          (FoxDifferential.FoxCalculus.relativeFreeGroupFoxDerivative (H := Hq) X ψ w) = 0 := by
    have hfund :=
      FoxDifferential.FoxCalculus.relativeFreeGroupFoxDerivative_fundamental_formula
        (H := Hq) X ψ w
    have hgb : groupRingBoundary ψ w = 0 :=
      groupRingBoundary_eq_zero_of_mem_ker (ψ := ψ) hwker
    rw [hgb] at hfund
    simpa [FoxDifferential.FoxCalculus.relativeFreeGroupFoxBoundary] using hfund.symm
  have hboundary_map_nsmul_all :
      ∀ m : ℕ,
        FoxDifferential.FoxCalculus.relativeFreeGroupFoxBoundary (H := Hq) X ψ (m • y) =
          m • FoxDifferential.FoxCalculus.relativeFreeGroupFoxBoundary (H := Hq) X ψ y := by
    intro m
    induction m with
    | zero =>
        simp only [zero_nsmul, map_zero]
    | succ m ih =>
        rw [succ_nsmul, map_add, ih, succ_nsmul]
  have hboundary_map_nsmul := hboundary_map_nsmul_all n
  have hboundary_nsmul :
      n • FoxDifferential.FoxCalculus.relativeFreeGroupFoxBoundary (H := Hq) X ψ y = 0 := by
    calc
      n • FoxDifferential.FoxCalculus.relativeFreeGroupFoxBoundary (H := Hq) X ψ y =
          FoxDifferential.FoxCalculus.relativeFreeGroupFoxBoundary (H := Hq) X ψ (n • y) := by
            exact hboundary_map_nsmul.symm
      _ = FoxDifferential.FoxCalculus.relativeFreeGroupFoxBoundary (H := Hq) X ψ
            (FoxDifferential.FoxCalculus.relativeFreeGroupFoxDerivative (H := Hq) X ψ w) := by
            rw [← hder]
      _ = 0 := hboundary_derivative
  have hboundary_y :
      FoxDifferential.FoxCalculus.relativeFreeGroupFoxBoundary (H := Hq) X ψ y = 0 :=
    FoxDifferential.groupRing_eq_zero_of_nsmul_eq_zero hn
      (FoxDifferential.FoxCalculus.relativeFreeGroupFoxBoundary (H := Hq) X ψ y)
      hboundary_nsmul
  let Y : DifferentialModule ψ :=
    FoxDifferential.FoxCalculus.relativeFreeFoxCoordinatesLinearMap (H := Hq) X ψ y
  have hYker : toGroupRing ψ Y = 0 := by
    have hcomp :=
      LinearMap.congr_fun
        (FoxDifferential.FoxCalculus.toGroupRing_comp_relativeFreeFoxCoordinatesLinearMap
          (H := Hq) X ψ) y
    change
      toGroupRing ψ
          (FoxDifferential.FoxCalculus.relativeFreeFoxCoordinatesLinearMap
            (H := Hq) X ψ y) =
        FoxDifferential.FoxCalculus.relativeFreeGroupFoxBoundary (H := Hq) X ψ y at hcomp
    change
      toGroupRing ψ
        (FoxDifferential.FoxCalculus.relativeFreeFoxCoordinatesLinearMap
          (H := Hq) X ψ y) = 0
    exact hcomp.trans hboundary_y
  let := kernelAbelianizationModuleOfSurjective ψ hψ
  obtain ⟨a, ha⟩ :=
    (exact_kernelAbelianizationBoundaryLinearOfSurjective_toGroupRing
      (H := Hq) ψ hψ Y).1 hYker
  have htoDiff_map_nsmul_all :
      ∀ m : ℕ,
        FoxDifferential.FoxCalculus.relativeFreeFoxCoordinatesLinearMap (H := Hq) X ψ (m • y) =
          m • FoxDifferential.FoxCalculus.relativeFreeFoxCoordinatesLinearMap (H := Hq) X ψ y := by
    intro m
    induction m with
    | zero =>
        simp only [zero_nsmul, map_zero]
    | succ m ih =>
        rw [succ_nsmul, map_add, ih, succ_nsmul]
  have htoDiff_map_nsmul := htoDiff_map_nsmul_all n
  have hd_nY : universalDifferential ψ w = n • Y := by
    calc
      universalDifferential ψ w =
          FoxDifferential.FoxCalculus.relativeFreeFoxCoordinatesLinearMap (H := Hq) X ψ
            (FoxDifferential.FoxCalculus.relativeFreeGroupFoxDerivative (H := Hq) X ψ w) := by
            exact
              (FoxDifferential.FoxCalculus.relativeFreeFoxCoordinatesLinearMap_derivative
                (H := Hq) X ψ w).symm
      _ = FoxDifferential.FoxCalculus.relativeFreeFoxCoordinatesLinearMap (H := Hq) X ψ
            (n • y) := by
            rw [hder]
      _ = n • Y := by
            simpa [Y] using htoDiff_map_nsmul
  let nw : ψ.ker := ⟨w, hwker⟩
  have hboundary_class :
      kernelAbelianizationBoundaryLinearOfSurjective ψ hψ
          (Additive.ofMul (Abelianization.of nw)) =
        n • kernelAbelianizationBoundaryLinearOfSurjective ψ hψ a := by
    calc
      kernelAbelianizationBoundaryLinearOfSurjective ψ hψ
          (Additive.ofMul (Abelianization.of nw)) =
          universalDifferential ψ w := by
            rw [kernelAbelianizationBoundaryLinearOfSurjective_of]
      _ = n • Y := hd_nY
      _ = n • kernelAbelianizationBoundaryLinearOfSurjective ψ hψ a := by
            simp only [ha]
  have hclassAdd :
      (Additive.ofMul (Abelianization.of nw) : KernelAbelianizationAdd ψ) = n • a := by
    apply kernelAbelianizationBoundaryLinearOfSurjective_injective
      (H := Hq) (ψ := ψ) hψ
    simpa using hboundary_class
  obtain ⟨a0, ha0⟩ := QuotientGroup.mk_surjective (Additive.toMul a)
  have ha0' : Abelianization.of a0 = Additive.toMul a := by
    change QuotientGroup.mk a0 = Additive.toMul a
    exact ha0
  have hclassMul :
      Abelianization.of nw = (Abelianization.of a0) ^ n := by
    have hmul := congrArg Additive.toMul hclassAdd
    simpa [ha0'] using hmul
  have hmemKer :
      w ∈ FoxDifferential.foxCommutatorPowerSubgroup
        (F := FreeGroup X) ψ.ker n :=
    FoxDifferential.mem_foxCommutatorPowerSubgroup_of_abelianization_eq_pow
      (F := FreeGroup X) ψ.ker n hwker a0 hclassMul
  have hker_eq : ψ.ker = N := by
    ext g
    change ψ g = 1 ↔ g ∈ N
    exact QuotientGroup.eq_one_iff (N := N) g
  simpa [hker_eq]
    using hmemKer

/--
General finite-class discrete Magnus conclusion for a surjective finite target map, with the
FoxDifferential finite-stage input supplied by the residue universal reverse inclusion.
-/
theorem mem_commutator_ker_of_zcUniversalDifferential_eq_zero_of_surjective
    {C : ProCGroups.FiniteGroupClass}
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    [TopologicalSpace H] [IsTopologicalGroup H] [DiscreteTopology H]
    (hCH : C H)
    {Q : Type} [Group Q]
    (α : FreeGroup X →* Q) (hα : Function.Surjective α)
    (β : Q →* H) (hβ : Function.Surjective β)
    (hCker : C β.ker)
    {w : FreeGroup X}
    (hwker : w ∈ (β.comp α).ker)
    (hzero :
      FoxDifferential.zcUniversalDifferential C (β.comp α) w = 0) :
    (⟨α w, by
      change β (α w) = 1
      simpa [MonoidHom.mem_ker, MonoidHom.comp_apply] using hwker⟩ : β.ker) ∈
      commutator β.ker := by
  exact
    FoxDifferential.mem_commutator_ker_of_zcUnivDiff_eq_zero_of_finite_magnus_surj
      (C := C) (hC := hC) (X := X) (hForm := hForm) (hCH := hCH)
      (α := α) (hα := hα) (β := β) (hβ := hβ) (hCker := hCker)
      (fun j _ w hw hres =>
        mem_foxCommutatorPowerSubgroup_of_residueUniversalDifferential_eq_zero
          (X := X) (β.comp α).ker j.positive hw hres)
      hwker hzero

/--
Finite-stage Magnus conclusion formulated with the finite Fox derivative vector. This is the
form used after a continuous pro-\(C\) derivative is projected to one finite coefficient/target
stage: the residue-universal reverse inclusion supplies the finite-stage Magnus input.
-/
theorem mem_commutator_ker_of_foxAlgebraicStageDerivativeVector_eq_zero
    {Q H : Type} [Group Q] [Group H]
    (α : FreeGroup X →* Q) (β : Q →* H) (n : ℕ) (hn : 0 < n)
    (hpow : ∀ k : β.ker, k ^ n = 1)
    {w : FreeGroup X}
    (hwker : w ∈ (β.comp α).ker)
    (hder :
      FoxDifferential.foxAlgebraicStageDerivativeVector
        (X := X) (β.comp α).ker n w = 0) :
    (⟨α w, by
      change β (α w) = 1
      simpa [MonoidHom.mem_ker, MonoidHom.comp_apply] using hwker⟩ : β.ker) ∈
      commutator β.ker := by
  have hres :
      FoxDifferential.residueUniversalDifferential n
          (QuotientGroup.mk' (β.comp α).ker) w = 0 :=
    (foxAlgebraicStageDerivativeVector_eq_zero_iff_residueUniversalDifferential_eq_zero
      (X := X) (N := (β.comp α).ker) (n := n) (w := w)).1 hder
  exact
    FoxDifferential.mem_commutator_ker_of_residueUniversalDifferential_eq_zero_of_kernel_le
      (X := X) α β n hpow
      (fun w hw hres =>
        mem_foxCommutatorPowerSubgroup_of_residueUniversalDifferential_eq_zero
          (X := X) (β.comp α).ker hn hw hres)
      hwker hres


universe u

/--
Universe-polymorphic finite-stage Magnus conclusion for finite source and target stages. This
is only a transport of the Type 0 discrete Magnus theorem above: finite groups are lowered to
an equivalent small model, and the finite-stage Fox derivative is reindexed along the
free-basis equivalence.
-/
theorem mem_commutator_ker_of_finiteFoxStageDerivativeVector_eq_zero_finite
    {X : Type u} [Finite X] [DecidableEq X]
    {Q H : Type u} [Group Q] [Group H] [Finite Q] [Finite H]
    (α : FreeGroup X →* Q) (β : Q →* H) (n : ℕ) (hn : 0 < n)
    (hpow : ∀ k : β.ker, k ^ n = 1)
    {w : FreeGroup X}
    (hwker : w ∈ (β.comp α).ker)
    (hder :
      FoxDifferential.foxAlgebraicStageDerivativeVector
        (X := X) (β.comp α).ker n w = 0) :
    (⟨α w, by
      change β (α w) = 1
      simpa [MonoidHom.mem_ker, MonoidHom.comp_apply] using hwker⟩ : β.ker) ∈
      commutator β.ker := by
  classical
  rcases Finite.exists_equiv_fin X with ⟨m, ⟨eX⟩⟩
  let : DecidableEq (Fin m) := Classical.decEq (Fin m)
  rcases Finite.exists_type_univ_nonempty_mulEquiv.{u, 0} Q with
    ⟨Q0, instQ0Group, _instQ0Fintype, ⟨eQ⟩⟩
  rcases Finite.exists_type_univ_nonempty_mulEquiv.{u, 0} H with
    ⟨H0, instH0Group, _instH0Fintype, ⟨eH⟩⟩
  let : Group Q0 := instQ0Group
  let : Group H0 := instH0Group
  let phi : FreeGroup X ≃* FreeGroup (Fin m) := FreeGroup.freeGroupCongr eX
  let α0 : FreeGroup (Fin m) →* Q0 :=
    eQ.toMonoidHom.comp (α.comp phi.symm.toMonoidHom)
  let β0 : Q0 →* H0 :=
    eH.toMonoidHom.comp (β.comp eQ.symm.toMonoidHom)
  let w0 : FreeGroup (Fin m) := phi w
  let M0 : Subgroup (FreeGroup (Fin m)) :=
    (β0.comp α0).ker
  have : M0.Normal := by
    dsimp [M0]
    infer_instance
  have hM0 : (β.comp α).ker.map phi.toMonoidHom = M0 := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      change β0 (α0 (phi x)) = 1
      change β (α x) = 1 at hx
      have hphi : phi.symm (phi x) = x := phi.symm_apply_apply x
      simpa [β0, α0, M0, hphi] using congrArg eH hx
    · intro hz
      refine ⟨phi.symm z, ?_, ?_⟩
      · change β (α (phi.symm z)) = 1
        have hz' : eH (β (α (phi.symm z))) = 1 := by
          simpa [β0, α0, M0] using hz
        exact eH.injective (by simpa using hz')
      · exact phi.apply_symm_apply z
  have hwker0 : w0 ∈ (β0.comp α0).ker := by
    change β0 (α0 w0) = 1
    change β (α w) = 1 at hwker
    have hphi : phi.symm (phi w) = w := phi.symm_apply_apply w
    simpa [β0, α0, w0, hphi] using congrArg eH hwker
  have hderM0 :
      FoxDifferential.foxAlgebraicStageDerivativeVector
        (X := Fin m) M0 n w0 = 0 := by
    simpa [M0, w0, phi] using
      FoxDifferential.foxAlgebraicStageDerivativeVector_eq_zero_reindex
        (X := X) (Y := Fin m) eX (β.comp α).ker M0 hM0 n hder
  have hder0 :
      FoxDifferential.foxAlgebraicStageDerivativeVector
        (X := Fin m) (β0.comp α0).ker n w0 = 0 := by
    simpa [M0] using hderM0
  have hpow0 : ∀ k : β0.ker, k ^ n = 1 := by
    intro k
    have hkβ : β (eQ.symm k.1) = 1 := by
      have hk0 : β0 k.1 = 1 := by
        exact k.2
      have hk : eH (β (eQ.symm k.1)) = 1 := by
        simpa [β0] using hk0
      exact eH.injective (by simpa using hk)
    have hkpow := hpow ⟨eQ.symm k.1, hkβ⟩
    have hkpow' : (eQ.symm k.1) ^ n = 1 :=
      congrArg Subtype.val hkpow
    have := congrArg eQ hkpow'
    apply Subtype.ext
    simpa using this
  let q0 : β0.ker :=
    ⟨α0 w0, by
      change β0 (α0 w0) = 1
      simpa [MonoidHom.mem_ker] using hwker0⟩
  have hcomm0 : q0 ∈ commutator β0.ker := by
    simpa [q0] using
      mem_commutator_ker_of_foxAlgebraicStageDerivativeVector_eq_zero
        (X := Fin m) α0 β0 n hn hpow0 hwker0 hder0
  let κ : β0.ker →* β.ker :=
    { toFun := fun k =>
        ⟨eQ.symm k.1, by
          change β (eQ.symm k.1) = 1
          have hk0 : β0 k.1 = 1 := by
            exact k.2
          have hk : eH (β (eQ.symm k.1)) = 1 := by
            simpa [β0] using hk0
          exact eH.injective (by simpa using hk)⟩
      map_one' := by
        apply Subtype.ext
        simp only [OneMemClass.coe_one, map_one]
      map_mul' := by
        intro a b
        apply Subtype.ext
        simp only [Subgroup.coe_mul, map_mul, MulMemClass.mk_mul_mk]}
  have hcomm_map : (commutator β0.ker).map κ ≤ commutator β.ker := by
    rw [_root_.map_commutator_eq]
    exact Subgroup.commutator_mono (by intro x hx; trivial) (by intro x hx; trivial)
  have hκq0 :
      κ q0 =
        (⟨α w, by
          change β (α w) = 1
          simpa [MonoidHom.mem_ker, MonoidHom.comp_apply] using hwker⟩ : β.ker) := by
    apply Subtype.ext
    have hphi : phi.symm (phi w) = w := phi.symm_apply_apply w
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_ofClass,
      Function.comp_apply, hphi, MonoidHom.coe_mk, OneHom.coe_mk,
      MulEquiv.symm_apply_apply, κ, q0, α0, w0]
  have hκcomm : κ q0 ∈ commutator β.ker :=
    hcomm_map ⟨q0, hcomm0, rfl⟩
  simpa [hκq0] using hκcomm


/--
Discrete Magnus descent through a surjective finite source quotient, with the hypothesis
expressed as ordinary relative Fox derivative zero for a representative word.
-/
theorem mem_commutator_ker_of_relFreeFoxDeriv_eq_zero_of_surj_factor
    {Q : Type} [Group Q]
    (α : FreeGroup X →* Q) (hα : Function.Surjective α)
    (β : Q →* H) (hβ : Function.Surjective β)
    (q : β.ker) (w : FreeGroup X) (hw : α w = q.1)
    (hn :
      FoxDifferential.FoxCalculus.relativeFreeGroupFoxDerivative
        (H := H) X (β.comp α) w = 0) :
    q ∈ commutator β.ker := by
  let ψ : FreeGroup X →* H := β.comp α
  have hψ : Function.Surjective ψ := by
    intro h
    rcases hβ h with ⟨q0, rfl⟩
    rcases hα q0 with ⟨w0, rfl⟩
    exact ⟨w0, rfl⟩
  have hwker : w ∈ ψ.ker := by
    change β (α w) = 1
    rw [hw]
    exact q.2
  let n : ψ.ker := ⟨w, hwker⟩
  have hncomm : n ∈ commutator ψ.ker :=
    mem_commutator_ker_of_relFreeFoxDeriv_eq_zero_of_surj
      (X := X) (H := H) ψ hψ n (by simpa [ψ, n] using hn)
  let κ : ψ.ker →* β.ker := {
    toFun := fun n => ⟨α n.1, by
      change β (α n.1) = 1
      change ψ n.1 = 1
      exact n.2⟩
    map_one' := by
      apply Subtype.ext
      simp only [OneMemClass.coe_one, map_one]
    map_mul' := by
      intro n₁ n₂
      apply Subtype.ext
      simp only [Subgroup.coe_mul, map_mul, MulMemClass.mk_mul_mk]}
  have hκn : κ n = q := by
    apply Subtype.ext
    exact hw
  have hcomm_map :
      (commutator ψ.ker).map κ ≤ commutator β.ker := by
    rw [_root_.map_commutator_eq]
    exact Subgroup.commutator_mono (by intro x hx; trivial) (by intro x hx; trivial)
  simpa [hκn] using hcomm_map ⟨n, hncomm, rfl⟩

/--
Over the all-finite coefficient class, vanishing of the completed universal differential on a
finite target quotient implies the ordinary discrete Magnus commutator conclusion.
-/
theorem mem_commutator_ker_of_zcUniversalDifferential_eq_zero_allFinite
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (FoxDifferential.foxAlgebraicStageTargetQuotient (X := X) N)]
    [DiscreteTopology (FoxDifferential.foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (FoxDifferential.foxAlgebraicStageTargetQuotient (X := X) N)]
    [Finite (FoxDifferential.foxAlgebraicStageTargetQuotient (X := X) N)]
    (n : (QuotientGroup.mk' N).ker)
    (hn :
      FoxDifferential.zcUniversalDifferential
        (ProCGroups.FiniteGroupClass.allFinite : ProCGroups.FiniteGroupClass)
        (QuotientGroup.mk' N) n.1 = 0) :
    n ∈ commutator (QuotientGroup.mk' N).ker := by
  exact
    mem_commutator_ker_of_relFreeFoxDeriv_eq_zero_of_surj
      (X := X)
      (H := FoxDifferential.foxAlgebraicStageTargetQuotient (X := X) N)
      (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N)
      n
      (FoxDifferential.relFreeFoxDeriv_eq_zero_of_zcUnivDiff_eq_zero_allFinite
        (X := X) N n.1 hn)

/--
Over the all-finite coefficient class, vanishing of the completed universal differential for
any surjective finite target map implies the ordinary discrete Magnus commutator conclusion.
-/
theorem mem_commutator_ker_of_zcUniversalDifferential_eq_zero_allFinite_of_surjective
    [TopologicalSpace H] [IsTopologicalGroup H] [DiscreteTopology H] [Finite H]
    (ψ : FreeGroup X →* H) (hψ : Function.Surjective ψ)
    (n : ψ.ker)
    (hn :
      FoxDifferential.zcUniversalDifferential
        (ProCGroups.FiniteGroupClass.allFinite : ProCGroups.FiniteGroupClass)
        ψ n.1 = 0) :
    n ∈ commutator ψ.ker := by
  exact
    mem_commutator_ker_of_relFreeFoxDeriv_eq_zero_of_surj
      (X := X) (H := H) ψ hψ n
      (FoxDifferential.relFreeFoxDeriv_eq_zero_of_zcUnivDiff_eq_zero_allFinite_of_surj
        (X := X) ψ hψ n.1 hn)

/--
All-finite discrete Magnus descent through a surjective finite source quotient, with the
hypothesis expressed as zero of the completed Fox derivative vector for the representative
word.
-/
theorem mem_commutator_ker_of_zcFreeFoxDerivVec_eq_zero_allFinite_of_surj_factor
    {Q : Type} [Group Q]
    [TopologicalSpace H] [IsTopologicalGroup H] [DiscreteTopology H] [Finite H]
    (α : FreeGroup X →* Q) (hα : Function.Surjective α)
    (β : Q →* H) (hβ : Function.Surjective β)
    (q : β.ker) (w : FreeGroup X) (hw : α w = q.1)
    (hn :
      FoxDifferential.zcFreeGroupFoxDerivativeVector
        (ProCGroups.FiniteGroupClass.allFinite : ProCGroups.FiniteGroupClass)
        (β.comp α) w = 0) :
    q ∈ commutator β.ker := by
  let ψ : FreeGroup X →* H := β.comp α
  have hψ : Function.Surjective ψ := by
    intro h
    rcases hβ h with ⟨q0, rfl⟩
    rcases hα q0 with ⟨w0, rfl⟩
    exact ⟨w0, rfl⟩
  exact
    mem_commutator_ker_of_relFreeFoxDeriv_eq_zero_of_surj_factor
      (X := X) (H := H) α hα β hβ q w hw
      (FoxDifferential.relFreeFoxDeriv_eq_zero_of_zcFreeFoxDerivVec_eq_zero_allFinite_of_surj
        (X := X) ψ hψ w (by simpa [ψ] using hn))

/--
All-finite discrete Magnus descent through a surjective finite source quotient. If a surjective
free-group map \(\alpha: \mathrm{FreeGroup}(X) \to Q\) presents a finite-stage source and
\(\beta: Q \to H\) is a surjective target map, vanishing of the completed universal
differential on a representative word of \(q \in \ker \beta\) forces \(q\) into the commutator
subgroup of \(\ker \beta\).
-/
theorem mem_commutator_ker_of_zcUnivDiff_eq_zero_allFinite_of_surj_factor
    {Q : Type} [Group Q]
    [TopologicalSpace H] [IsTopologicalGroup H] [DiscreteTopology H] [Finite H]
    (α : FreeGroup X →* Q) (hα : Function.Surjective α)
    (β : Q →* H) (hβ : Function.Surjective β)
    (q : β.ker) (w : FreeGroup X) (hw : α w = q.1)
    (hn :
      FoxDifferential.zcUniversalDifferential
        (ProCGroups.FiniteGroupClass.allFinite : ProCGroups.FiniteGroupClass)
        (β.comp α) w = 0) :
    q ∈ commutator β.ker := by
  exact
    mem_commutator_ker_of_zcFreeFoxDerivVec_eq_zero_allFinite_of_surj_factor
      (X := X) (H := H) α hα β hβ q w hw
      (FoxDifferential.zcFreeGroupFoxDerivativeVector_eq_zero_of_zcUniversalDifferential_eq_zero
        (C := (ProCGroups.FiniteGroupClass.allFinite : ProCGroups.FiniteGroupClass))
        (β.comp α) hn)

/--
Over the finite \(p\)-group coefficient class, vanishing of the completed universal
differential on a finite \(p\)-group target quotient implies the ordinary discrete Magnus
commutator conclusion.
-/
theorem mem_commutator_ker_of_zcUniversalDifferential_eq_zero_pGroup
    (p : ℕ) [Fact (Nat.Prime p)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (FoxDifferential.foxAlgebraicStageTargetQuotient (X := X) N)]
    [DiscreteTopology (FoxDifferential.foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (FoxDifferential.foxAlgebraicStageTargetQuotient (X := X) N)]
    (hCtarget :
      ProCGroups.FiniteGroupClass.pGroup p
        (FoxDifferential.foxAlgebraicStageTargetQuotient (X := X) N))
    (n : (QuotientGroup.mk' N).ker)
    (hn :
      FoxDifferential.zcUniversalDifferential
        (ProCGroups.FiniteGroupClass.pGroup p : ProCGroups.FiniteGroupClass)
        (QuotientGroup.mk' N) n.1 = 0) :
    n ∈ commutator (QuotientGroup.mk' N).ker := by
  exact
    mem_commutator_ker_of_relFreeFoxDeriv_eq_zero_of_surj
      (X := X)
      (H := FoxDifferential.foxAlgebraicStageTargetQuotient (X := X) N)
      (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N)
      n
      (relativeFreeGroupFoxDerivative_eq_zero_of_zcUniversalDifferential_eq_zero_pGroup
        (X := X) (N := N) (p := p) (hCtarget := hCtarget) (w := n.1) hn)

/--
Over the finite \(p\)-group coefficient class, vanishing of the completed universal
differential for any surjective finite \(p\)-group target map implies the ordinary discrete
Magnus commutator conclusion.
-/
theorem mem_commutator_ker_of_zcUniversalDifferential_eq_zero_pGroup_of_surjective
    (p : ℕ) [Fact (Nat.Prime p)]
    [TopologicalSpace H] [IsTopologicalGroup H] [DiscreteTopology H]
    (hCtarget : ProCGroups.FiniteGroupClass.pGroup p H)
    (ψ : FreeGroup X →* H) (hψ : Function.Surjective ψ)
    (n : ψ.ker)
    (hn :
      FoxDifferential.zcUniversalDifferential
        (ProCGroups.FiniteGroupClass.pGroup p : ProCGroups.FiniteGroupClass)
        ψ n.1 = 0) :
    n ∈ commutator ψ.ker := by
  exact
    mem_commutator_ker_of_relFreeFoxDeriv_eq_zero_of_surj
      (X := X) (H := H) ψ hψ n
      (FoxDifferential.relFreeFoxDeriv_eq_zero_of_zcUnivDiff_eq_zero_pGroup_of_surj
        (X := X) (H := H) (p := p) (hCtarget := hCtarget)
        (ψ := ψ) (hψ := hψ) (w := n.1) hn)

/--
Finite-p discrete Magnus descent through a surjective finite source quotient, with the
hypothesis expressed as zero of the completed Fox derivative vector for the representative
word.
-/
theorem mem_commutator_ker_of_zcFreeFoxDerivVec_eq_zero_pGroup_of_surj_factor
    (p : ℕ) [Fact (Nat.Prime p)]
    {Q : Type} [Group Q]
    [TopologicalSpace H] [IsTopologicalGroup H] [DiscreteTopology H]
    (hCtarget : ProCGroups.FiniteGroupClass.pGroup p H)
    (α : FreeGroup X →* Q) (hα : Function.Surjective α)
    (β : Q →* H) (hβ : Function.Surjective β)
    (q : β.ker) (w : FreeGroup X) (hw : α w = q.1)
    (hn :
      FoxDifferential.zcFreeGroupFoxDerivativeVector
        (ProCGroups.FiniteGroupClass.pGroup p : ProCGroups.FiniteGroupClass)
        (β.comp α) w = 0) :
    q ∈ commutator β.ker := by
  let ψ : FreeGroup X →* H := β.comp α
  have hψ : Function.Surjective ψ := by
    intro h
    rcases hβ h with ⟨q0, rfl⟩
    rcases hα q0 with ⟨w0, rfl⟩
    exact ⟨w0, rfl⟩
  exact
    mem_commutator_ker_of_relFreeFoxDeriv_eq_zero_of_surj_factor
      (X := X) (H := H) α hα β hβ q w hw
      (FoxDifferential.relFreeFoxDeriv_eq_zero_of_zcFreeFoxDerivVec_eq_zero_pGroup_of_surj
        (X := X) (H := H) (p := p) (hCtarget := hCtarget)
        (ψ := ψ) (hψ := hψ) (w := w) (by simpa [ψ] using hn))

/-- Finite-p discrete Magnus descent through a surjective finite source quotient. -/
theorem mem_commutator_ker_of_zcUnivDiff_eq_zero_pGroup_of_surj_factor
    (p : ℕ) [Fact (Nat.Prime p)]
    {Q : Type} [Group Q]
    [TopologicalSpace H] [IsTopologicalGroup H] [DiscreteTopology H]
    (hCtarget : ProCGroups.FiniteGroupClass.pGroup p H)
    (α : FreeGroup X →* Q) (hα : Function.Surjective α)
    (β : Q →* H) (hβ : Function.Surjective β)
    (q : β.ker) (w : FreeGroup X) (hw : α w = q.1)
    (hn :
      FoxDifferential.zcUniversalDifferential
        (ProCGroups.FiniteGroupClass.pGroup p : ProCGroups.FiniteGroupClass)
        (β.comp α) w = 0) :
    q ∈ commutator β.ker := by
  exact
    mem_commutator_ker_of_zcFreeFoxDerivVec_eq_zero_pGroup_of_surj_factor
      (X := X) (H := H) p hCtarget α hα β hβ q w hw
      (FoxDifferential.zcFreeGroupFoxDerivativeVector_eq_zero_of_zcUniversalDifferential_eq_zero
        (C := (ProCGroups.FiniteGroupClass.pGroup p : ProCGroups.FiniteGroupClass))
        (β.comp α) hn)

end

end CrowellExactSequence

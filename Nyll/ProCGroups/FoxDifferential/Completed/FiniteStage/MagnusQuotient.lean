/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.Stage.Derivative.Rules
import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.Stage.Derivative.Relators

/-!
# Fox differential: completed — finite stage — magnus quotient

The principal declarations in this module are:

- `foxAlgebraicStageSemidirectReindexHom`
  Reindex the finite-stage Fox semidirect target along an equivalence of free bases.
- `foxAlgebraicStageSemidirectReindexHom_lift`
  The reindexing hom carries the finite-stage lift to the finite-stage lift.
- `foxAlgebraicStageDerivativeVector_reindex`
  Finite-stage Fox derivative vectors reindex along an equivalence of free bases.
- `foxAlgebraicStageDerivativeVector_eq_zero_reindex`
  Zero of a finite-stage Fox derivative vector is invariant under reindexing the free basis.
-/

namespace FoxDifferential

noncomputable section

open scoped commutatorElement

universe u v

variable {X : Type u}

section Reindex

variable {Y : Type v}
variable [DecidableEq X] [DecidableEq Y]

/-- Reindex the finite-stage Fox semidirect target along an equivalence of free bases. -/
def foxAlgebraicStageSemidirectReindexHom
    (e : X ≃ Y)
    (N : Subgroup (FreeGroup X)) [N.Normal]
    (M : Subgroup (FreeGroup Y)) [M.Normal]
    (hM : N.map (FreeGroup.freeGroupCongr e).toMonoidHom = M)
    (n : ℕ) :
    FoxAlgebraicStageSemidirect (X := X) N n →*
      FoxAlgebraicStageSemidirect (X := Y) M n := by
  let φ : FreeGroup X ≃* FreeGroup Y := FreeGroup.freeGroupCongr e
  let qXY :
      foxAlgebraicStageTargetQuotient (X := X) N ≃*
        foxAlgebraicStageTargetQuotient (X := Y) M :=
    QuotientGroup.congr N M φ hM
  exact
    { toFun := fun a =>
        { left := fun y =>
            MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff n) qXY.toMonoidHom
              (a.left (e.symm y))
          right := qXY a.right }
      map_one' := by
        apply FoxAlgebraicStageSemidirect.ext
        · funext y
          simp only [MulEquiv.toMonoidHom_eq_coe, FoxAlgebraicStageSemidirect.one_left,
              Pi.zero_apply,
  MonoidAlgebra.mapDomainRingHom_apply, MonoidHom.coe_ofClass, MonoidAlgebra.mapDomain_zero]
        · simp only [FoxAlgebraicStageSemidirect.one_right, map_one]
      map_mul' := by
        intro a b
        apply FoxAlgebraicStageSemidirect.ext
        · funext y
          have hright :
              MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff n) qXY.toMonoidHom
                  (MonoidAlgebra.of (ModNCompletedCoeff n)
                    (foxAlgebraicStageTargetQuotient (X := X) N) a.right) =
                MonoidAlgebra.of (ModNCompletedCoeff n)
                  (foxAlgebraicStageTargetQuotient (X := Y) M) (qXY a.right) := by
            change MonoidAlgebra.mapDomain qXY.toMonoidHom
                (MonoidAlgebra.single a.right 1) =
              MonoidAlgebra.single (qXY a.right) 1
            exact MonoidAlgebra.mapDomain_single
          simp only [MulEquiv.toMonoidHom_eq_coe, FoxAlgebraicStageSemidirect.mul_left,
              MonoidAlgebra.of_apply,
  Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidHom.coe_ofClass,
  add_right_inj]
          change
            MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff n) qXY.toMonoidHom
                (MonoidAlgebra.of (ModNCompletedCoeff n)
                    (foxAlgebraicStageTargetQuotient (X := X) N) a.right *
                  b.left (e.symm y)) =
              MonoidAlgebra.of (ModNCompletedCoeff n)
                  (foxAlgebraicStageTargetQuotient (X := Y) M) (qXY a.right) *
                MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff n) qXY.toMonoidHom
                  (b.left (e.symm y))
          rw [map_mul, hright]
        · simp only [FoxAlgebraicStageSemidirect.mul_right, map_mul, MulEquiv.toMonoidHom_eq_coe,
  MonoidAlgebra.mapDomainRingHom_apply, MonoidHom.coe_ofClass]}

/-- The reindexing hom carries the finite-stage lift to the finite-stage lift. -/
theorem foxAlgebraicStageSemidirectReindexHom_lift
    (e : X ≃ Y)
    (N : Subgroup (FreeGroup X)) [N.Normal]
    (M : Subgroup (FreeGroup Y)) [M.Normal]
    (hM : N.map (FreeGroup.freeGroupCongr e).toMonoidHom = M)
    (n : ℕ) (w : FreeGroup X) :
    foxAlgebraicStageSemidirectReindexHom (X := X) (Y := Y) e N M hM n
        (foxAlgebraicStageLift (X := X) N n w) =
      foxAlgebraicStageLift (X := Y) M n ((FreeGroup.freeGroupCongr e) w) := by
  let φ : FreeGroup X ≃* FreeGroup Y := FreeGroup.freeGroupCongr e
  let qXY :
      foxAlgebraicStageTargetQuotient (X := X) N ≃*
        foxAlgebraicStageTargetQuotient (X := Y) M :=
    QuotientGroup.congr N M φ hM
  let f₁ : FreeGroup X →* FoxAlgebraicStageSemidirect (X := Y) M n :=
    (foxAlgebraicStageSemidirectReindexHom (X := X) (Y := Y) e N M hM n).comp
      (foxAlgebraicStageLift (X := X) N n)
  let f₂ : FreeGroup X →* FoxAlgebraicStageSemidirect (X := Y) M n :=
    (foxAlgebraicStageLift (X := Y) M n).comp φ.toMonoidHom
  have hf : f₁ = f₂ := by
    apply FreeGroup.ext_hom
    intro x
    apply FoxAlgebraicStageSemidirect.ext
    · funext y
      by_cases hy : y = e x
      · subst hy
        simp only [foxAlgebraicStageSemidirectReindexHom, MulEquiv.toMonoidHom_eq_coe,
  MonoidAlgebra.mapDomainRingHom_apply, MonoidHom.coe_ofClass, foxAlgebraicStageLift,
      QuotientGroup.mk'_apply,
  MonoidHom.coe_comp, MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_apply, FreeGroup.lift_apply_of,
  FreeGroup.freeGroupCongr_apply, FreeGroup.map.of, Pi.single_eq_same,
      f₁, f₂, φ]
        rw [e.symm_apply_apply, Pi.single_eq_same]
        simp only [MonoidAlgebra.mapDomain_one]
      · have hne : e.symm y ≠ x := by
          intro h
          exact hy ((e.apply_symm_apply y).symm.trans (by simp only [h]))
        simp only [foxAlgebraicStageSemidirectReindexHom, MulEquiv.toMonoidHom_eq_coe,
  MonoidAlgebra.mapDomainRingHom_apply, MonoidHom.coe_ofClass, foxAlgebraicStageLift,
      QuotientGroup.mk'_apply,
  MonoidHom.coe_comp, MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_apply, FreeGroup.lift_apply_of,
  FreeGroup.freeGroupCongr_apply, FreeGroup.map.of, Pi.single_eq_of_ne hne,
  MonoidAlgebra.mapDomain_zero, Pi.single_eq_of_ne hy, f₁, f₂, φ]
    · change
        (QuotientGroup.congr N M (FreeGroup.freeGroupCongr e) hM)
            (QuotientGroup.mk' N (FreeGroup.of x)) =
          QuotientGroup.mk' M (FreeGroup.of (e x))
      exact
        (QuotientGroup.congr_mk' N M (FreeGroup.freeGroupCongr e) hM (FreeGroup.of x)).trans
          (congrArg (QuotientGroup.mk' M) (by
            simp only [FreeGroup.freeGroupCongr_apply, FreeGroup.map.of]))
  exact congrArg (fun f : FreeGroup X →* FoxAlgebraicStageSemidirect (X := Y) M n => f w) hf

/-- Finite-stage Fox derivative vectors reindex along an equivalence of free bases. -/
theorem foxAlgebraicStageDerivativeVector_reindex
    (e : X ≃ Y)
    (N : Subgroup (FreeGroup X)) [N.Normal]
    (M : Subgroup (FreeGroup Y)) [M.Normal]
    (hM : N.map (FreeGroup.freeGroupCongr e).toMonoidHom = M)
    (n : ℕ) (w : FreeGroup X) :
    foxAlgebraicStageDerivativeVector (X := Y) M n ((FreeGroup.freeGroupCongr e) w) =
      fun y =>
        MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff n)
          (QuotientGroup.congr N M (FreeGroup.freeGroupCongr e) hM).toMonoidHom
          (foxAlgebraicStageDerivativeVector (X := X) N n w (e.symm y)) := by
  have h :=
    congrArg FoxAlgebraicStageSemidirect.left
      (foxAlgebraicStageSemidirectReindexHom_lift
        (X := X) (Y := Y) e N M hM n w)
  simpa [foxAlgebraicStageDerivativeVector, foxAlgebraicStageSemidirectReindexHom] using h.symm

/-- Zero of a finite-stage Fox derivative vector is invariant under reindexing the free basis. -/
theorem foxAlgebraicStageDerivativeVector_eq_zero_reindex
    (e : X ≃ Y)
    (N : Subgroup (FreeGroup X)) [N.Normal]
    (M : Subgroup (FreeGroup Y)) [M.Normal]
    (hM : N.map (FreeGroup.freeGroupCongr e).toMonoidHom = M)
    (n : ℕ) {w : FreeGroup X}
    (hw : foxAlgebraicStageDerivativeVector (X := X) N n w = 0) :
    foxAlgebraicStageDerivativeVector (X := Y) M n ((FreeGroup.freeGroupCongr e) w) = 0 := by
  rw [foxAlgebraicStageDerivativeVector_reindex (X := X) (Y := Y) e N M hM n w]
  funext y
  simp only [MulEquiv.toMonoidHom_eq_coe, hw, Pi.zero_apply, MonoidAlgebra.mapDomainRingHom_apply,
  MonoidHom.coe_ofClass, MonoidAlgebra.mapDomain_zero]

end Reindex

variable {Q H : Type u}
variable [Group Q] [Group H]

section CommutatorPowerSubgroup

variable {F : Type u} [Group F]

/--
The ordinary commutator subgroup of \(N\), mapped back to the ambient group, is contained in the
finite Fox commutator-power subgroup.
-/
theorem commutator_subtype_le_foxCommutatorPowerSubgroup
    (N : Subgroup F) (n : ℕ) :
    (commutator N).map N.subtype ≤ foxCommutatorPowerSubgroup (F := F) N n := by
  rw [Subgroup.map_subtype_commutator]
  refine Subgroup.commutator_le.mpr ?_
  intro a ha b hb
  exact Subgroup.subset_normalClosure
    (Or.inl ⟨a, ha, b, hb, rfl⟩)

/-- Nth powers from N are defining relators for the finite Fox commutator-power subgroup. -/
theorem pow_mem_foxCommutatorPowerSubgroup
    (N : Subgroup F) (n : ℕ) {a : F} (ha : a ∈ N) :
    a ^ n ∈ foxCommutatorPowerSubgroup (F := F) N n :=
  Subgroup.subset_normalClosure (Or.inr ⟨a, ha, rfl⟩)

/--
If the abelianization class of a kernel element is an \(n\)-th power, then the element lies in
\([N,N]N^n\).
-/
theorem mem_foxCommutatorPowerSubgroup_of_abelianization_eq_pow
    (N : Subgroup F) (n : ℕ) {w : F} (hw : w ∈ N) (a : N)
    (hclass :
      Abelianization.of ⟨w, hw⟩ = (Abelianization.of a) ^ n) :
    w ∈ foxCommutatorPowerSubgroup (F := F) N n := by
  have hclass' :
      Abelianization.of (a ^ n) = Abelianization.of ⟨w, hw⟩ := by
    simpa using hclass.symm
  have hcommN : (a ^ n)⁻¹ * ⟨w, hw⟩ ∈ commutator N :=
    QuotientGroup.eq.mp hclass'
  have hcommF :
      ((a : F) ^ n)⁻¹ * w ∈
        foxCommutatorPowerSubgroup (F := F) N n := by
    have hmap :
        (((a ^ n)⁻¹ * ⟨w, hw⟩ : N) : F) ∈ (commutator N).map N.subtype :=
      ⟨(a ^ n)⁻¹ * ⟨w, hw⟩, hcommN, rfl⟩
    exact
      commutator_subtype_le_foxCommutatorPowerSubgroup (F := F) N n
        (by simpa using hmap)
  have hpowF :
      (a : F) ^ n ∈ foxCommutatorPowerSubgroup (F := F) N n :=
    pow_mem_foxCommutatorPowerSubgroup (F := F) N n a.2
  have hmul :
      (a : F) ^ n * (((a : F) ^ n)⁻¹ * w) ∈
        foxCommutatorPowerSubgroup (F := F) N n :=
    (foxCommutatorPowerSubgroup (F := F) N n).mul_mem hpowF hcommF
  simpa [mul_assoc] using hmul

end CommutatorPowerSubgroup

/--
Residue-Fox form of the finite-stage Magnus reverse inclusion. The finite-stage derivative is
not a separate Fox theory: it is the residue free Fox derivative for the quotient map
\(\mathrm{FreeGroup}(X) \to F/N\). This is the residue form of the finite Magnus reverse
inclusion, expressed through the finite-stage derivative.
-/
theorem ker_foxAlgebraicStageLift_le_foxCommutatorPowerSubgroup_iff_residue
    [DecidableEq X]
    (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ) :
    (foxAlgebraicStageLift (X := X) N n).ker ≤
        foxCommutatorPowerSubgroup (F := FreeGroup X) N n ↔
      ∀ w : FreeGroup X,
        w ∈ N →
        residueFreeGroupFoxDerivativeVector n (QuotientGroup.mk' N) w = 0 →
          w ∈ foxCommutatorPowerSubgroup (F := FreeGroup X) N n := by
  rw [ker_foxAlgebraicStageLift_le_foxCommutatorPowerSubgroup_iff]
  constructor
  · intro h w hwN hder
    exact h w hwN (by
      simpa [foxAlgebraicStageDerivativeVector_eq_residueFreeGroupFoxDerivativeVector (X := X) N n]
        using hder)
  · intro h w hwN hder
    exact h w hwN (by
      simpa [foxAlgebraicStageDerivativeVector_eq_residueFreeGroupFoxDerivativeVector (X := X) N n]
        using hder)

/--
Residue-universal form of the finite-stage Magnus reverse inclusion. With a finite free basis,
the finite-stage coordinate vector is equivalent to the residue universal differential, so the
remaining theorem is a kernel statement in the residue universal module.
-/
theorem ker_foxAlgebraicStageLift_le_foxCommutatorPowerSubgroup_iff_residueUniversal
    [DecidableEq X] [Finite X]
    (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ) :
    (foxAlgebraicStageLift (X := X) N n).ker ≤
        foxCommutatorPowerSubgroup (F := FreeGroup X) N n ↔
      ∀ w : FreeGroup X,
        w ∈ N →
        residueUniversalDifferential n (QuotientGroup.mk' N) w = 0 →
          w ∈ foxCommutatorPowerSubgroup (F := FreeGroup X) N n := by
  classical
  let : Fintype X := Fintype.ofFinite X
  rw [ker_foxAlgebraicStageLift_le_foxCommutatorPowerSubgroup_iff]
  constructor
  · intro h w hwN hres
    exact h w hwN
      ((foxAlgebraicStageDerivativeVector_eq_zero_iff_residueUniversalDifferential_eq_zero
        (X := X) (N := N) (n := n) (w := w)).2 hres)
  · intro h w hwN hder
    exact h w hwN
      ((foxAlgebraicStageDerivativeVector_eq_zero_iff_residueUniversalDifferential_eq_zero
        (X := X) (N := N) (n := n) (w := w)).1 hder)

/--
The finite commutator-power subgroup maps into the ordinary commutator subgroup of a target
kernel whenever the chosen exponent kills that kernel. This is the mathematical quotient
bookkeeping needed after the finite-stage Magnus kernel theorem: the commutator relators map to
commutators in kernel \(\beta\), while the power relators map to \(1\) by the given
exponent-killing hypothesis.
-/
theorem mem_commutator_ker_of_mem_foxCommutatorPowerSubgroup_of_pow_eq_one
    (α : FreeGroup X →* Q) (β : Q →* H) (n : ℕ)
    (hpow : ∀ k : β.ker, k ^ n = 1)
    {w : FreeGroup X}
    (hwker : w ∈ (β.comp α).ker)
    (hw :
      w ∈ foxCommutatorPowerSubgroup
        (F := FreeGroup X) (β.comp α).ker n) :
    (⟨α w, by
      change β (α w) = 1
      simpa [MonoidHom.mem_ker, MonoidHom.comp_apply] using hwker⟩ : β.ker) ∈
      commutator β.ker := by
  let K : Subgroup Q := β.ker
  let S : Subgroup (FreeGroup X) := (⁅K, K⁆).comap α
  have hSnormal : S.Normal := by
    dsimp [S, K]
    infer_instance
  have hrel_le :
      foxCommutatorPowerSubgroup (F := FreeGroup X) (β.comp α).ker n ≤ S := by
    refine Subgroup.normalClosure_le_normal ?_
    intro g hg
    rcases hg with ⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, rfl⟩
    · change α ⁅a, b⁆ ∈ ⁅K, K⁆
      rw [map_commutatorElement]
      have haK : α a ∈ K := by
        change β (α a) = 1
        simpa [MonoidHom.mem_ker, MonoidHom.comp_apply] using ha
      have hbK : α b ∈ K := by
        change β (α b) = 1
        simpa [MonoidHom.mem_ker, MonoidHom.comp_apply] using hb
      exact Subgroup.commutator_mem_commutator haK hbK
    · change α (a ^ n) ∈ ⁅K, K⁆
      rw [map_pow]
      have haK : α a ∈ β.ker := by
        change β (α a) = 1
        simpa [MonoidHom.mem_ker, MonoidHom.comp_apply] using ha
      have hpowQ : (α a) ^ n = 1 := by
        simpa using congrArg Subtype.val (hpow ⟨α a, haK⟩)
      rw [hpowQ]
      exact (⁅K, K⁆).one_mem
  have hQ : α w ∈ ⁅K, K⁆ := hrel_le hw
  have hQmap : α w ∈ (commutator β.ker).map β.ker.subtype := by
    simpa [K, Subgroup.map_subtype_commutator] using hQ
  rcases hQmap with ⟨c, hc, hcval⟩
  have hc_eq :
      c =
        (⟨α w, by
          change β (α w) = 1
          simpa [MonoidHom.mem_ker, MonoidHom.comp_apply] using hwker⟩ : β.ker) := by
    apply Subtype.ext
    exact hcval
  simpa [hc_eq] using hc

/-- The finite-kernel cardinality version of the quotient bookkeeping lemma. -/
theorem mem_commutator_ker_of_mem_foxCommutatorPowerSubgroup_card
    (α : FreeGroup X →* Q) (β : Q →* H)
    {w : FreeGroup X}
    (hwker : w ∈ (β.comp α).ker)
    (hw :
      w ∈ foxCommutatorPowerSubgroup
        (F := FreeGroup X) (β.comp α).ker (Nat.card β.ker)) :
    (⟨α w, by
      change β (α w) = 1
      simpa [MonoidHom.mem_ker, MonoidHom.comp_apply] using hwker⟩ : β.ker) ∈
      commutator β.ker := by
  exact
    mem_commutator_ker_of_mem_foxCommutatorPowerSubgroup_of_pow_eq_one
      (X := X) α β (Nat.card β.ker) (fun _ => pow_card_eq_one') hwker hw

/--
Finite quotient commutator conclusion from the finite-stage Magnus reverse inclusion. Once the
kernel of the finite-stage lift has been identified with \([N,N]N^m\), a zero finite-stage
derivative for a representative word gives the ordinary commutator conclusion in kernel \beta.
-/
theorem mem_commutator_ker_of_foxAlgebraicStageDerivativeVector_eq_zero_of_ker_le
    [DecidableEq X]
    (α : FreeGroup X →* Q) (β : Q →* H) (n : ℕ)
    (hpow : ∀ k : β.ker, k ^ n = 1)
    (hmag :
      (foxAlgebraicStageLift (X := X) (β.comp α).ker n).ker ≤
        foxCommutatorPowerSubgroup (F := FreeGroup X) (β.comp α).ker n)
    {w : FreeGroup X}
    (hwker : w ∈ (β.comp α).ker)
    (hder :
      foxAlgebraicStageDerivativeVector (X := X) (β.comp α).ker n w = 0) :
    (⟨α w, by
      change β (α w) = 1
      simpa [MonoidHom.mem_ker, MonoidHom.comp_apply] using hwker⟩ : β.ker) ∈
      commutator β.ker := by
  have hwrel :
      w ∈ foxCommutatorPowerSubgroup (F := FreeGroup X) (β.comp α).ker n :=
    hmag
      ((mem_ker_foxAlgebraicStageLift_iff
        (X := X) (N := (β.comp α).ker) (n := n)).2
        ⟨hwker, hder⟩)
  exact
    mem_commutator_ker_of_mem_foxCommutatorPowerSubgroup_of_pow_eq_one
      (X := X) α β n hpow hwker hwrel

/--
Finite quotient commutator conclusion from the residue-universal finite Magnus kernel statement.
-/
theorem mem_commutator_ker_of_residueUniversalDifferential_eq_zero_of_kernel_le
    (α : FreeGroup X →* Q) (β : Q →* H) (n : ℕ)
    (hpow : ∀ k : β.ker, k ^ n = 1)
    (hmag :
      ∀ w : FreeGroup X,
        w ∈ (β.comp α).ker →
        residueUniversalDifferential n (QuotientGroup.mk' (β.comp α).ker) w = 0 →
          w ∈ foxCommutatorPowerSubgroup
            (F := FreeGroup X) (β.comp α).ker n)
    {w : FreeGroup X}
    (hwker : w ∈ (β.comp α).ker)
    (hder :
      residueUniversalDifferential n (QuotientGroup.mk' (β.comp α).ker) w = 0) :
    (⟨α w, by
      change β (α w) = 1
      simpa [MonoidHom.mem_ker, MonoidHom.comp_apply] using hwker⟩ : β.ker) ∈
      commutator β.ker := by
  exact
    mem_commutator_ker_of_mem_foxCommutatorPowerSubgroup_of_pow_eq_one
      (X := X) α β n hpow hwker (hmag w hwker hder)

/--
The cardinality-specialized finite quotient commutator conclusion from the finite-stage Magnus
reverse inclusion.
-/
theorem mem_commutator_ker_of_foxAlgebraicStageDerivativeVector_eq_zero_of_ker_le_card
    [DecidableEq X]
    (α : FreeGroup X →* Q) (β : Q →* H)
    (hmag :
      (foxAlgebraicStageLift (X := X) (β.comp α).ker (Nat.card β.ker)).ker ≤
        foxCommutatorPowerSubgroup
          (F := FreeGroup X) (β.comp α).ker (Nat.card β.ker))
    {w : FreeGroup X}
    (hwker : w ∈ (β.comp α).ker)
    (hder :
      foxAlgebraicStageDerivativeVector (X := X) (β.comp α).ker (Nat.card β.ker) w = 0) :
    (⟨α w, by
      change β (α w) = 1
      simpa [MonoidHom.mem_ker, MonoidHom.comp_apply] using hwker⟩ : β.ker) ∈
      commutator β.ker := by
  exact
    mem_commutator_ker_of_foxAlgebraicStageDerivativeVector_eq_zero_of_ker_le
      (X := X) α β (Nat.card β.ker) (fun _ => pow_card_eq_one') hmag hwker hder

/--
The cardinality-specialized finite quotient commutator conclusion from the residue-universal
finite Magnus kernel statement.
-/
theorem mem_commutator_ker_of_residueUniversalDifferential_eq_zero_of_kernel_le_card
    (α : FreeGroup X →* Q) (β : Q →* H)
    (hmag :
      ∀ w : FreeGroup X,
        w ∈ (β.comp α).ker →
        residueUniversalDifferential (Nat.card β.ker)
            (QuotientGroup.mk' (β.comp α).ker) w = 0 →
          w ∈ foxCommutatorPowerSubgroup
            (F := FreeGroup X) (β.comp α).ker (Nat.card β.ker))
    {w : FreeGroup X}
    (hwker : w ∈ (β.comp α).ker)
    (hder :
      residueUniversalDifferential (Nat.card β.ker)
          (QuotientGroup.mk' (β.comp α).ker) w = 0) :
    (⟨α w, by
      change β (α w) = 1
      simpa [MonoidHom.mem_ker, MonoidHom.comp_apply] using hwker⟩ : β.ker) ∈
      commutator β.ker := by
  exact
    mem_commutator_ker_of_residueUniversalDifferential_eq_zero_of_kernel_le
      (X := X) α β (Nat.card β.ker) (fun _ => pow_card_eq_one') hmag hwker hder

end

end FoxDifferential

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Discrete.KernelBoundary.IdentityAugmentation

/-!
# Fox differential: discrete — kernel boundary — basic

The principal declarations in this module are:

- `KernelAbelianizationAdd`
  Additive form of the kernel abelianization map.
- `kernelBoundary`
  The kernel of \(\psi\) maps multiplicatively into the additive differential module via d.
- `augmentation_toGroupRing_eq_zero`
  The Crowell boundary map lands in the kernel of the augmentation map.
- `augmentation_surjective`
  The augmentation map \(\mathbb{Z}[H] \to \mathbb{Z}\) is surjective.
-/

namespace FoxDifferential

noncomputable section


variable {H G : Type*} [Group H] [DecidableEq H] [Group G] [DecidableEq G]

/-- Additive form of the kernel abelianization map. -/
abbrev KernelAbelianizationAdd (ψ : G →* H) : Type _ :=
  Additive (Abelianization ψ.ker)

omit [DecidableEq H] [DecidableEq G] in
/-- The Crowell boundary map lands in the kernel of the augmentation map. -/
theorem augmentation_toGroupRing_eq_zero (ψ : G →* H) (x : DifferentialModule ψ) :
    augmentation H (toGroupRing ψ x) = 0 := by
  exact (mem_augmentationIdeal_iff (H := H) (x := toGroupRing ψ x)).1
    (toGroupRing_mem_augmentationIdeal (H := H) ψ x)

omit [DecidableEq H] in
/-- The augmentation map \(\mathbb{Z}[H] \to \mathbb{Z}\) is surjective. -/
theorem augmentation_surjective : Function.Surjective (augmentation H) := by
  intro n
  refine ⟨(n : GroupRing H), ?_⟩
  simp only [augmentation, augmentationAlgHom, AlgHom.toRingHom_eq_coe, map_intCast, Int.cast_eq]

omit [DecidableEq H] [DecidableEq G] in
/--
Tail exactness of the discrete Crowell sequence: \(A_{\psi}\) \(\to\) \(\mathbb{Z}[H]\) \(\to\)
\(\mathbb{Z}\) is used when \(\psi\) is surjective.
-/
theorem exact_toGroupRing_augmentation (ψ : G →* H) (hψ : Function.Surjective ψ) :
    Function.Exact (fun x => toGroupRing ψ x) (augmentation H) := by
  intro y
  constructor
  · intro hy
    have hy_mem : y ∈ augmentationIdeal H := (mem_augmentationIdeal_iff (H := H) (x := y)).2 hy
    let y' : augmentationIdeal H := ⟨y, hy_mem⟩
    rcases toAugmentationIdeal_surjective (H := H) ψ hψ y' with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    exact congrArg Subtype.val hx
  · rintro ⟨x, rfl⟩
    exact augmentation_toGroupRing_eq_zero (H := H) ψ x

/-- The kernel of \(\psi\) maps multiplicatively into the additive differential module via d. -/
def kernelBoundary (ψ : G →* H) : ψ.ker →* Multiplicative (DifferentialModule ψ) where
  toFun g := Multiplicative.ofAdd (universalDifferential ψ g.1)
  map_one' := by
    apply congrArg Multiplicative.ofAdd
    simp only [OneMemClass.coe_one, universalDifferential_one]
  map_mul' g₁ g₂ := by
    apply congrArg Multiplicative.ofAdd
    have h := universalDifferential_mul ψ g₁.1 g₂.1
    have hψ : (MonoidAlgebra.of ℤ H (ψ g₁.1) : GroupRing H) = 1 := by
      rw [g₁.2, groupRing_of_one (H := H)]
    rw [hψ, one_smul] at h
    simpa using h

/-- The kernel boundary factors through the abelianization of \(\ker \psi\). -/
def kernelAbelianizationBoundary (ψ : G →* H) :
    Abelianization ψ.ker →* Multiplicative (DifferentialModule ψ) :=
  Abelianization.lift (kernelBoundary ψ)

/-- The additive kernel-boundary map sends a kernel element to its abelianization boundary class. -/
def kernelAbelianizationBoundaryAdd (ψ : G →* H) :
    Additive (Abelianization ψ.ker) →+ DifferentialModule ψ where
  toFun x := Multiplicative.toAdd (kernelAbelianizationBoundary ψ (Additive.toMul x))
  map_zero' := by
    simp only [toMul_zero, map_one, toAdd_one]
  map_add' x y := by
    simp only [toMul_add, map_mul, toAdd_mul]

omit [DecidableEq H] [DecidableEq G] in
/-- The additive kernel-boundary map has the stated value on a kernel element. -/
@[simp 900]
theorem kernelAbelianizationBoundaryAdd_of (ψ : G →* H) (g : ψ.ker) :
    kernelAbelianizationBoundaryAdd ψ (Additive.ofMul (Abelianization.of g)) =
        universalDifferential ψ g.1 := by
  change Multiplicative.toAdd (Multiplicative.ofAdd (universalDifferential ψ g.1)) =
      universalDifferential ψ g.1
  rfl

/-- Conjugation by G on \(\ker \psi\), transported to the abelianization of \(\ker \psi\). -/
def kernelAbelianizationConj (ψ : G →* H) :
    G →* MulAut (Abelianization ψ.ker) where
  toFun g := (MulAut.conjNormal (H := ψ.ker) g).abelianizationCongr
  map_one' := by
    ext x
    refine QuotientGroup.induction_on x ?_
    intro n
    have hconj : MulAut.conjNormal (H := ψ.ker) (1 : G) = 1 := by
      ext m
      simp only [map_one, MulAut.one_apply]
    rw [hconj]
    rfl
  map_mul' g₁ g₂ := by
    ext x
    refine QuotientGroup.induction_on x ?_
    intro n
    let e₁ : MulAut ψ.ker := MulAut.conjNormal (H := ψ.ker) g₁
    let e₂ : MulAut ψ.ker := MulAut.conjNormal (H := ψ.ker) g₂
    have hconj : MulAut.conjNormal (H := ψ.ker) (g₁ * g₂) = e₁ * e₂ := by
      ext m
      simp only [map_mul, MulAut.mul_apply, MulAut.conjNormal_apply, mul_assoc, e₁, e₂]
    rw [hconj]
    calc
      (e₁ * e₂).abelianizationCongr (Abelianization.of n)
          = Abelianization.of ((e₁ * e₂) n) := by
              exact abelianizationCongr_of (e := e₁ * e₂) n
      _ = e₁.abelianizationCongr (Abelianization.of (e₂ n)) := by
            exact (abelianizationCongr_of (e := e₁) (e₂ n)).symm
      _ = e₁.abelianizationCongr (e₂.abelianizationCongr (Abelianization.of n)) := by
            rw [abelianizationCongr_of (e := e₂) n]
      _ = (e₁.abelianizationCongr * e₂.abelianizationCongr) (Abelianization.of n) := by
            rfl

omit [DecidableEq H] [DecidableEq G] in
/--
The conjugation action on kernel abelianization is computed by the displayed representative
formula.
-/
@[simp]
theorem kernelAbelianizationConj_of (ψ : G →* H) (g : G) (n : ψ.ker) :
    kernelAbelianizationConj ψ g (Abelianization.of n) =
      Abelianization.of (MulAut.conjNormal (H := ψ.ker) g n) := by
  rfl

omit [DecidableEq H] [DecidableEq G] in
/-- Conjugation by a kernel element becomes trivial in the kernel abelianization. -/
@[simp]
theorem kernelAbelianizationConj_eq_one_of_mem_ker (ψ : G →* H) (n : ψ.ker) :
    kernelAbelianizationConj ψ n = 1 := by
  ext x
  refine QuotientGroup.induction_on x ?_
  intro k
  calc
    kernelAbelianizationConj ψ n (Abelianization.of k)
        = Abelianization.of ((MulAut.conjNormal (H := ψ.ker) (n : G)) k) := by
            exact abelianizationCongr_of (e := MulAut.conjNormal (H := ψ.ker) (n : G)) k
    _ = Abelianization.of (n * k * n⁻¹) := by
          congr 1
    _ = Abelianization.of k := by
          simp only [mul_assoc, map_mul, map_inv, mul_inv_cancel_comm_assoc]

omit [DecidableEq H] [DecidableEq G] in
/--
Elements in the kernel of \(\psi\) act trivially after passing to the kernel abelianization
action.
-/
theorem ker_le_kernelAbelianizationConj_ker (ψ : G →* H) :
    ψ.ker ≤ (kernelAbelianizationConj ψ).ker := by
  intro n hn
  change kernelAbelianizationConj ψ n = 1
  simpa using kernelAbelianizationConj_eq_one_of_mem_ker (ψ := ψ) ⟨n, hn⟩

/--
The conjugation action on the abelianization of \(\ker \psi\) factors through \(G/\ker \psi\).
-/
def quotientKernelAbelianizationConj (ψ : G →* H) :
    G ⧸ ψ.ker →* MulAut (Abelianization ψ.ker) :=
  QuotientGroup.lift ψ.ker (kernelAbelianizationConj ψ) (ker_le_kernelAbelianizationConj_ker ψ)

omit [DecidableEq H] [DecidableEq G] in
/--
If \(\psi\) is surjective, the conjugation action on the abelianization of \(\ker \psi\) is
expressed directly as an action of H.
-/
def kernelAbelianizationConjOfSurjective
    (ψ : G →* H) (hψ : Function.Surjective ψ) :
    H →* MulAut (Abelianization ψ.ker) :=
  (quotientKernelAbelianizationConj ψ).comp
    (QuotientGroup.quotientKerEquivOfSurjective (φ := ψ) hψ).symm.toMonoidHom

omit [DecidableEq H] [DecidableEq G] in
/--
For a surjective \(\psi\), the induced action on the kernel abelianization agrees with
conjugation by a chosen preimage.
-/
@[simp 900]
theorem kernelAbelianizationConjOfSurjective_eq_surjInv
    (ψ : G →* H) (hψ : Function.Surjective ψ) (h : H) :
    kernelAbelianizationConjOfSurjective ψ hψ h =
      kernelAbelianizationConj ψ (Function.surjInv hψ h) := by
  let g₁ : G := hψ.hasRightInverse.choose h
  let g₂ : G := Function.surjInv hψ h
  have hg₁ : ψ g₁ = h := hψ.hasRightInverse.choose_spec h
  have hg₂ : ψ g₂ = h := Function.surjInv_eq hψ h
  have hker : ψ (g₁ * g₂⁻¹) = 1 := by
    simp only [map_mul, hg₁, map_inv, hg₂, mul_inv_cancel]
  have htriv :
      kernelAbelianizationConj ψ (g₁ * g₂⁻¹) = 1 := by
    simpa using kernelAbelianizationConj_eq_one_of_mem_ker (ψ := ψ) ⟨g₁ * g₂⁻¹, hker⟩
  have hsame :
      kernelAbelianizationConj ψ g₁ = kernelAbelianizationConj ψ g₂ := by
    have hmul :
        kernelAbelianizationConj ψ g₁ *
            (kernelAbelianizationConj ψ g₂)⁻¹ = 1 := by
      simpa [map_mul] using htriv
    have hmul' := congrArg (fun u : MulAut (Abelianization ψ.ker) =>
        u * kernelAbelianizationConj ψ g₂) hmul
    simpa [mul_assoc] using hmul'
  change quotientKernelAbelianizationConj ψ
      ((QuotientGroup.quotientKerEquivOfSurjective (φ := ψ) hψ).symm h) =
    kernelAbelianizationConj ψ g₂
  have hq :
      (QuotientGroup.quotientKerEquivOfSurjective (φ := ψ) hψ).symm h =
        QuotientGroup.mk' ψ.ker g₁ := by
    apply (QuotientGroup.quotientKerEquivOfSurjective (φ := ψ) hψ).injective
    rw [MulEquiv.apply_symm_apply]
    exact hg₁.symm
  rw [hq]
  change kernelAbelianizationConj ψ g₁ = kernelAbelianizationConj ψ g₂
  exact hsame

/--
For a surjective homomorphism, the conjugation action on the kernel abelianization is rewritten
as an additive automorphism action.
-/
def kernelAbelianizationAddAutOfSurjective
    (ψ : G →* H) (hψ : Function.Surjective ψ) :
    H →* Multiplicative (AddAut (KernelAbelianizationAdd ψ)) :=
  (AddAutAdditive (Abelianization ψ.ker)).symm.toAddMonoidHom.toMultiplicativeRight.comp
    (kernelAbelianizationConjOfSurjective ψ hψ)

omit [DecidableEq H] [DecidableEq G] in
/--
An additive automorphism of the kernel abelianization determines its underlying
\(\mathbb{Z}\)-linear endomorphism.
-/
def kernelAbelianizationAddAutToModuleEnd (ψ : G →* H) :
    Multiplicative (AddAut (KernelAbelianizationAdd ψ)) →*
      Module.End ℤ (KernelAbelianizationAdd ψ) where
  toFun e := e.toAdd.toIntLinearEquiv.toLinearMap
  map_one' := by
    ext x
    change (0 : AddAut (KernelAbelianizationAdd ψ)) x = x
    rfl
  map_mul' e₁ e₂ := by
    ext x
    change (e₁.toAdd + e₂.toAdd) x = e₁.toAdd (e₂.toAdd x)
    rfl

/-- The surjective-case action as a hom into \(\mathbb{Z}\)-linear endomorphisms. -/
def kernelAbelianizationModuleEndOfSurjective
    (ψ : G →* H) (hψ : Function.Surjective ψ) :
    H →* Module.End ℤ (KernelAbelianizationAdd ψ) where
  toFun h := kernelAbelianizationAddAutToModuleEnd (ψ := ψ)
    (kernelAbelianizationAddAutOfSurjective ψ hψ h)
  map_one' := by
    rw [(kernelAbelianizationAddAutOfSurjective ψ hψ).map_one]
    ext x
    rfl
  map_mul' h₁ h₂ := by
    rw [(kernelAbelianizationAddAutOfSurjective ψ hψ).map_mul]
    ext x
    rfl

omit [DecidableEq H] [DecidableEq G] in
/--
The module endomorphism associated to `h` acts by the conjugation automorphism obtained from a
chosen lift of `h`.
-/
@[simp]
theorem kernelAbelianizationModuleEndOfSurjective_apply
    (ψ : G →* H) (hψ : Function.Surjective ψ) (h : H) (x : KernelAbelianizationAdd ψ) :
    kernelAbelianizationModuleEndOfSurjective ψ hψ h x =
      Additive.ofMul (kernelAbelianizationConjOfSurjective ψ hψ h (Additive.toMul x)) := by
  rfl

/--
The induced \(\mathbb{Z}[H]\)-action on \((\ker \psi)^{\mathrm{ab}}\), written in additive form.
-/
def kernelAbelianizationActionRingHomOfSurjective
    (ψ : G →* H) (hψ : Function.Surjective ψ) :
    GroupRing H →+* Module.End ℤ (KernelAbelianizationAdd ψ) :=
  MonoidAlgebra.liftNCRingHom (Int.castRingHom (Module.End ℤ (KernelAbelianizationAdd ψ)))
    (kernelAbelianizationModuleEndOfSurjective ψ hψ) (by
      intro z h
      ext x
      simp only [eq_intCast, Module.End.mul_apply, kernelAbelianizationModuleEndOfSurjective_apply,
  kernelAbelianizationConjOfSurjective_eq_surjInv, Module.End.intCast_apply, toMul_zsmul,
      toMul_ofMul, map_smul])

omit [DecidableEq H] [DecidableEq G] in
/--
The surjective-case group-ring action on kernel abelianization has the displayed value on
representatives.
-/
@[simp]
theorem kernelAbelianizationActionRingHomOfSurjective_of
    (ψ : G →* H) (hψ : Function.Surjective ψ) (h : H) :
    kernelAbelianizationActionRingHomOfSurjective ψ hψ (MonoidAlgebra.of ℤ H h) =
      kernelAbelianizationModuleEndOfSurjective ψ hψ h := by
  let f := Int.castRingHom (Module.End ℤ (KernelAbelianizationAdd ψ))
  let g := kernelAbelianizationModuleEndOfSurjective ψ hψ
  have hcomm : ∀ z h, Commute (f z) (g h) := by
    intro z h
    ext x
    simp only [f, g, eq_intCast, Module.End.mul_apply,
      kernelAbelianizationModuleEndOfSurjective_apply,
      kernelAbelianizationConjOfSurjective_eq_surjInv, Module.End.intCast_apply,
      toMul_zsmul, toMul_ofMul, map_smul]
  change
    MonoidAlgebra.liftNCRingHom f g hcomm (MonoidAlgebra.single h 1) = g h
  exact
    (MonoidAlgebra.liftNCRingHom_single f g hcomm h 1).trans (by
      rw [map_one, one_mul])

/--
The \(\mathbb{Z}[H]\)-module structure on \(\ker(\psi)^{\mathrm{ab}}\) induced by surjective
conjugation.
-/
@[reducible]
def kernelAbelianizationModuleOfSurjective
    (ψ : G →* H) (hψ : Function.Surjective ψ) :
    Module (GroupRing H) (KernelAbelianizationAdd ψ) :=
  Module.compHom _ (kernelAbelianizationActionRingHomOfSurjective ψ hψ)

omit [DecidableEq H] [DecidableEq G] in
/--
For a surjective \(\psi\), the additive kernel-boundary map intertwines the induced conjugation
action with scalar multiplication by the corresponding group-ring basis element.
-/
@[simp]
theorem kernelAbelianizationBoundaryAdd_conjOfSurjective
    (ψ : G →* H) (hψ : Function.Surjective ψ) (h : H) (x : Abelianization ψ.ker) :
    kernelAbelianizationBoundaryAdd ψ
        (Additive.ofMul (kernelAbelianizationConjOfSurjective ψ hψ h x)) =
      (MonoidAlgebra.of ℤ H h : GroupRing H) •
        kernelAbelianizationBoundaryAdd ψ (Additive.ofMul x) := by
  let g : G := Function.surjInv hψ h
  have hg : ψ g = h := Function.surjInv_eq hψ h
  refine QuotientGroup.induction_on x ?_
  intro n
  rw [kernelAbelianizationConjOfSurjective_eq_surjInv]
  change kernelAbelianizationBoundaryAdd ψ
      (Additive.ofMul (kernelAbelianizationConj ψ g (Abelianization.of n))) =
    (MonoidAlgebra.of ℤ H h : GroupRing H) •
      kernelAbelianizationBoundaryAdd ψ (Additive.ofMul (Abelianization.of n))
  rw [kernelAbelianizationConj_of, kernelAbelianizationBoundaryAdd_of,
    kernelAbelianizationBoundaryAdd_of]
  simpa [g, hg, MulAut.conjNormal_apply, mul_assoc] using universalDifferential_conj_of_mem_ker
      ψ g n.1 n.2

omit [DecidableEq H] [DecidableEq G] in
/-- The kernel-boundary additive map is compatible with the surjective-case group-ring action. -/
@[simp]
theorem kernelAbelianizationBoundaryAdd_commOfSurjective
    (ψ : G →* H) (hψ : Function.Surjective ψ) (h : H) (x : KernelAbelianizationAdd ψ) :
    letI := kernelAbelianizationModuleOfSurjective ψ hψ
    kernelAbelianizationBoundaryAdd ψ ((MonoidAlgebra.of ℤ H h : GroupRing H) • x) =
      (MonoidAlgebra.of ℤ H h : GroupRing H) • kernelAbelianizationBoundaryAdd ψ x := by
  let := kernelAbelianizationModuleOfSurjective ψ hψ
  change kernelAbelianizationBoundaryAdd ψ
      ((kernelAbelianizationActionRingHomOfSurjective ψ hψ (MonoidAlgebra.of ℤ H h)) x) =
    (MonoidAlgebra.of ℤ H h : GroupRing H) • kernelAbelianizationBoundaryAdd ψ x
  rw [kernelAbelianizationActionRingHomOfSurjective_of,
    kernelAbelianizationModuleEndOfSurjective_apply]
  simpa using
    kernelAbelianizationBoundaryAdd_conjOfSurjective ψ hψ h (Additive.toMul x)

/--
The head map of the discrete Crowell sequence, in \(\mathbb{Z}[H]\)-linear form when \(\psi\) is
surjective.
-/
def kernelAbelianizationBoundaryLinearOfSurjective
    (ψ : G →* H) (hψ : Function.Surjective ψ) :
    letI := kernelAbelianizationModuleOfSurjective ψ hψ
    KernelAbelianizationAdd ψ →ₗ[GroupRing H] DifferentialModule ψ := by
  letI := kernelAbelianizationModuleOfSurjective ψ hψ
  let f : KernelAbelianizationAdd ψ →ₗ[ℤ] DifferentialModule ψ :=
    (kernelAbelianizationBoundaryAdd ψ).toIntLinearMap
  exact MonoidAlgebra.equivariantOfLinearOfComm f
    (fun h x => by
      exact kernelAbelianizationBoundaryAdd_commOfSurjective (ψ := ψ) hψ h x)

omit [DecidableEq H] [DecidableEq G] in
/--
The linear kernel-boundary map in the surjective case has the stated value on a kernel element.
-/
@[simp]
theorem kernelAbelianizationBoundaryLinearOfSurjective_of
    (ψ : G →* H) (hψ : Function.Surjective ψ) (n : ψ.ker) :
    kernelAbelianizationBoundaryLinearOfSurjective ψ hψ
        (Additive.ofMul (Abelianization.of n)) = universalDifferential ψ n.1 := by
  let := kernelAbelianizationModuleOfSurjective ψ hψ
  change kernelAbelianizationBoundaryAdd ψ (Additive.ofMul (Abelianization.of n)) =
    universalDifferential ψ n.1
  exact kernelAbelianizationBoundaryAdd_of ψ n

omit [DecidableEq H] [DecidableEq G] in
/--
The kernel-abelianization boundary map is evaluated on canonical generators and then extended
linearly.
-/
@[simp]
theorem kernelAbelianizationBoundaryLinearOfSurjective_apply
    (ψ : G →* H) (hψ : Function.Surjective ψ) (x : KernelAbelianizationAdd ψ) :
    kernelAbelianizationBoundaryLinearOfSurjective ψ hψ x =
      kernelAbelianizationBoundaryAdd ψ x := by
  let := kernelAbelianizationModuleOfSurjective ψ hψ
  rfl

omit [DecidableEq H] [DecidableEq G] in
/--
Composing the surjective-case kernel-boundary map with the group-ring map gives the expected
group-ring boundary.
-/
@[simp]
theorem toGroupRing_kernelAbelianizationBoundaryLinearOfSurjective
    (ψ : G →* H) (hψ : Function.Surjective ψ) (x : KernelAbelianizationAdd ψ) :
    toGroupRing ψ (kernelAbelianizationBoundaryLinearOfSurjective ψ hψ x) = 0 := by
  rw [kernelAbelianizationBoundaryLinearOfSurjective_apply]
  change toGroupRing ψ
      (Multiplicative.toAdd (kernelAbelianizationBoundary ψ (Additive.toMul x))) = 0
  refine QuotientGroup.induction_on (Additive.toMul x) ?_
  intro n
  change toGroupRing ψ (universalDifferential ψ n.1) = 0
  rw [FoxDifferential.toGroupRing_d, FoxDifferential.groupRingBoundary_subtype_ker]

/-- The \(A_{\psi}\)-submodule generated by the head map in the surjective case. -/
abbrev kernelAbelianizationBoundaryRangeOfSurjective
    (ψ : G →* H) (hψ : Function.Surjective ψ) :
    Submodule (GroupRing H) (DifferentialModule ψ) := by
  letI := kernelAbelianizationModuleOfSurjective ψ hψ
  exact LinearMap.range (kernelAbelianizationBoundaryLinearOfSurjective ψ hψ)


end

end FoxDifferential

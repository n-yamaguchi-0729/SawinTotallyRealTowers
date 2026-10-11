/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence
import Nyll.ProCGroups.FoxDifferential.Discrete.KernelBoundary.Basic

/-!
# Fox differential: discrete — kernel boundary — homology

The principal declarations in this module are:

- `kernelGroupRingRep`
  The left-multiplication representation of \(\ker \psi\) on \(\mathbb{Z}[G]\).
- `kernelSplitEquiv`
  A section-based decomposition G \(\simeq\) \(\ker \psi\) \(\times\) H.
- `kernelSplitEquiv_smul`
  The kernel-splitting equivalence is equivariant for the left action of \(\ker\psi\): acting by
  \(n\) before applying the equivalence is the same as acting by \(n\) afterward.
- `indBottomKernelUnderlyingEquiv_mk`
  The bottom-kernel induced-module equivalence sends the representative indexed by \(g\in\ker\psi\)
  and \(a\in \mathbb{Z}[H]\) to the tensor of the singleton at \(g\) with \(a\).
-/

namespace FoxDifferential

noncomputable section

open CategoryTheory Limits Representation Rep TensorProduct MonoidalCategory

variable {H G : Type} [Group H] [DecidableEq H] [Group G] [DecidableEq G]

section KernelGroupRing

variable {H G : Type} [Group H] [DecidableEq H] [Group G] [DecidableEq G]

variable (ψ : G →* H) (hψ : Function.Surjective ψ)

/-- The kernel-boundary codomain carries the trivial multiplication action. -/
instance instMulActionKernelCodomainTrivial : MulAction ↥(ψ.ker) H where
  smul _ h := h
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The left-multiplication representation of \(\ker \psi\) on \(\mathbb{Z}[G]\). -/
abbrev kernelGroupRingRep : Rep ℤ ↥(ψ.ker) :=
  Rep.ofMulAction ℤ ↥(ψ.ker) G

/-- A section-based decomposition G \(\simeq\) \(\ker \psi\) \(\times\) H. -/
def kernelSplitEquiv : G ≃ ↥(ψ.ker) × H where
  toFun g :=
    (⟨g * (Function.surjInv hψ (ψ g))⁻¹, by
        simp only [MonoidHom.mem_ker, map_mul, map_inv, Function.surjInv_eq hψ (ψ g),
            mul_inv_cancel]⟩, ψ g)
  invFun x := x.1.1 * Function.surjInv hψ x.2
  left_inv g := by
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  right_inv x := by
    rcases x with ⟨n, h⟩
    apply Prod.ext
    · apply Subtype.ext
      change
        n.1 * Function.surjInv hψ h *
            (Function.surjInv hψ (ψ (n.1 * Function.surjInv hψ h)))⁻¹ = n.1
      rw [map_mul, n.2, Function.surjInv_eq hψ h]
      simp only [one_mul, mul_assoc, mul_inv_cancel, mul_one]
    · change ψ (n.1 * Function.surjInv hψ h) = h
      rw [map_mul, n.2, one_mul, Function.surjInv_eq hψ h]

omit [DecidableEq H] [DecidableEq G] in
/--
The kernel-splitting equivalence is equivariant for the left action of \(\ker\psi\): acting by
\(n\) before applying the equivalence is the same as acting by \(n\) afterward.
-/
@[simp]
theorem kernelSplitEquiv_smul (n : ↥(ψ.ker)) (g : G) :
    kernelSplitEquiv ψ hψ (n • g) = n • kernelSplitEquiv ψ hψ g := by
  apply Prod.ext
  · apply Subtype.ext
    change
      n.1 * g * (Function.surjInv hψ (ψ (n.1 * g)))⁻¹ =
        n.1 * (g * (Function.surjInv hψ (ψ g))⁻¹)
    rw [map_mul, n.2, one_mul]
    simp only [mul_assoc]
  · change ψ (n.1 * g) = ψ g
    rw [map_mul, n.2, one_mul]

/--
The \(\ker \psi\)-representation on \(\mathbb{Z}[\ker \psi\] \otimes \mathbb{Z}[H]\) whose first
factor is right-regular and whose second factor is trivial.
-/
abbrev kernelRightTensorRep : Rep ℤ ↥(ψ.ker) :=
  rightRegularRep ↥(ψ.ker) ⊗ Rep.trivial ℤ ↥(ψ.ker) (H →₀ ℤ)

/--
The section decomposition, rewritten as a representation isomorphism to a right-regular tensor
model.
-/
def kernelGroupRingRepIsoRightTensor :
    kernelGroupRingRep (ψ := ψ) ≅ kernelRightTensorRep (H := H) (ψ := ψ) := by
  let e₁ :
      GroupRing G ≃ₗ[ℤ] ((↥(ψ.ker) × H) →₀ ℤ) :=
    (MonoidAlgebra.coeffLinearEquiv ℤ).trans
      (Finsupp.domLCongr (kernelSplitEquiv ψ hψ))
  let f : (↥(ψ.ker) →₀ ℤ) ≃ₗ[ℤ] GroupRing ↥(ψ.ker) :=
    (Finsupp.domLCongr (Equiv.inv ↥(ψ.ker))).trans
      (MonoidAlgebra.coeffLinearEquiv ℤ).symm
  let gEquiv : (H →₀ ℤ) ≃ₗ[ℤ] (H →₀ ℤ) :=
    LinearEquiv.refl ℤ (H →₀ ℤ)
  let e₂ :
      ((↥(ψ.ker) × H) →₀ ℤ) ≃ₗ[ℤ] (GroupRing ↥(ψ.ker)) ⊗[ℤ] (H →₀ ℤ) :=
    (finsuppTensorFinsupp' ℤ ↥(ψ.ker) H).symm.trans
      (TensorProduct.congr f gEquiv)
  have he₂_single (m : ↥(ψ.ker)) (h : H) (r : ℤ) :
      e₂ (Finsupp.single (m, h) r) =
        f (Finsupp.single m 1) ⊗ₜ[ℤ] gEquiv (Finsupp.single h r) := by
    dsimp only [e₂]
    erw [LinearEquiv.trans_apply,
      finsuppTensorFinsupp'_symm_single_eq_single_one_tmul,
      TensorProduct.congr_tmul f gEquiv]
  refine Rep.mkIso (Representation.Equiv.mk (e₁.trans e₂) ?_)
  intro n
  apply LinearMap.toAddMonoidHom_injective
  apply MonoidAlgebra.addMonoidHom_ext
  intro g r
  have hcalc :
      e₂ (Finsupp.single (n • kernelSplitEquiv ψ hψ g) r) =
        ((kernelRightTensorRep (ψ := ψ) (H := H)).ρ n)
          (e₂ (Finsupp.single (kernelSplitEquiv ψ hψ g) r)) := by
    change e₂ (Finsupp.single (n • kernelSplitEquiv ψ hψ g) r) =
      TensorProduct.map ((rightRegularRepresentation ↥(ψ.ker)) n) LinearMap.id
        (e₂ (Finsupp.single (kernelSplitEquiv ψ hψ g) r))
    cases hkg : kernelSplitEquiv ψ hψ g with
    | mk m h =>
        have hnm :
            f (Finsupp.single (n * m) (1 : ℤ)) =
              MonoidAlgebra.single ((n * m)⁻¹) (1 : ℤ) := by
          ext x
          simp only [f, LinearEquiv.trans_apply, Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
            Finsupp.equivMapDomain_single, Equiv.inv_apply, mul_inv_rev,
            MonoidAlgebra.coeffLinearEquiv_symm_apply, MonoidAlgebra.coeff_single]
        have hm :
            f (Finsupp.single m (1 : ℤ)) =
              MonoidAlgebra.single m⁻¹ (1 : ℤ) := by
          ext x
          simp only [f, LinearEquiv.trans_apply, Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
            Finsupp.equivMapDomain_single, Equiv.inv_apply,
            MonoidAlgebra.coeffLinearEquiv_symm_apply, MonoidAlgebra.coeff_single]
        rw [show n • (m, h) = (n * m, h) by rfl]
        rw [he₂_single, he₂_single]
        erw [TensorProduct.map_tmul
          ((rightRegularRepresentation ↥(ψ.ker)) n) LinearMap.id]
        dsimp only [gEquiv, LinearEquiv.refl_apply, LinearMap.id_coe, id_eq]
        rw [hnm, hm]
        simp only [mul_inv_rev, rightRegularRepresentation_apply_single]
  change
    e₂
        (e₁
          (((kernelGroupRingRep (ψ := ψ)).ρ n) (MonoidAlgebra.single g r))) =
      ((kernelRightTensorRep (ψ := ψ) (H := H)).ρ n)
        (e₂ (e₁ (MonoidAlgebra.single g r)))
  simpa [kernelGroupRingRep, kernelRightTensorRep, e₁,
    LinearEquiv.trans_apply, kernelSplitEquiv_smul, MonoidAlgebra.coeffLinearEquiv_apply,
    Representation.ofMulAction_single, Rep.tensor_ρ] using hcalc

/--
The trivial representation of the trivial subgroup of \(\ker \psi\) on the free
\(\mathbb{Z}\)-module \(\mathbb{Z}[H]\).
-/
def indBottomKernelUnderlyingEquiv :
    Representation.IndV (⊥ : Subgroup ↥(ψ.ker)).subtype
      (Rep.trivial ℤ (⊥ : Subgroup ↥(ψ.ker)) (H →₀ ℤ)).ρ
      ≃ₗ[ℤ] (GroupRing ↥(ψ.ker)) ⊗[ℤ] (H →₀ ℤ) := by
  let ρt :
      Representation ℤ (⊥ : Subgroup ↥(ψ.ker))
        (TensorProduct ℤ (GroupRing ↥(ψ.ker)) (H →₀ ℤ)) :=
    Representation.tprod
      (((Rep.leftRegular ℤ ↥(ψ.ker)).ρ.comp (⊥ : Subgroup ↥(ψ.ker)).subtype))
      (Rep.trivial ℤ (⊥ : Subgroup ↥(ψ.ker)) (H →₀ ℤ)).ρ
  exact coinvariantsLEquivOfSubsingleton ρt

omit [DecidableEq H] [DecidableEq G] in
/--
The bottom-kernel induced-module equivalence sends the representative indexed by
\(g\in\ker\psi\) and \(a\in \mathbb{Z}[H]\) to the tensor of the singleton at \(g\) with \(a\).
-/
@[simp 900]
theorem indBottomKernelUnderlyingEquiv_mk (g : ↥(ψ.ker)) (a : H →₀ ℤ) :
    indBottomKernelUnderlyingEquiv (H := H) (ψ := ψ)
      (Representation.IndV.mk (⊥ : Subgroup ↥(ψ.ker)).subtype
        (Rep.trivial ℤ (⊥ : Subgroup ↥(ψ.ker)) (H →₀ ℤ)).ρ g a) =
        MonoidAlgebra.single g 1 ⊗ₜ[ℤ] a := by
  change
      (Representation.Coinvariants.lift
          (Representation.tprod
            (((Rep.leftRegular ℤ ↥(ψ.ker)).ρ.comp (⊥ : Subgroup ↥(ψ.ker)).subtype))
            (Rep.trivial ℤ (⊥ : Subgroup ↥(ψ.ker)) (H →₀ ℤ)).ρ)
          LinearMap.id
          (fun x => by
            ext y
            have : x = (1 : (⊥ : Subgroup ↥(ψ.ker))) := Subsingleton.elim _ _
            subst this
            simp only [map_one, LinearMap.id_comp, Module.End.one_apply,
              LinearMap.id_coe, id_eq]))
        (Representation.Coinvariants.mk _
          ((MonoidAlgebra.single g 1 : GroupRing ↥(ψ.ker)) ⊗ₜ[ℤ] a)) = _
  rw [Representation.Coinvariants.lift_mk]
  rfl

/-- \(\operatorname{Ind}_{1}^{\ker \psi}(\mathbb{Z}[H])\) is the right-regular tensor model. -/
def indBottomKernelIsoRightTensor :
    Rep.ind (⊥ : Subgroup ↥(ψ.ker)).subtype
        (Rep.trivial ℤ (⊥ : Subgroup ↥(ψ.ker)) (H →₀ ℤ)) ≅
      kernelRightTensorRep (ψ := ψ) (H := H) := by
  refine Rep.mkIso (Representation.Equiv.mk
    (indBottomKernelUnderlyingEquiv (H := H) (ψ := ψ)) ?_)
  intro g
  apply Representation.IndV.hom_ext (φ := (⊥ : Subgroup ↥(ψ.ker)).subtype)
    (ρ := (Rep.trivial ℤ (⊥ : Subgroup ↥(ψ.ker)) (H →₀ ℤ)).ρ)
  · intro h
    apply LinearMap.ext
    intro a
    change
      indBottomKernelUnderlyingEquiv (H := H) (ψ := ψ)
        (((Rep.ind (⊥ : Subgroup ↥(ψ.ker)).subtype
            (Rep.trivial ℤ (⊥ : Subgroup ↥(ψ.ker)) (H →₀ ℤ))).ρ g)
          ((Representation.IndV.mk (⊥ : Subgroup ↥(ψ.ker)).subtype
            (Rep.trivial ℤ (⊥ : Subgroup ↥(ψ.ker)) (H →₀ ℤ)).ρ h) a)) =
        ((kernelRightTensorRep (ψ := ψ) (H := H)).ρ g)
          (indBottomKernelUnderlyingEquiv (H := H) (ψ := ψ)
            ((Representation.IndV.mk (⊥ : Subgroup ↥(ψ.ker)).subtype
              (Rep.trivial ℤ (⊥ : Subgroup ↥(ψ.ker)) (H →₀ ℤ)).ρ h) a))
    have hind :
        (((Rep.ind (⊥ : Subgroup ↥(ψ.ker)).subtype
            (Rep.trivial ℤ (⊥ : Subgroup ↥(ψ.ker)) (H →₀ ℤ))).ρ g)
          ((Representation.IndV.mk (⊥ : Subgroup ↥(ψ.ker)).subtype
            (Rep.trivial ℤ (⊥ : Subgroup ↥(ψ.ker)) (H →₀ ℤ)).ρ h) a)) =
        (Representation.IndV.mk (⊥ : Subgroup ↥(ψ.ker)).subtype
          (Rep.trivial ℤ (⊥ : Subgroup ↥(ψ.ker)) (H →₀ ℤ)).ρ (h * g⁻¹)) a := by
      exact Representation.ind_mk
        (φ := (⊥ : Subgroup ↥(ψ.ker)).subtype)
        (ρ := (Rep.trivial ℤ (⊥ : Subgroup ↥(ψ.ker)) (H →₀ ℤ)).ρ) g h a
    rw [hind, indBottomKernelUnderlyingEquiv_mk, indBottomKernelUnderlyingEquiv_mk]
    change MonoidAlgebra.single (h * g⁻¹) 1 ⊗ₜ[ℤ] a =
      TensorProduct.map ((rightRegularRepresentation ↥(ψ.ker)) g) LinearMap.id
        (MonoidAlgebra.single h 1 ⊗ₜ[ℤ] a)
    simp only [map_tmul, rightRegularRepresentation_apply_single, LinearMap.id_coe, id_eq]

end KernelGroupRing

section KernelAugmentation

variable {H G : Type} [Group H] [DecidableEq H] [Group G] [DecidableEq G]

variable (ψ : G →* H)

/-- The left-regular representation of \(G\) on \(\mathbb{Z}[G]\). -/
abbrev groupRingRep : Rep ℤ G :=
  Rep.ofMulAction ℤ G G

omit [DecidableEq G] in
/--
The group-ring representation sends a singleton basis element to the singleton at the product.
-/
@[simp]
theorem groupRingRep_apply_single (g h : G) (m : ℤ) :
    ((groupRingRep (G := G)).ρ g) (MonoidAlgebra.single h m) =
      MonoidAlgebra.single (g * h) m := by
  exact Representation.ofMulAction_single (k := ℤ) (G := G) (H := G) g h m

omit [DecidableEq H] [DecidableEq G] in
/--
The kernel group-ring representation sends a singleton basis element to the singleton at the
product.
-/
@[simp]
theorem kernelGroupRingRep_apply_single (n : ψ.ker) (g : G) (m : ℤ) :
    ((kernelGroupRingRep (ψ := ψ)).ρ n) (MonoidAlgebra.single g m) =
      MonoidAlgebra.single (n • g) m := by
  exact Representation.ofMulAction_single (k := ℤ) (G := ↥(ψ.ker)) (H := G) n g m

omit [DecidableEq H] [DecidableEq G] in
/-- The left-regular group-ring representation preserves the augmentation-kernel condition. -/
theorem augmentation_kernelGroupRingRep
    (n : ψ.ker) (x : GroupRing G) :
    augmentation G (((kernelGroupRingRep (ψ := ψ)).ρ n) x) = augmentation G x := by
  let F : GroupRing G →ₗ[ℤ] ℤ :=
    ((augmentation G).toAddMonoidHom.toIntLinearMap).comp ((kernelGroupRingRep (ψ := ψ)).ρ n)
  have hF : F = (augmentation G).toAddMonoidHom.toIntLinearMap := by
    apply LinearMap.toAddMonoidHom_injective
    apply MonoidAlgebra.addMonoidHom_ext
    intro g m
    change augmentation G (((kernelGroupRingRep (ψ := ψ)).ρ n)
      (MonoidAlgebra.single g m)) = augmentation G (MonoidAlgebra.single g m)
    rw [kernelGroupRingRep_apply_single]
    simp only [augmentation, augmentationAlgHom,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MonoidAlgebra.lift_single,
      MonoidHom.one_apply, Int.zsmul_eq_mul, mul_one]
  exact LinearMap.congr_fun hF x

omit [DecidableEq G] in
/-- Left multiplication by \(g : G\) preserves the group-ring augmentation. -/
theorem augmentation_groupRingRep
    (g : G) (x : GroupRing G) :
    augmentation G (((groupRingRep (G := G)).ρ g) x) = augmentation G x := by
  let F : GroupRing G →ₗ[ℤ] ℤ :=
    ((augmentation G).toAddMonoidHom.toIntLinearMap).comp ((groupRingRep (G := G)).ρ g)
  have hF : F = (augmentation G).toAddMonoidHom.toIntLinearMap := by
    apply LinearMap.toAddMonoidHom_injective
    apply MonoidAlgebra.addMonoidHom_ext
    intro h m
    change augmentation G (((groupRingRep (G := G)).ρ g)
      (MonoidAlgebra.single h m)) = augmentation G (MonoidAlgebra.single h m)
    rw [groupRingRep_apply_single]
    simp only [augmentation, augmentationAlgHom,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MonoidAlgebra.lift_single,
      MonoidHom.one_apply, Int.zsmul_eq_mul, mul_one]
  exact LinearMap.congr_fun hF x

/-- The left-regular G-action preserves the augmentation ideal \(I(\mathbb{Z}[G])\). -/
abbrev groupAugmentationIdealRep : Rep ℤ G :=
  Rep.of (X := augmentationIdeal G)
    { toFun := fun g =>
        { toFun := fun x =>
            ⟨((groupRingRep (G := G)).ρ g) x.1, by
              rw [mem_augmentationIdeal_iff]
              rw [augmentation_groupRingRep (G := G) g x.1]
              exact (mem_augmentationIdeal_iff (H := G) (x := x.1)).1 x.2⟩
          map_add' := by
            intro x y
            apply Subtype.ext
            exact map_add ((groupRingRep (G := G)).ρ g) x.1 y.1
          map_smul' := by
            intro m x
            apply Subtype.ext
            exact map_smul ((groupRingRep (G := G)).ρ g) m x.1 }
      map_one' := by
        ext x h
        simp only [groupRingRep, map_one, Module.End.one_apply, Subtype.coe_eta,
          LinearMap.coe_mk, AddHom.coe_mk]
      map_mul' := by
        intro g₁ g₂
        ext x h
        simp only [groupRingRep, map_mul, Module.End.mul_apply, LinearMap.coe_mk,
          AddHom.coe_mk]}

/-- The kernel-restricted action of \(\ker \psi\) on the augmentation ideal \(I(\mathbb{Z}[G])\). -/
abbrev kernelAugmentationIdealRep : Rep ℤ ↥(ψ.ker) :=
  Rep.of (X := augmentationIdeal G)
    { toFun := fun n =>
        { toFun := fun x =>
            ⟨((kernelGroupRingRep (ψ := ψ)).ρ n) x.1, by
              rw [mem_augmentationIdeal_iff]
              rw [augmentation_kernelGroupRingRep (ψ := ψ) n x.1]
              exact (mem_augmentationIdeal_iff (H := G) (x := x.1)).1 x.2⟩
          map_add' := by
            intro x y
            apply Subtype.ext
            exact map_add ((kernelGroupRingRep (ψ := ψ)).ρ n) x.1 y.1
          map_smul' := by
            intro m x
            apply Subtype.ext
            exact map_smul ((kernelGroupRingRep (ψ := ψ)).ρ n) m x.1 }
      map_one' := by
        ext x g
        simp only [kernelGroupRingRep, map_one, Module.End.one_apply, Subtype.coe_eta,
          LinearMap.coe_mk, AddHom.coe_mk]
      map_mul' := by
        intro n₁ n₂
        ext x g
        simp only [kernelGroupRingRep, map_mul, Module.End.mul_apply, LinearMap.coe_mk,
          AddHom.coe_mk]}

/--
The inclusion \(I(\mathbb{Z}[G])\hookrightarrow \mathbb{Z}[G]\) as a morphism of \(\ker
\psi\)-representations.
-/
def kernelAugmentationIdealInclusion :
    kernelAugmentationIdealRep (ψ := ψ) ⟶ kernelGroupRingRep (ψ := ψ) :=
  Rep.ofHom <| Representation.IntertwiningMap.mk
    ((augmentationIdeal G).subtype.restrictScalars ℤ) fun _ => rfl

/--
The augmentation map \(\mathbb{Z}[G] \to \mathbb{Z}\) as a morphism of \(\ker
\psi\)-representations.
-/
def kernelGroupRingAugmentation :
    kernelGroupRingRep (ψ := ψ) ⟶ Rep.trivial ℤ ↥(ψ.ker) ℤ :=
  Rep.ofHom <| Representation.IntertwiningMap.mk
    ((augmentation G).toAddMonoidHom.toIntLinearMap) fun n => by
      apply LinearMap.toAddMonoidHom_injective
      apply MonoidAlgebra.addMonoidHom_ext
      intro g m
      change augmentation G (((kernelGroupRingRep (ψ := ψ)).ρ n)
          (MonoidAlgebra.single g m)) =
        ((Rep.trivial ℤ ↥(ψ.ker) ℤ).ρ n) (augmentation G (MonoidAlgebra.single g m))
      rw [kernelGroupRingRep_apply_single]
      simp only [augmentation, augmentationAlgHom,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MonoidAlgebra.lift_single,
        MonoidHom.one_apply, Int.zsmul_eq_mul, mul_one, isTrivial_def, LinearMap.id_coe, id_eq]

/--
The augmentation ideal \(I(\mathbb{Z}[G])\), the group ring \(\mathbb{Z}[G]\), and the
augmentation \(\mathbb{Z}[G]\to\mathbb{Z}\) form the short complex \(0\to
I(\mathbb{Z}[G])\to\mathbb{Z}[G]\to\mathbb{Z}\to 0\) of \(\ker \psi\)-representations.
-/
def kernelAugmentationShortComplex :
    CategoryTheory.ShortComplex (Rep ℤ ↥(ψ.ker)) :=
  CategoryTheory.ShortComplex.mk
    (kernelAugmentationIdealInclusion (ψ := ψ))
    (kernelGroupRingAugmentation (ψ := ψ))
    (by
      ext x
      exact x.2)

omit [DecidableEq H] [DecidableEq G] in
/--
The kernel-augmentation short complex is exact: the augmentation ideal maps onto the kernel of
the group-ring augmentation.
-/
theorem kernelAugmentationShortComplex_exact :
    (kernelAugmentationShortComplex (ψ := ψ)).Exact := by
  let repIntModule (A : Rep.{0} ℤ ↥(ψ.ker)) : Module ℤ A := A.hV2
  apply (forget₂ (Rep.{0} ℤ ↥(ψ.ker)) (ModuleCat ℤ)).reflects_exact_of_faithful
  rw [CategoryTheory.ShortComplex.moduleCat_exact_iff_range_eq_ker]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    change augmentation G x = 0 at hx
    refine ⟨⟨x, ?_⟩, rfl⟩
    exact (mem_augmentationIdeal_iff (H := G) (x := (show GroupRing G from x))).2 hx

omit [DecidableEq H] [DecidableEq G] in
/--
The canonical augmentation sequence with augmentation ideal as kernel is short exact: the
inclusion is injective, its image is the kernel of augmentation, and the augmentation is
surjective.
-/
theorem kernelAugmentationShortExact :
    (kernelAugmentationShortComplex (ψ := ψ)).ShortExact := by
  have : Mono (kernelAugmentationShortComplex (ψ := ψ)).f := by
    change Mono (kernelAugmentationIdealInclusion (ψ := ψ))
    exact (Rep.mono_iff_injective _).2 fun x y h => by
      apply Subtype.ext
      exact h
  have : Epi (kernelAugmentationShortComplex (ψ := ψ)).g := by
    change Epi (kernelGroupRingAugmentation (ψ := ψ))
    exact (Rep.epi_iff_surjective _).2 <| by
      intro m
      refine ⟨(m : GroupRing G), ?_⟩
      change augmentation G (m : GroupRing G) = m
      rw [map_intCast]
      rfl
  refine CategoryTheory.ShortComplex.ShortExact.mk
    (S := kernelAugmentationShortComplex (ψ := ψ))
    (exact := kernelAugmentationShortComplex_exact (ψ := ψ))

/-- The trivial integral representation of \(\ker\psi\). -/
abbrev kernelTrivialIntRep : Rep ℤ ↥(ψ.ker) :=
  Rep.trivial ℤ ↥(ψ.ker) ℤ

/--
The connecting homomorphism \(H_1(\ker \psi, \mathbb{Z})\) \(\to\) \(H_0(\ker \psi,
I(\mathbb{Z}[G]))\) attached to the short exact sequence 0 \(\to\) \(I(\mathbb{Z}[G])\) \(\to\)
\(\mathbb{Z}[G]\) \(\to\) \(\mathbb{Z}\) \(\to\) 0 of \(\ker \psi\)-representations.
-/
def kernelAugmentationConnecting :
    groupHomology (kernelTrivialIntRep (ψ := ψ)) 1 ⟶
      groupHomology (kernelAugmentationIdealRep (ψ := ψ)) 0 :=
  groupHomology.δ
    (X := kernelAugmentationShortComplex (ψ := ψ))
    (kernelAugmentationShortExact (ψ := ψ))
    1 0 rfl

/--
The standard low-degree identification \(H_1(\ker \psi, \mathbb{Z}) \simeq (\ker
\psi)^{\mathrm{ab}}\).
-/
def kernelTrivialH1AddEquivAbelianization :
    groupHomology (kernelTrivialIntRep (ψ := ψ)) 1 ≃+
      Additive (Abelianization ψ.ker) :=
  (groupHomology.H1AddEquivOfIsTrivial (kernelTrivialIntRep (ψ := ψ))).trans
    (TensorProduct.rid ℤ (Additive (Abelianization ψ.ker))).toAddEquiv

omit [DecidableEq H] [DecidableEq G] in
/--
The inverse of the \(H_1\)-abelianization equivalence sends the abelianization class of
\(n\in\ker\psi\) to the degree-one homology class represented by the singleton cycle at \(n\).
-/
@[simp]
theorem kernelTrivialH1AddEquivAbelianization_symm_of (n : ψ.ker) :
    (kernelTrivialH1AddEquivAbelianization (ψ := ψ)).symm
        (Additive.ofMul (Abelianization.of n)) =
      groupHomology.H1π (kernelTrivialIntRep (ψ := ψ))
        ((groupHomology.cycles₁IsoOfIsTrivial (kernelTrivialIntRep (ψ := ψ))).inv
          (Finsupp.single n 1)) := by
  unfold kernelTrivialH1AddEquivAbelianization
  rw [AddEquiv.symm_trans_apply]
  simpa [TensorProduct.rid_symm_apply] using
    (groupHomology.H1AddEquivOfIsTrivial_symm_tmul
      (A := kernelTrivialIntRep (ψ := ψ)) n (1 : ℤ))

omit [DecidableEq H] [DecidableEq G] in
/--
The connecting morphism sends a boundary cycle to the corresponding augmentation-coinvariant
class.
-/
theorem kernelAugmentationConnecting_boundaryCycle_of (n : ψ.ker) :
    Finsupp.mapRange.linearMap (kernelAugmentationShortComplex (ψ := ψ)).g.hom.toLinearMap
      (Finsupp.single n (MonoidAlgebra.single n.1 (1 : ℤ))) =
    ((groupHomology.cycles₁IsoOfIsTrivial (kernelTrivialIntRep (ψ := ψ))).inv
      (Finsupp.single n 1)).1 := by
  change
    Finsupp.mapRange.linearMap (kernelGroupRingAugmentation (ψ := ψ)).hom.toLinearMap
      (Finsupp.single n (MonoidAlgebra.single n.1 (1 : ℤ))) =
    (Finsupp.single n (1 : ℤ))
  rw [show
      (Finsupp.mapRange.linearMap (kernelGroupRingAugmentation (ψ := ψ)).hom.toLinearMap)
          (Finsupp.single n (MonoidAlgebra.single n.1 (1 : ℤ))) =
        Finsupp.mapRange (kernelGroupRingAugmentation (ψ := ψ)).hom.toLinearMap
          ((kernelGroupRingAugmentation (ψ := ψ)).hom.toLinearMap.map_zero)
          (Finsupp.single n (MonoidAlgebra.single n.1 (1 : ℤ))) by
        rfl]
  rw [Finsupp.mapRange_single]
  have hcoeff :
      (kernelGroupRingAugmentation (ψ := ψ)).hom.toLinearMap
        (MonoidAlgebra.single n.1 (1 : ℤ)) = 1 := by
    change augmentation G (MonoidAlgebra.single n.1 (1 : ℤ)) = 1
    simp only [augmentation, augmentationAlgHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
  MonoidAlgebra.lift_single, MonoidHom.one_apply, Int.zsmul_eq_mul, mul_one]
  simpa using congrArg (Finsupp.single n) hcoeff

omit [DecidableEq H] [DecidableEq G] in
/-- The connecting morphism has the displayed representative on a boundary element. -/
theorem kernelAugmentationConnecting_boundaryElement_of (n : ψ.ker) :
    (kernelAugmentationShortComplex (ψ := ψ)).f.hom
      (-(augmentationGeneratorSubtype (H := G) n.1)) =
    groupHomology.d₁₀ (kernelGroupRingRep (ψ := ψ))
      (Finsupp.single n (MonoidAlgebra.single n.1 (1 : ℤ))) := by
  have hn : (n⁻¹ : ψ.ker) • n.1 = (1 : G) := by
    change n.1⁻¹ * n.1 = 1
    simp only [inv_mul_cancel]
  change (-(augmentationGenerator (H := G) n.1) : GroupRing G) =
    groupHomology.d₁₀ (kernelGroupRingRep (ψ := ψ))
      (Finsupp.single n (MonoidAlgebra.single n.1 (1 : ℤ)))
  rw [groupHomology.d₁₀_single, kernelGroupRingRep_apply_single, hn]
  unfold augmentationGenerator
  change (-(MonoidAlgebra.single n.1 (1 : ℤ) -
      MonoidAlgebra.single (1 : G) (1 : ℤ)) : GroupRing G) =
    MonoidAlgebra.single (1 : G) (1 : ℤ) - MonoidAlgebra.single n.1 (1 : ℤ)
  simp only [sub_eq_add_neg]
  rw [neg_add, neg_neg]
  change -MonoidAlgebra.single n.1 (1 : ℤ) + MonoidAlgebra.single (1 : G) (1 : ℤ) =
    MonoidAlgebra.single (1 : G) (1 : ℤ) + -MonoidAlgebra.single n.1 (1 : ℤ)
  abel_nf

omit [DecidableEq H] [DecidableEq G] in
/-- The connecting morphism matches the corresponding degree-zero coinvariant class. -/
theorem kernelAugmentationConnecting_H0Iso_of (n : ψ.ker) :
    (groupHomology.H0Iso (kernelAugmentationIdealRep (ψ := ψ))).hom.hom
      ((kernelAugmentationConnecting (ψ := ψ)).hom
        ((kernelTrivialH1AddEquivAbelianization (ψ := ψ)).symm
          (Additive.ofMul (Abelianization.of n)))) =
      -Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
          (augmentationGeneratorSubtype (H := G) n.1) := by
  rw [kernelTrivialH1AddEquivAbelianization_symm_of (ψ := ψ) n]
  have hδ :
      (kernelAugmentationConnecting (ψ := ψ)).hom
        ((groupHomology.H1π (kernelTrivialIntRep (ψ := ψ))).hom
          ((groupHomology.cycles₁IsoOfIsTrivial (kernelTrivialIntRep (ψ := ψ))).inv
            (Finsupp.single n 1))) =
      (groupHomology.H0π (kernelAugmentationIdealRep (ψ := ψ))).hom
        (-(augmentationGeneratorSubtype (H := G) n.1)) := by
    exact
      groupHomology.δ₀_apply
        (hX := kernelAugmentationShortExact (ψ := ψ))
        (z := (groupHomology.cycles₁IsoOfIsTrivial (kernelTrivialIntRep (ψ := ψ))).inv
          (Finsupp.single n 1))
        (y := Finsupp.single n (MonoidAlgebra.single n.1 (1 : ℤ)))
        (x := -(augmentationGeneratorSubtype (H := G) n.1))
        (kernelAugmentationConnecting_boundaryCycle_of (ψ := ψ) n)
        (kernelAugmentationConnecting_boundaryElement_of (ψ := ψ) n)
  have hδ' := congrArg
      ((groupHomology.H0Iso (kernelAugmentationIdealRep (ψ := ψ))).hom.hom) hδ
  have hδ'' :
      (groupHomology.H0Iso (kernelAugmentationIdealRep (ψ := ψ))).hom.hom
        ((kernelAugmentationConnecting (ψ := ψ)).hom
          ((groupHomology.H1π (kernelTrivialIntRep (ψ := ψ))).hom
            ((groupHomology.cycles₁IsoOfIsTrivial (kernelTrivialIntRep (ψ := ψ))).inv
              (Finsupp.single n 1)))) =
      (groupHomology.H0Iso (kernelAugmentationIdealRep (ψ := ψ))).hom.hom
        ((groupHomology.H0π (kernelAugmentationIdealRep (ψ := ψ))).hom
          (-(augmentationGeneratorSubtype (H := G) n.1))) := by
    exact hδ'
  calc
    (groupHomology.H0Iso (kernelAugmentationIdealRep (ψ := ψ))).hom.hom
        ((kernelAugmentationConnecting (ψ := ψ)).hom
          ((groupHomology.H1π (kernelTrivialIntRep (ψ := ψ))).hom
            ((groupHomology.cycles₁IsoOfIsTrivial (kernelTrivialIntRep (ψ := ψ))).inv
              (Finsupp.single n 1))))
        =
      (groupHomology.H0Iso (kernelAugmentationIdealRep (ψ := ψ))).hom.hom
        ((groupHomology.H0π (kernelAugmentationIdealRep (ψ := ψ))).hom
          (-(augmentationGeneratorSubtype (H := G) n.1))) := hδ''
    _ = ((coinvariantsMk ℤ ↥ψ.ker).app (kernelAugmentationIdealRep (ψ := ψ)))
          (-(augmentationGeneratorSubtype (H := G) n.1)) := by
          exact
            (groupHomology.H0π_comp_H0Iso_hom_apply
              (A := kernelAugmentationIdealRep (ψ := ψ))
              (x := -(augmentationGeneratorSubtype (H := G) n.1)))
    _ = -Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
          (augmentationGeneratorSubtype (H := G) n.1) := by
          rfl

omit [DecidableEq H] [DecidableEq G] in
/-- The kernel-augmentation connecting map is injective. -/
theorem kernelAugmentationConnecting_injective
    (hψ : Function.Surjective ψ) :
    Function.Injective (kernelAugmentationConnecting (ψ := ψ)).hom := by
  let : Mono (kernelAugmentationConnecting (ψ := ψ)) := by
    let hH1 : Limits.IsZero (groupHomology (kernelGroupRingRep (ψ := ψ)) 1) := by
      classical
      let hrt : Limits.IsZero (groupHomology (kernelRightTensorRep (ψ := ψ) (H := H)) 1) :=
        let hbot : Limits.IsZero
            (groupHomology (Rep.trivial ℤ (⊥ : Subgroup ↥(ψ.ker)) (H →₀ ℤ)) 1) := by
          simpa using
            (isZero_groupHomology_succ_of_subsingleton
              (A := Rep.trivial ℤ (⊥ : Subgroup ↥(ψ.ker)) (H →₀ ℤ)) 0)
        hbot.of_iso <|
          (groupHomologyIsoOfRepIso (H := ↥(ψ.ker))
            (indBottomKernelIsoRightTensor (H := H) (ψ := ψ)).symm 1) ≪≫
          groupHomology.indIso (⊥ : Subgroup ↥(ψ.ker))
            (Rep.trivial ℤ (⊥ : Subgroup ↥(ψ.ker)) (H →₀ ℤ)) 1
      exact hrt.of_iso
        (groupHomologyIsoOfRepIso (H := ↥(ψ.ker))
          (kernelGroupRingRepIsoRightTensor (H := H) (ψ := ψ) hψ) 1)
    exact groupHomology.mono_δ_of_isZero
      (X := kernelAugmentationShortComplex (ψ := ψ))
      (kernelAugmentationShortExact (ψ := ψ))
      0
      hH1
  exact (ModuleCat.mono_iff_injective _).1 inferInstance

/--
The coinvariants of the kernel augmentation ideal are formed from the ordinary group-ring
augmentation ideal.
-/
abbrev KernelAugmentationIdealCoinvariants (ψ : G →* H) : Type _ :=
  Representation.Coinvariants ((kernelAugmentationIdealRep (ψ := ψ)).ρ)

local instance instKernelAugmentationIdealCoinvariantsIntModule :
    Module ℤ (KernelAugmentationIdealCoinvariants (ψ := ψ)) :=
  Representation.Coinvariants.instModule ((kernelAugmentationIdealRep (ψ := ψ)).ρ)

omit [DecidableEq H] [DecidableEq G] in
/--
The kernel augmentation-ideal representative agrees with the corresponding group
augmentation-ideal representative.
-/
@[simp 900]
theorem kernelAugmentationIdealRep_rho_eq_groupAugmentationIdealRep_rho
    (n : ψ.ker) :
    (kernelAugmentationIdealRep (ψ := ψ)).ρ n =
      (groupAugmentationIdealRep (G := G)).ρ n.1 := by
  ext x
  rfl

section CoinvariantsAction

/-- The \(H\)-action on \(H_0(\ker \psi, I(\mathbb{Z}[G]))\), built from a surjective section. -/
def kernelAugmentationIdealCoinvariantsEndOfSurjective
    (hψ : Function.Surjective ψ) (h : H) :
    KernelAugmentationIdealCoinvariants (ψ := ψ) →ₗ[ℤ]
      KernelAugmentationIdealCoinvariants (ψ := ψ) :=
  Representation.Coinvariants.lift ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
    ((Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)).comp
      ((groupAugmentationIdealRep (G := G)).ρ (Function.surjInv hψ h)))
    (by
      intro n
      ext x
      let s : G := Function.surjInv hψ h
      have hs : ψ s = h := by
        simpa [s] using Function.surjInv_eq hψ h
      let n' : ψ.ker := ⟨s * n.1 * s⁻¹, by
        change ψ (s * n.1 * s⁻¹) = 1
        rw [map_mul, map_mul, n.2, map_inv, hs]
        simp only [mul_one, mul_inv_cancel]⟩
      have hs_mul :
          ((groupAugmentationIdealRep (G := G)).ρ s)
              (((groupAugmentationIdealRep (G := G)).ρ n.1) x) =
            ((groupAugmentationIdealRep (G := G)).ρ (s * n.1)) x := by
        exact congrArg
          (fun f : augmentationIdeal G →ₗ[ℤ] augmentationIdeal G => f x)
          (((groupAugmentationIdealRep (G := G)).ρ).map_mul s n.1).symm
      have hs'_mul :
          ((groupAugmentationIdealRep (G := G)).ρ n'.1)
              (((groupAugmentationIdealRep (G := G)).ρ s) x) =
            ((groupAugmentationIdealRep (G := G)).ρ (n'.1 * s)) x := by
        exact congrArg
          (fun f : augmentationIdeal G →ₗ[ℤ] augmentationIdeal G => f x)
          (((groupAugmentationIdealRep (G := G)).ρ).map_mul n'.1 s).symm
      calc
        Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
            (((groupAugmentationIdealRep (G := G)).ρ s)
              (((kernelAugmentationIdealRep (ψ := ψ)).ρ n) x))
            = Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
                (((groupAugmentationIdealRep (G := G)).ρ s)
                  (((groupAugmentationIdealRep (G := G)).ρ n.1) x)) := by
                    rw [kernelAugmentationIdealRep_rho_eq_groupAugmentationIdealRep_rho
                      (ψ := ψ) n]
        _ = Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
              (((groupAugmentationIdealRep (G := G)).ρ (s * n.1)) x) := by
                rw [hs_mul]
        _ = Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
              (((groupAugmentationIdealRep (G := G)).ρ (n'.1 * s)) x) := by
                congr 1
                simp only [MonoidHom.coe_mk, OneHom.coe_mk, map_mul, Module.End.mul_apply,
                    LinearMap.coe_mk,
  AddHom.coe_mk, mul_assoc, inv_mul_cancel, mul_one, s, n']
        _ = Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
              (((groupAugmentationIdealRep (G := G)).ρ n'.1)
                (((groupAugmentationIdealRep (G := G)).ρ s) x)) := by
                  rw [hs'_mul]
        _ = Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
              (((kernelAugmentationIdealRep (ψ := ψ)).ρ n')
                (((groupAugmentationIdealRep (G := G)).ρ s) x)) := by
                  rw [kernelAugmentationIdealRep_rho_eq_groupAugmentationIdealRep_rho
                    (ψ := ψ) n']
        _ = Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
              (((groupAugmentationIdealRep (G := G)).ρ s) x) := by
                exact Representation.Coinvariants.mk_self_apply
                  ((kernelAugmentationIdealRep (ψ := ψ)).ρ) n'
                  (((groupAugmentationIdealRep (G := G)).ρ s) x))

omit [DecidableEq H] [DecidableEq G] in
/--
The surjective-case endomorphism of kernel augmentation coinvariants is evaluated on
representatives.
-/
@[simp 900]
theorem kernelAugmentationIdealCoinvariantsEndOfSurjective_mk
    (hψ : Function.Surjective ψ) (h : H) (x : augmentationIdeal G) :
    kernelAugmentationIdealCoinvariantsEndOfSurjective (ψ := ψ) hψ h
        (Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ) x) =
      Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
        (((groupAugmentationIdealRep (G := G)).ρ (Function.surjInv hψ h)) x) := by
  rfl

/--
In the surjective case, the \(H\)-action on \(H_0(\ker\psi, I(\mathbb{Z}[G]))\) is bundled as
linear endomorphisms.
-/
def kernelAugmentationIdealCoinvariantsModuleEndOfSurjective
    (hψ : Function.Surjective ψ) :
    H →* Module.End ℤ (KernelAugmentationIdealCoinvariants (ψ := ψ)) where
  toFun h := kernelAugmentationIdealCoinvariantsEndOfSurjective (ψ := ψ) hψ h
  map_one' := by
    apply Representation.Coinvariants.hom_ext
    ext x
    rw [LinearMap.comp_apply]
    rw [kernelAugmentationIdealCoinvariantsEndOfSurjective_mk (ψ := ψ) hψ]
    let n : ψ.ker := ⟨Function.surjInv hψ (1 : H), by
      simpa using Function.surjInv_eq hψ (1 : H)⟩
    rw [← kernelAugmentationIdealRep_rho_eq_groupAugmentationIdealRep_rho
      (ψ := ψ) n]
    simpa [n] using
      (Representation.Coinvariants.mk_self_apply ((kernelAugmentationIdealRep (ψ := ψ)).ρ) n x)
  map_mul' h₁ h₂ := by
    apply Representation.Coinvariants.hom_ext
    ext x
    let s₁ : G := Function.surjInv hψ h₁
    let s₂ : G := Function.surjInv hψ h₂
    let s₁₂ : G := Function.surjInv hψ (h₁ * h₂)
    have hs₁ : ψ s₁ = h₁ := by
      simpa [s₁] using Function.surjInv_eq hψ h₁
    have hs₂ : ψ s₂ = h₂ := by
      simpa [s₂] using Function.surjInv_eq hψ h₂
    have hs₁₂ : ψ s₁₂ = h₁ * h₂ := by
      simpa [s₁₂] using Function.surjInv_eq hψ (h₁ * h₂)
    let n : ψ.ker := ⟨s₁ * s₂ * s₁₂⁻¹, by
      change ψ (s₁ * s₂ * s₁₂⁻¹) = 1
      rw [map_mul, map_mul, hs₁, hs₂, map_inv, hs₁₂]
      simp only [mul_inv_rev, mul_assoc, mul_inv_cancel_left, mul_inv_cancel]⟩
    have hs :
        ((groupAugmentationIdealRep (G := G)).ρ s₁)
            (((groupAugmentationIdealRep (G := G)).ρ s₂) x) =
          ((groupAugmentationIdealRep (G := G)).ρ (s₁ * s₂)) x := by
      exact congrArg
        (fun f : augmentationIdeal G →ₗ[ℤ] augmentationIdeal G => f x)
        (((groupAugmentationIdealRep (G := G)).ρ).map_mul s₁ s₂).symm
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    change
      Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
        (((groupAugmentationIdealRep (G := G)).ρ s₁₂) x) =
      kernelAugmentationIdealCoinvariantsEndOfSurjective (ψ := ψ) hψ h₁
        (kernelAugmentationIdealCoinvariantsEndOfSurjective (ψ := ψ) hψ h₂
          (Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ) x))
    rw [kernelAugmentationIdealCoinvariantsEndOfSurjective_mk (ψ := ψ) hψ,
      kernelAugmentationIdealCoinvariantsEndOfSurjective_mk (ψ := ψ) hψ]
    calc
      Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
          (((groupAugmentationIdealRep (G := G)).ρ s₁₂) x)
          =
        Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
          (((kernelAugmentationIdealRep (ψ := ψ)).ρ n)
            (((groupAugmentationIdealRep (G := G)).ρ s₁₂) x)) := by
              rw [Representation.Coinvariants.mk_self_apply]
      _ = Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
            (((groupAugmentationIdealRep (G := G)).ρ n.1)
              (((groupAugmentationIdealRep (G := G)).ρ s₁₂) x)) := by
                rw [kernelAugmentationIdealRep_rho_eq_groupAugmentationIdealRep_rho
                  (ψ := ψ) n]
      _ = Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
            (((groupAugmentationIdealRep (G := G)).ρ (n.1 * s₁₂)) x) := by
              have hs' :
                  ((groupAugmentationIdealRep (G := G)).ρ n.1)
                      (((groupAugmentationIdealRep (G := G)).ρ s₁₂) x) =
                    ((groupAugmentationIdealRep (G := G)).ρ (n.1 * s₁₂)) x := by
                  exact congrArg
                    (fun f : augmentationIdeal G →ₗ[ℤ] augmentationIdeal G => f x)
                    (((groupAugmentationIdealRep (G := G)).ρ).map_mul n.1 s₁₂).symm
              rw [hs']
      _ = Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
            (((groupAugmentationIdealRep (G := G)).ρ (s₁ * s₂)) x) := by
              congr 1
              simp only [mul_assoc, inv_mul_cancel, mul_one, MonoidHom.coe_mk, OneHom.coe_mk,
                  map_mul,
  Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk, s₁, s₂, s₁₂, n]
      _ = Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
            (((groupAugmentationIdealRep (G := G)).ρ s₁)
              (((groupAugmentationIdealRep (G := G)).ρ s₂) x)) := by
                rw [hs]

/--
The ring action of \(\mathbb{Z}[H]\) on \(H_0(\ker \psi, I(\mathbb{Z}[G]))\) induced by a
surjective section.
-/
def kernelAugmentationIdealCoinvariantsActionRingHomOfSurjective
    (hψ : Function.Surjective ψ) :
    GroupRing H →+* Module.End ℤ (KernelAugmentationIdealCoinvariants (ψ := ψ)) :=
  MonoidAlgebra.liftNCRingHom
    (Int.castRingHom (Module.End ℤ (KernelAugmentationIdealCoinvariants (ψ := ψ))))
    (kernelAugmentationIdealCoinvariantsModuleEndOfSurjective (ψ := ψ) hψ)
    (by
      intro z h
      apply LinearMap.ext
      intro x
      change z •
          kernelAugmentationIdealCoinvariantsModuleEndOfSurjective (ψ := ψ) hψ h x =
        kernelAugmentationIdealCoinvariantsModuleEndOfSurjective (ψ := ψ) hψ h (z • x)
      rw [map_zsmul])

omit [DecidableEq H] [DecidableEq G] in
/--
The surjective-case coefficient action on coinvariants has the displayed value on
representatives.
-/
@[simp]
theorem kernelAugmentationIdealCoinvariantsActionRingHomOfSurjective_of
    (hψ : Function.Surjective ψ) (h : H) :
    kernelAugmentationIdealCoinvariantsActionRingHomOfSurjective (ψ := ψ) hψ
        (MonoidAlgebra.of ℤ H h) =
      kernelAugmentationIdealCoinvariantsModuleEndOfSurjective (ψ := ψ) hψ h := by
  let f := Int.castRingHom
    (Module.End ℤ (KernelAugmentationIdealCoinvariants (ψ := ψ)))
  let g := kernelAugmentationIdealCoinvariantsModuleEndOfSurjective (ψ := ψ) hψ
  have hcomm : ∀ z h₀, Commute (f z) (g h₀) := by
    intro z h₀
    apply LinearMap.ext
    intro x
    change z • g h₀ x = g h₀ (z • x)
    rw [map_zsmul]
  change MonoidAlgebra.liftNCRingHom f g hcomm
      (MonoidAlgebra.single h 1) = g h
  exact (MonoidAlgebra.liftNCRingHom_single f g hcomm h 1).trans
    (by rw [map_one, one_mul])

/-- The induced \(\mathbb{Z}[H]\)-module structure on \(H_0(\ker \psi, I(\mathbb{Z}[G]))\). -/
@[reducible] def kernelAugmentationIdealCoinvariantsModuleOfSurjective
    (hψ : Function.Surjective ψ) :
    Module (GroupRing H) (KernelAugmentationIdealCoinvariants (ψ := ψ)) :=
  Module.compHom _
    (kernelAugmentationIdealCoinvariantsActionRingHomOfSurjective (ψ := ψ) hψ)

omit [DecidableEq G] in
/--
The augmentation-generator identity \((g_1g_2-1)=(g_1-1)+g_1(g_2-1)\) inside
\(I(\mathbb{Z}[G])\).
-/
@[simp]
theorem augmentationGeneratorSubtype_mul (g₁ g₂ : G) :
    augmentationGeneratorSubtype (H := G) (g₁ * g₂) =
      augmentationGeneratorSubtype (H := G) g₁ +
        ((groupAugmentationIdealRep (G := G)).ρ g₁)
          (augmentationGeneratorSubtype (H := G) g₂) := by
  let ρg : GroupRing G →ₗ[ℤ] GroupRing G := (groupRingRep (G := G)).ρ g₁
  apply Subtype.ext
  change (augmentationGenerator G (g₁ * g₂) : GroupRing G) =
    (augmentationGenerator G g₁ : GroupRing G) +
      ρg (augmentationGenerator G g₂)
  have hρ :
      ρg (augmentationGenerator G g₂) =
        (MonoidAlgebra.of ℤ G (g₁ * g₂) : GroupRing G) - MonoidAlgebra.of ℤ G g₁ := by
    change ((groupRingRep (G := G)).ρ g₁)
        (MonoidAlgebra.single g₂ 1 - MonoidAlgebra.single (1 : G) 1) =
      (MonoidAlgebra.of ℤ G (g₁ * g₂) : GroupRing G) - MonoidAlgebra.of ℤ G g₁
    rw [map_sub, groupRingRep_apply_single, groupRingRep_apply_single]
    simp only [mul_one, MonoidAlgebra.of_apply]
  rw [augmentationGenerator, augmentationGenerator, hρ]
  abel_nf

/-- Kernel elements map to \(H_0(\ker \psi, I(\mathbb{Z}[G]))\) by \(n \mapsto [n - 1]\). -/
def kernelCoinvariantsBoundary (ψ : G →* H) :
    ψ.ker →* Multiplicative (KernelAugmentationIdealCoinvariants (ψ := ψ)) where
  toFun n := Multiplicative.ofAdd <|
    Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
      (augmentationGeneratorSubtype (H := G) n.1)
  map_one' := by
    apply Multiplicative.toAdd.injective
    have hzero : augmentationGeneratorSubtype (H := G) (1 : G) = 0 := by
      apply Subtype.ext
      simp only [augmentationGeneratorSubtype, augmentationGenerator, groupRing_of_one (H := G),
          sub_self,
  ZeroMemClass.coe_zero]
    simp only [OneMemClass.coe_one, hzero, map_zero, ofAdd_zero, toAdd_one]
  map_mul' n₁ n₂ := by
    apply Multiplicative.toAdd.injective
    change
      Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
        (augmentationGeneratorSubtype (H := G) (n₁.1 * n₂.1)) =
      Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
          (augmentationGeneratorSubtype (H := G) n₁.1) +
        Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
          (augmentationGeneratorSubtype (H := G) n₂.1)
    rw [augmentationGeneratorSubtype_mul, map_add]
    congr 1
    calc
      Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
          (((groupAugmentationIdealRep (G := G)).ρ n₁.1)
            (augmentationGeneratorSubtype (H := G) n₂.1))
        = Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
            (((kernelAugmentationIdealRep (ψ := ψ)).ρ n₁)
              (augmentationGeneratorSubtype (H := G) n₂.1)) := by
              rw [kernelAugmentationIdealRep_rho_eq_groupAugmentationIdealRep_rho (ψ := ψ) n₁]
      _ = Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
            (augmentationGeneratorSubtype (H := G) n₂.1) := by
              exact Representation.Coinvariants.mk_self_apply
                ((kernelAugmentationIdealRep (ψ := ψ)).ρ) n₁
                (augmentationGeneratorSubtype (H := G) n₂.1)

/-- The map \(n \mapsto [n-1]\) factors through the abelianization of \(\ker \psi\). -/
def kernelAbelianizationToCoinvariants (ψ : G →* H) :
    Abelianization ψ.ker →* Multiplicative (KernelAugmentationIdealCoinvariants (ψ := ψ)) :=
  Abelianization.lift (kernelCoinvariantsBoundary (ψ := ψ))

/-- Additive form of the map \((\ker \psi)^{\mathrm{ab}} \to H_0(\ker \psi, I(\mathbb{Z}[G]))\). -/
def kernelAbelianizationToCoinvariantsAdd (ψ : G →* H) :
    KernelAbelianizationAdd ψ →+ KernelAugmentationIdealCoinvariants (ψ := ψ) where
  toFun x := Multiplicative.toAdd (kernelAbelianizationToCoinvariants (ψ := ψ) (Additive.toMul x))
  map_zero' := by
    simp only [toMul_zero, map_one, toAdd_one]
  map_add' x y := by
    simp only [toMul_add, map_mul, toAdd_mul]

omit [DecidableEq H] [DecidableEq G] in
/--
The additive kernel-abelianization map sends a kernel element to its augmentation-coinvariant
class.
-/
@[simp]
theorem kernelAbelianizationToCoinvariantsAdd_of (n : ψ.ker) :
    kernelAbelianizationToCoinvariantsAdd (ψ := ψ)
        (Additive.ofMul (Abelianization.of n)) =
      Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
        (augmentationGeneratorSubtype (H := G) n.1) := by
  simp only [kernelAbelianizationToCoinvariantsAdd, kernelAbelianizationToCoinvariants,
  kernelCoinvariantsBoundary, AddMonoidHom.coe_mk, ZeroHom.coe_mk, toMul_ofMul,
      Abelianization.lift_apply_of,
  MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]

/--
\(\mathbb{Z}\)-linear form of the map \((\ker \psi)^{\mathrm{ab}} \to H_0(\ker \psi,
I(\mathbb{Z}[G]))\).
-/
def kernelAbelianizationToCoinvariantsLinear (ψ : G →* H) :
    KernelAbelianizationAdd ψ →ₗ[ℤ] KernelAugmentationIdealCoinvariants (ψ := ψ) :=
  (kernelAbelianizationToCoinvariantsAdd (ψ := ψ)).toIntLinearMap

/--
The low-degree homology comparison \((\ker \psi)^{\mathrm{ab}} \to H_0(\ker \psi,
I(\mathbb{Z}[G]))\) obtained from the connecting morphism \(H_1(\ker \psi, \mathbb{Z}) \to
H_0(\ker \psi, I(\mathbb{Z}[G]))\). Our convention for \(\delta_0\) introduces a minus sign on
generators.
-/
def kernelAbelianizationToCoinvariantsViaConnectingAdd (ψ : G →* H) :
    KernelAbelianizationAdd ψ →+ KernelAugmentationIdealCoinvariants (ψ := ψ) where
  toFun x :=
    -((groupHomology.H0Iso (kernelAugmentationIdealRep (ψ := ψ))).hom.hom
      ((kernelAugmentationConnecting (ψ := ψ)).hom
        ((kernelTrivialH1AddEquivAbelianization (ψ := ψ)).symm x)))
  map_zero' := by
    simp only [coinvariantsFunctor_obj_carrier, map_zero, neg_zero]
  map_add' x y := by
    rw [(kernelTrivialH1AddEquivAbelianization (ψ := ψ)).symm.map_add]
    simp only [coinvariantsFunctor_obj_carrier, map_add, neg_add_rev]
    abel_nf

/--
\(\mathbb{Z}\)-linear form of the connecting-morphism comparison \((\ker \psi)^{\mathrm{ab}} \to
H_0(\ker \psi, I(\mathbb{Z}[G]))\).
-/
def kernelAbelianizationToCoinvariantsViaConnectingLinear (ψ : G →* H) :
    KernelAbelianizationAdd ψ →ₗ[ℤ] KernelAugmentationIdealCoinvariants (ψ := ψ) :=
  (kernelAbelianizationToCoinvariantsViaConnectingAdd (ψ := ψ)).toIntLinearMap

omit [DecidableEq H] [DecidableEq G] in
/--
The connecting-morphism comparison sends a kernel element to the corresponding
augmentation-coinvariant class.
-/
@[simp]
theorem kernelAbelianizationToCoinvariantsViaConnectingAdd_of (n : ψ.ker) :
    kernelAbelianizationToCoinvariantsViaConnectingAdd (ψ := ψ)
        (Additive.ofMul (Abelianization.of n)) =
      Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
        (augmentationGeneratorSubtype (H := G) n.1) := by
  change
    -((groupHomology.H0Iso (kernelAugmentationIdealRep (ψ := ψ))).hom.hom
      ((kernelAugmentationConnecting (ψ := ψ)).hom
        ((kernelTrivialH1AddEquivAbelianization (ψ := ψ)).symm
          (Additive.ofMul (Abelianization.of n))))) =
      Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
        (augmentationGeneratorSubtype (H := G) n.1)
  rw [kernelAugmentationConnecting_H0Iso_of]
  simp only [coinvariantsFunctor_obj_carrier, neg_neg]

omit [DecidableEq H] [DecidableEq G] in
/-- The linear connecting-morphism comparison has the stated value on a kernel element. -/
@[simp]
theorem kernelAbelianizationToCoinvariantsViaConnectingLinear_of (n : ψ.ker) :
    kernelAbelianizationToCoinvariantsViaConnectingLinear (ψ := ψ)
        (Additive.ofMul (Abelianization.of n)) =
      Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
        (augmentationGeneratorSubtype (H := G) n.1) := by
  change kernelAbelianizationToCoinvariantsViaConnectingAdd (ψ := ψ)
      (Additive.ofMul (Abelianization.of n)) = _
  exact kernelAbelianizationToCoinvariantsViaConnectingAdd_of (ψ := ψ) n

omit [DecidableEq H] [DecidableEq G] in
/--
The linear abelianization-to-coinvariants map agrees with the map obtained from the connecting
morphism.
-/
theorem kernelAbelianizationToCoinvariantsLinear_eq_viaConnecting
    (ψ : G →* H) :
    kernelAbelianizationToCoinvariantsLinear (ψ := ψ) =
      kernelAbelianizationToCoinvariantsViaConnectingLinear (ψ := ψ) := by
  apply LinearMap.ext
  intro x
  change
    (fun y : Abelianization ψ.ker =>
      kernelAbelianizationToCoinvariantsLinear (ψ := ψ) (Additive.ofMul y) =
        kernelAbelianizationToCoinvariantsViaConnectingLinear (ψ := ψ) (Additive.ofMul y))
      (Additive.toMul x)
  refine QuotientGroup.induction_on (Additive.toMul x) ?_
  intro n
  calc
    kernelAbelianizationToCoinvariantsLinear (ψ := ψ) (Additive.ofMul (Abelianization.of n))
      = kernelAbelianizationToCoinvariantsAdd (ψ := ψ)
          (Additive.ofMul (Abelianization.of n)) := by
            rfl
    _ = Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
          (augmentationGeneratorSubtype (H := G) n.1) := by
            rw [kernelAbelianizationToCoinvariantsAdd_of]
    _ = kernelAbelianizationToCoinvariantsViaConnectingLinear (ψ := ψ)
          (Additive.ofMul (Abelianization.of n)) := by
            rw [kernelAbelianizationToCoinvariantsViaConnectingLinear_of]

omit [DecidableEq H] [DecidableEq G] in
/-- The abelianization-to-coinvariants map is injective. -/
theorem kernelAbelianizationToCoinvariantsLinear_injective
    (hψ : Function.Surjective ψ) :
    Function.Injective (kernelAbelianizationToCoinvariantsLinear (ψ := ψ)) := by
  have hEq := kernelAbelianizationToCoinvariantsLinear_eq_viaConnecting (ψ := ψ)
  intro x y hxy
  have hxy' :
      kernelAbelianizationToCoinvariantsViaConnectingLinear (ψ := ψ) x =
        kernelAbelianizationToCoinvariantsViaConnectingLinear (ψ := ψ) y := by
    simpa [hEq] using hxy
  have hxy'' :
      kernelAbelianizationToCoinvariantsViaConnectingAdd (ψ := ψ) x =
        kernelAbelianizationToCoinvariantsViaConnectingAdd (ψ := ψ) y := by
    change
      (kernelAbelianizationToCoinvariantsViaConnectingAdd (ψ := ψ)).toIntLinearMap x =
        (kernelAbelianizationToCoinvariantsViaConnectingAdd (ψ := ψ)).toIntLinearMap y
    exact hxy'
  have hxy''' : ((groupHomology.H0Iso (kernelAugmentationIdealRep (ψ := ψ))).hom.hom
      ((kernelAugmentationConnecting (ψ := ψ)).hom
        ((kernelTrivialH1AddEquivAbelianization (ψ := ψ)).symm x))) =
    ((groupHomology.H0Iso (kernelAugmentationIdealRep (ψ := ψ))).hom.hom
      ((kernelAugmentationConnecting (ψ := ψ)).hom
        ((kernelTrivialH1AddEquivAbelianization (ψ := ψ)).symm y))) := by
    simpa [kernelAbelianizationToCoinvariantsViaConnectingAdd] using congrArg Neg.neg hxy''
  have hH0Iso :
      Function.Injective
        ((groupHomology.H0Iso (kernelAugmentationIdealRep (ψ := ψ))).hom.hom) := by
    exact (ModuleCat.mono_iff_injective _).1 inferInstance
  apply (kernelTrivialH1AddEquivAbelianization (ψ := ψ)).symm.injective
  apply kernelAugmentationConnecting_injective (H := H) (ψ := ψ) hψ
  exact hH0Iso hxy'''

omit [DecidableEq H] [DecidableEq G] in
/-- The induced \(H\)-action on kernel augmentation coinvariants is computed on representatives. -/
@[simp]
theorem kernelAugmentationIdealCoinvariants_smul_mk_ofSurjective
    (hψ : Function.Surjective ψ) (h : H) (x : augmentationIdeal G) :
    letI := kernelAugmentationIdealCoinvariantsModuleOfSurjective (ψ := ψ) hψ
    (MonoidAlgebra.of ℤ H h : GroupRing H) •
        Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ) x =
      Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
        (((groupAugmentationIdealRep (G := G)).ρ (Function.surjInv hψ h)) x) := by
  let := kernelAugmentationIdealCoinvariantsModuleOfSurjective (ψ := ψ) hψ
  rw [show (MonoidAlgebra.of ℤ H h : GroupRing H) •
      Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ) x =
    kernelAugmentationIdealCoinvariantsActionRingHomOfSurjective (ψ := ψ) hψ
        (MonoidAlgebra.of ℤ H h)
        (Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ) x) by
      rfl]
  rw [kernelAugmentationIdealCoinvariantsActionRingHomOfSurjective_of (ψ := ψ) hψ]
  simpa [kernelAugmentationIdealCoinvariantsModuleEndOfSurjective] using
    (kernelAugmentationIdealCoinvariantsEndOfSurjective_mk (ψ := ψ) hψ h x)

omit [DecidableEq H] [DecidableEq G] in
/--
The coinvariant representative in the augmentation-ideal kernel is compatible with the group
action whenever the underlying representatives are equal.
-/
theorem kernelAugmentationIdealCoinvariants_mk_group_action_eq_of_eq
    {g₁ g₂ : G} (h : ψ g₁ = ψ g₂) (x : augmentationIdeal G) :
    Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
        (((groupAugmentationIdealRep (G := G)).ρ g₁) x) =
      Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
        (((groupAugmentationIdealRep (G := G)).ρ g₂) x) := by
  let n : ψ.ker := ⟨g₁ * g₂⁻¹, by
    simp only [MonoidHom.mem_ker, map_mul, h, map_inv, mul_inv_cancel]⟩
  calc
    Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
        (((groupAugmentationIdealRep (G := G)).ρ g₁) x)
      = Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
          (((groupAugmentationIdealRep (G := G)).ρ (n.1 * g₂)) x) := by
            congr 1
            simp only [MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
                mul_assoc, inv_mul_cancel,
  mul_one, n]
    _ = Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
          (((groupAugmentationIdealRep (G := G)).ρ n.1)
            (((groupAugmentationIdealRep (G := G)).ρ g₂) x)) := by
            congr 1
            exact congrArg
              (fun f : augmentationIdeal G →ₗ[ℤ] augmentationIdeal G => f x)
              (((groupAugmentationIdealRep (G := G)).ρ).map_mul n.1 g₂)
    _ = Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
          (((kernelAugmentationIdealRep (ψ := ψ)).ρ n)
            (((groupAugmentationIdealRep (G := G)).ρ g₂) x)) := by
            rw [kernelAugmentationIdealRep_rho_eq_groupAugmentationIdealRep_rho (ψ := ψ) n]
    _ = Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
          (((groupAugmentationIdealRep (G := G)).ρ g₂) x) := by
            exact Representation.Coinvariants.mk_self_apply
              ((kernelAugmentationIdealRep (ψ := ψ)).ρ) n
              (((groupAugmentationIdealRep (G := G)).ρ g₂) x)

/--
The canonical differential generator \(g \mapsto [g - 1]\) in \(H_0(\ker \psi,
I(\mathbb{Z}[G]))\).
-/
def kernelAugmentationIdealCoinvariantsGeneratorOfSurjective
    (g : G) :
    KernelAugmentationIdealCoinvariants (ψ := ψ) :=
  Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
    (augmentationGeneratorSubtype (H := G) g)

omit [DecidableEq H] [DecidableEq G] in
private theorem kernelAugmentationIdealCoinvariantsGeneratorOfSurjective_map_mul
    (hψ : Function.Surjective ψ) (g₁ g₂ : G) :
    letI := kernelAugmentationIdealCoinvariantsModuleOfSurjective (ψ := ψ) hψ
    kernelAugmentationIdealCoinvariantsGeneratorOfSurjective (ψ := ψ) (g₁ * g₂) =
      kernelAugmentationIdealCoinvariantsGeneratorOfSurjective (ψ := ψ) g₁ +
        groupRingScalar ψ g₁ •
          kernelAugmentationIdealCoinvariantsGeneratorOfSurjective (ψ := ψ) g₂ := by
  let := kernelAugmentationIdealCoinvariantsModuleOfSurjective (ψ := ψ) hψ
  rw [kernelAugmentationIdealCoinvariantsGeneratorOfSurjective,
    augmentationGeneratorSubtype_mul]
  rw [map_add]
  congr 1
  calc
    Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
        (((groupAugmentationIdealRep (G := G)).ρ g₁)
          (augmentationGeneratorSubtype (H := G) g₂))
      = Representation.Coinvariants.mk ((kernelAugmentationIdealRep (ψ := ψ)).ρ)
          (((groupAugmentationIdealRep (G := G)).ρ
              (Function.surjInv hψ (ψ g₁)))
            (augmentationGeneratorSubtype (H := G) g₂)) := by
              apply kernelAugmentationIdealCoinvariants_mk_group_action_eq_of_eq (ψ := ψ)
              simpa using (Function.surjInv_eq hψ (ψ g₁)).symm
    _ = (MonoidAlgebra.of ℤ H (ψ g₁) : GroupRing H) •
          kernelAugmentationIdealCoinvariantsGeneratorOfSurjective (ψ := ψ) g₂ := by
            symm
            exact kernelAugmentationIdealCoinvariants_smul_mk_ofSurjective
              (ψ := ψ) hψ (ψ g₁) (augmentationGeneratorSubtype (H := G) g₂)

/-- The canonical coinvariant generator is a crossed differential in the surjective case. -/
def kernelAugmentationIdealCoinvariantsGeneratorHomOfSurjective
    (hψ : Function.Surjective ψ) :
    letI := kernelAugmentationIdealCoinvariantsModuleOfSurjective (ψ := ψ) hψ
    DifferentialHom ψ (KernelAugmentationIdealCoinvariants (ψ := ψ)) := by
  letI := kernelAugmentationIdealCoinvariantsModuleOfSurjective (ψ := ψ) hψ
  exact
    { toFun := kernelAugmentationIdealCoinvariantsGeneratorOfSurjective (ψ := ψ)
      map_mul' := by
        intro g₁ g₂
        simpa only [scalarCrossedAction_apply] using
          kernelAugmentationIdealCoinvariantsGeneratorOfSurjective_map_mul
            (ψ := ψ) hψ g₁ g₂ }

/--
The canonical linear map \(A_{\psi}\to H_0(\ker \psi, I(\mathbb{Z}[G]))\) sending \(d(g)\) to
\([g-1]\).
-/
def differentialToKernelAugmentationIdealCoinvariantsLinearOfSurjective
    (hψ : Function.Surjective ψ) :
    letI := kernelAugmentationIdealCoinvariantsModuleOfSurjective (ψ := ψ) hψ
    DifferentialModule ψ →ₗ[GroupRing H] KernelAugmentationIdealCoinvariants (ψ := ψ) := by
  letI := kernelAugmentationIdealCoinvariantsModuleOfSurjective (ψ := ψ) hψ
  exact
    differentialModuleLift ψ
      (kernelAugmentationIdealCoinvariantsGeneratorHomOfSurjective (ψ := ψ) hψ)

omit [DecidableEq H] [DecidableEq G] in
/--
The surjective-case differential-to-coinvariants map sends each universal differential generator
to the corresponding coinvariant class.
-/
@[simp]
theorem differentialToKernelAugmentationIdealCoinvariantsLinearOfSurjective_d
    (hψ : Function.Surjective ψ) (g : G) :
    letI := kernelAugmentationIdealCoinvariantsModuleOfSurjective (ψ := ψ) hψ
    differentialToKernelAugmentationIdealCoinvariantsLinearOfSurjective
        (ψ := ψ) hψ (universalDifferential ψ g) =
      kernelAugmentationIdealCoinvariantsGeneratorOfSurjective (ψ := ψ) g := by
  let := kernelAugmentationIdealCoinvariantsModuleOfSurjective (ψ := ψ) hψ
  change
    differentialModuleLift ψ
        (kernelAugmentationIdealCoinvariantsGeneratorHomOfSurjective (ψ := ψ) hψ)
        (universalDifferential ψ g) =
      kernelAugmentationIdealCoinvariantsGeneratorOfSurjective (ψ := ψ) g
  exact
    differentialModuleLift_d
      (A := KernelAugmentationIdealCoinvariants (ψ := ψ))
      ψ
      (kernelAugmentationIdealCoinvariantsGeneratorHomOfSurjective (ψ := ψ) hψ)
      g

omit [DecidableEq H] [DecidableEq G] in
/-- The surjective-case differential-to-coinvariants map is compatible with the boundary map. -/
@[simp 900]
theorem differentialToKernelAugmentationIdealCoinvariantsLinearOfSurjective_boundary
    (hψ : Function.Surjective ψ) (x : KernelAbelianizationAdd ψ) :
    letI := kernelAbelianizationModuleOfSurjective ψ hψ
    letI := kernelAugmentationIdealCoinvariantsModuleOfSurjective (ψ := ψ) hψ
    differentialToKernelAugmentationIdealCoinvariantsLinearOfSurjective (ψ := ψ) hψ
        (kernelAbelianizationBoundaryLinearOfSurjective ψ hψ x) =
      kernelAbelianizationToCoinvariantsLinear (ψ := ψ) x := by
  let := kernelAbelianizationModuleOfSurjective ψ hψ
  let := kernelAugmentationIdealCoinvariantsModuleOfSurjective (ψ := ψ) hψ
  change
    (fun y : Abelianization ψ.ker =>
      differentialToKernelAugmentationIdealCoinvariantsLinearOfSurjective (ψ := ψ) hψ
          (kernelAbelianizationBoundaryAdd ψ (Additive.ofMul y)) =
        kernelAbelianizationToCoinvariantsAdd (ψ := ψ) (Additive.ofMul y))
      (Additive.toMul x)
  refine QuotientGroup.induction_on (Additive.toMul x) ?_
  intro n
  calc
    differentialToKernelAugmentationIdealCoinvariantsLinearOfSurjective (ψ := ψ) hψ
        ((kernelAbelianizationBoundaryAdd ψ) (Additive.ofMul (Abelianization.of n))) =
      differentialToKernelAugmentationIdealCoinvariantsLinearOfSurjective (ψ := ψ) hψ
        (universalDifferential ψ n.1) := by
          exact congrArg
            (differentialToKernelAugmentationIdealCoinvariantsLinearOfSurjective
              (ψ := ψ) hψ)
            (kernelAbelianizationBoundaryAdd_of (ψ := ψ) n)
    _ = kernelAugmentationIdealCoinvariantsGeneratorOfSurjective (ψ := ψ) n.1 := by
          exact differentialToKernelAugmentationIdealCoinvariantsLinearOfSurjective_d
            (ψ := ψ) hψ n.1
    _ = kernelAbelianizationToCoinvariantsAdd (ψ := ψ) (Additive.ofMul (Abelianization.of n)) := by
          symm
          simp only [kernelAbelianizationToCoinvariantsAdd_of,
  kernelAugmentationIdealCoinvariantsGeneratorOfSurjective]

end CoinvariantsAction

end KernelAugmentation

end

end FoxDifferential

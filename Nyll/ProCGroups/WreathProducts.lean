/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.SemidirectProduct
import Nyll.ProCGroups.ProC.Subgroups.Products
import Nyll.ProCGroups.ReidemeisterSchreier.RightQuotient

/-!
# Pro C Groups / Wreath Products

This module formalizes permutational wreath products.
-/

open scoped Pointwise

namespace ProCGroups.WreathProducts

universe u v w

section RightCosets

variable {G : Type u} [Group G]

/-- Right multiplication on right cosets, expressed as a left action by
`g • [a] = [a * g⁻¹]`. -/
@[reducible]
def rightCosetMulAction (H : Subgroup G) :
    MulAction G (Quotient (QuotientGroup.rightRel H)) :=
  _root_.ReidemeisterSchreier.rightCosetMulAction H

/-- Acting on a represented right coset multiplies its representative by the inverse on the
right. -/
@[simp 900] theorem rightCosetMulAction_mk_smul
    (H : Subgroup G) (g a : G) :
    letI := rightCosetMulAction H
    g • (Quotient.mk'' a : Quotient (QuotientGroup.rightRel H)) =
      Quotient.mk'' (a * g⁻¹) :=
  rfl

/-- Acting by an inverse on a represented right coset multiplies its representative on the
right. -/
@[simp 900] theorem rightCosetMulAction_inv_mk_smul
    (H : Subgroup G) (g a : G) :
    letI := rightCosetMulAction H
    g⁻¹ • (Quotient.mk'' a : Quotient (QuotientGroup.rightRel H)) =
      Quotient.mk'' (a * g) := by
  rw [rightCosetMulAction_mk_smul (H := H) g⁻¹ a]
  simp only [inv_inv]

end RightCosets

section RightCosetTopology

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- For an open subgroup, the orbit map to the discrete right-coset space is continuous. -/
theorem continuous_rightCosetMulAction_inv_smul_of_open
    (H : Subgroup G) (hH : IsOpen (H : Set G))
    [TopologicalSpace (Quotient (QuotientGroup.rightRel H))]
    [DiscreteTopology (Quotient (QuotientGroup.rightRel H))]
    (q : Quotient (QuotientGroup.rightRel H)) :
    letI := rightCosetMulAction H
    Continuous fun g : G => g⁻¹ • q := by
  rw [continuous_discrete_rng]
  intro q'
  classical
  let a : G := q.out
  let b : G := q'.out
  have hpre :
      (fun g : G => g⁻¹ • q) ⁻¹' (Set.singleton q') =
        (fun g : G => b * g⁻¹ * a⁻¹) ⁻¹' (H : Set G) := by
    ext g
    constructor
    · intro hg
      have hEq :
          (Quotient.mk'' (a * g) : Quotient (QuotientGroup.rightRel H)) =
            Quotient.mk'' b := by
        calc
          (Quotient.mk'' (a * g) : Quotient (QuotientGroup.rightRel H))
              = g⁻¹ • (Quotient.mk'' a : Quotient (QuotientGroup.rightRel H)) := by
                  rw [rightCosetMulAction_inv_mk_smul (H := H) g a]
          _ = g⁻¹ • q := by rw [Quotient.out_eq' q]
          _ = q' := by
            change g⁻¹ • q = q' at hg
            exact hg
          _ = Quotient.mk'' b := by simp only [Quotient.out_eq, b]
      have hrel : QuotientGroup.rightRel H (a * g) b := Quotient.eq''.mp hEq
      simpa [mul_inv_rev, mul_assoc] using (QuotientGroup.rightRel_apply.mp hrel)
    · intro hg
      have hrel : QuotientGroup.rightRel H (a * g) b := by
        rw [QuotientGroup.rightRel_apply]
        simpa [mul_inv_rev, mul_assoc] using hg
      calc
        g⁻¹ • q = g⁻¹ • (Quotient.mk'' a : Quotient (QuotientGroup.rightRel H)) := by
          rw [Quotient.out_eq' q]
        _ = Quotient.mk'' (a * g) := by
          rw [rightCosetMulAction_inv_mk_smul (H := H) g a]
        _ = Quotient.mk'' b := Quotient.eq''.mpr hrel
        _ = q' := Quotient.out_eq' q'
  change
    (fun g : G => g⁻¹ • q) ⁻¹'
      ({q'} : Set (Quotient (QuotientGroup.rightRel H))) =
        (fun g : G => b * g⁻¹ * a⁻¹) ⁻¹' (H : Set G) at hpre
  rw [hpre]
  exact hH.preimage ((continuous_const.mul continuous_inv).mul continuous_const)

end RightCosetTopology

section BasicDefinitions

variable (A : Type u) (S : Type v) (G : Type w)
variable [Group A] [Group G] [MulAction G S]

/-- The permutational wreath product attached to a `G`-set `Σ`. -/
abbrev PermutationalWreathProduct :=
  (S → A) ⋊[(mulAutArrow (G := G) (A := S) (M := A))] G

end BasicDefinitions

section Topology

variable {A : Type u} {S : Type v} {G : Type w}
variable [Group A] [Group G] [MulAction G S]
variable [TopologicalSpace A] [TopologicalSpace G]

/-- Give a permutational wreath product the topology transported from its product
representation. -/
instance instTopologicalSpacePermutationalWreathProduct :
    TopologicalSpace (PermutationalWreathProduct A S G) :=
  TopologicalSpace.induced
    (SemidirectProduct.equivProd :
      PermutationalWreathProduct A S G ≃ (S → A) × G)
    inferInstance

/-- The topology on a permutational wreath product is the one transported from the product of the
function factor and the right factor. -/
@[simps!]
def permutationalWreathProductHomeomorphProd :
    PermutationalWreathProduct A S G ≃ₜ (S → A) × G where
  toEquiv := SemidirectProduct.equivProd
  continuous_toFun := continuous_induced_dom
  continuous_invFun := by
    rw [continuous_induced_rng]
    simpa using (continuous_id : Continuous fun x : (S → A) × G => x)

/-- The canonical equivalence from a permutational wreath product to its two factors is
continuous. -/
@[continuity] theorem continuous_permutationalWreathProduct_equivProd :
    Continuous
      (SemidirectProduct.equivProd :
        PermutationalWreathProduct A S G → (S → A) × G) :=
  continuous_induced_dom

/-- Projection to the function factor of a permutational wreath product is continuous. -/
@[continuity] theorem continuous_permutationalWreathProduct_left :
    Continuous (fun x : PermutationalWreathProduct A S G => x.left) :=
  continuous_fst.comp continuous_permutationalWreathProduct_equivProd

/-- Projection to the acting-group factor of a permutational wreath product is continuous. -/
@[continuity] theorem continuous_permutationalWreathProduct_right :
    Continuous (fun x : PermutationalWreathProduct A S G => x.right) :=
  continuous_snd.comp continuous_permutationalWreathProduct_equivProd

/-- Evaluation of the function factor at a fixed index is continuous. -/
@[continuity] theorem continuous_permutationalWreathProduct_left_apply (s : S) :
    Continuous (fun x : PermutationalWreathProduct A S G => x.left s) :=
  (continuous_apply s).comp continuous_permutationalWreathProduct_left

/-- A permutational wreath product is Hausdorff when both group factors are Hausdorff. -/
instance instT2SpacePermutationalWreathProduct [T2Space A] [T2Space G] :
    T2Space (PermutationalWreathProduct A S G) :=
  (permutationalWreathProductHomeomorphProd (A := A) (S := S) (G := G)).symm.t2Space

/-- A permutational wreath product is compact when both group factors are compact. -/
instance instCompactSpacePermutationalWreathProduct [CompactSpace A] [CompactSpace G] :
    CompactSpace (PermutationalWreathProduct A S G) :=
  (permutationalWreathProductHomeomorphProd (A := A) (S := S) (G := G)).symm.compactSpace

/-- A permutational wreath product is totally disconnected when both group factors are. -/
instance instTotallyDisconnectedSpacePermutationalWreathProduct
    [TotallyDisconnectedSpace A] [TotallyDisconnectedSpace G] :
    TotallyDisconnectedSpace (PermutationalWreathProduct A S G) :=
  Homeomorph.totallyDisconnectedSpace
    ((permutationalWreathProductHomeomorphProd (A := A) (S := S) (G := G)).symm)

/-- Precomposition by the inverse permutation coming from the `G`-action on `S`. This is the
action appearing in `mulAutArrow`. -/
def functionPrecomp (g : G) (f : S → A) : S → A :=
  fun s => f (g⁻¹ • s)

omit [Group A] [TopologicalSpace A] [TopologicalSpace G] in
/-- Precomposition by the action evaluates at the inverse translate of the index. -/
@[simp] theorem functionPrecomp_apply (g : G) (f : S → A) (s : S) :
    functionPrecomp g f s = f (g⁻¹ • s) :=
  rfl

omit [TopologicalSpace A] [TopologicalSpace G] in
/-- Mathlib's action on the function factor is precomposition by the inverse permutation. -/
@[simp] theorem mulAutArrow_apply_eq_functionPrecomp (g : G) (f : S → A) :
    mulAutArrow (G := G) (A := S) (M := A) g f = functionPrecomp g f :=
  rfl

section DiscreteIndex

variable [TopologicalSpace S] [DiscreteTopology S]
variable [ContinuousSMul G S] [ContinuousInv G]

omit [Group A] in
/-- Evaluation is jointly continuous on the product of a function space with a discrete index
space. -/
theorem continuous_eval_of_discreteIndex :
    Continuous (fun p : (S → A) × S => p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  have hs :
      Prod.snd ⁻¹' ({p.2} : Set S) ∈ nhds p := by
    refine IsOpen.mem_nhds ((isOpen_discrete ({p.2} : Set S)).preimage continuous_snd) ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
  have hEq :
      (fun q : (S → A) × S => q.1 q.2) =ᶠ[nhds p] fun q => q.1 p.2 := by
    refine Filter.eventuallyEq_iff_exists_mem.mpr ?_
    refine ⟨Prod.snd ⁻¹' ({p.2} : Set S), hs, ?_⟩
    intro q hq
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hq
    simp only [hq]
  exact ContinuousAt.congr
    (((continuous_apply p.2).comp continuous_fst).continuousAt) hEq.symm

omit [Group A] in
/-- The precomposition action on the function factor is continuous when the index space is
discrete. -/
theorem continuous_functionPrecomp :
    Continuous (fun p : G × (S → A) => functionPrecomp p.1 p.2) := by
  refine continuous_pi ?_
  intro s
  change Continuous (fun p : G × (S → A) => p.2 (p.1⁻¹ • s))
  have h :=
    (continuous_eval_of_discreteIndex (A := A) (S := S)).comp
      (continuous_snd.prodMk
        (((continuous_inv.comp continuous_fst).smul continuous_const) :
          Continuous (fun p : G × (S → A) => p.1⁻¹ • s)))
  change Continuous (fun p : G × (S → A) => p.2 (p.1⁻¹ • s)) at h
  exact h

omit [TopologicalSpace A] [TopologicalSpace G] [TopologicalSpace S] [DiscreteTopology S]
    [ContinuousSMul G S] [ContinuousInv G] in
/-- The function factor of a product is the first function times the translate of the second. -/
@[simp 900] theorem permutationalWreathProduct_mul_left
    (x y : PermutationalWreathProduct A S G) :
    (x * y).left = x.left * functionPrecomp x.right y.left :=
  rfl

omit [TopologicalSpace A] [TopologicalSpace G] [TopologicalSpace S] [DiscreteTopology S]
    [ContinuousSMul G S] [ContinuousInv G] in
/-- The function factor of an inverse is the translated pointwise inverse. -/
@[simp 900] theorem permutationalWreathProduct_inv_left
    (x : PermutationalWreathProduct A S G) :
    x⁻¹.left = functionPrecomp x.right⁻¹ x.left⁻¹ :=
  rfl

/-- Multiplication in the permutational wreath product is continuous for a discrete index
space. -/
instance instContinuousMulPermutationalWreathProduct
    [ContinuousMul A] [ContinuousMul G] :
    ContinuousMul (PermutationalWreathProduct A S G) where
  continuous_mul := by
    refine continuous_induced_rng.2 ?_
    change Continuous
      (fun p : PermutationalWreathProduct A S G × PermutationalWreathProduct A S G =>
        ((p.1 * p.2).left, (p.1 * p.2).right))
    have hleft :
        Continuous
          (fun p : PermutationalWreathProduct A S G × PermutationalWreathProduct A S G =>
            p.1.left * functionPrecomp p.1.right p.2.left) :=
      (continuous_permutationalWreathProduct_left.comp continuous_fst).mul
        (continuous_functionPrecomp.comp
          ((continuous_permutationalWreathProduct_right.comp continuous_fst).prodMk
            (continuous_permutationalWreathProduct_left.comp continuous_snd)))
    have hright :
        Continuous
          (fun p : PermutationalWreathProduct A S G × PermutationalWreathProduct A S G =>
            p.1.right * p.2.right) :=
      (continuous_permutationalWreathProduct_right.comp continuous_fst).mul
        (continuous_permutationalWreathProduct_right.comp continuous_snd)
    simpa using hleft.prodMk hright

/-- Inversion in the permutational wreath product is continuous for a discrete index space. -/
instance instContinuousInvPermutationalWreathProduct
    [ContinuousInv A] :
    ContinuousInv (PermutationalWreathProduct A S G) where
  continuous_inv := by
    refine continuous_induced_rng.2 ?_
    change Continuous
      (fun x : PermutationalWreathProduct A S G => (x⁻¹.left, x⁻¹.right))
    have hleft :
        Continuous
          (fun x : PermutationalWreathProduct A S G =>
            functionPrecomp x.right⁻¹ x.left⁻¹) :=
      continuous_functionPrecomp.comp
        ((continuous_permutationalWreathProduct_right.inv).prodMk
          (continuous_permutationalWreathProduct_left.inv))
    have hright :
        Continuous (fun x : PermutationalWreathProduct A S G => x.right⁻¹) :=
      continuous_permutationalWreathProduct_right.inv
    have hfun :
        (fun x : PermutationalWreathProduct A S G => (x⁻¹.left, x⁻¹.right)) =
          fun x => (functionPrecomp x.right⁻¹ x.left⁻¹, x.right⁻¹) := by
      funext x
      apply Prod.ext
      · exact permutationalWreathProduct_inv_left x
      · rfl
    rw [hfun]
    exact hleft.prodMk hright

end DiscreteIndex

/-- The transported topology makes the permutational wreath product a topological group. -/
instance instIsTopologicalGroupPermutationalWreathProduct
    [TopologicalSpace S] [DiscreteTopology S] [ContinuousSMul G S]
    [IsTopologicalGroup A] [IsTopologicalGroup G] :
    IsTopologicalGroup (PermutationalWreathProduct A S G) :=
  { }

/-- The canonical inclusion of the function factor is continuous. -/
def permutationalWreathProductInlContinuousHom :
    (S → A) →ₜ* PermutationalWreathProduct A S G where
  toMonoidHom := SemidirectProduct.inl
  continuous_toFun := by
    refine continuous_induced_rng.2 ?_
    change Continuous
      (fun f : S → A =>
        ((SemidirectProduct.inl f : PermutationalWreathProduct A S G).left,
          (SemidirectProduct.inl f : PermutationalWreathProduct A S G).right))
    simpa using (continuous_id.prodMk continuous_const)

/-- The canonical inclusion of the right factor is continuous. -/
def permutationalWreathProductInrContinuousHom :
    G →ₜ* PermutationalWreathProduct A S G where
  toMonoidHom := SemidirectProduct.inr
  continuous_toFun := by
    refine continuous_induced_rng.2 ?_
    change Continuous
      (fun g : G =>
        ((SemidirectProduct.inr g : PermutationalWreathProduct A S G).left,
          (SemidirectProduct.inr g : PermutationalWreathProduct A S G).right))
    simpa using (continuous_const.prodMk continuous_id)

/-- The projection to the right factor is a continuous homomorphism. -/
def permutationalWreathProductRightContinuousHom :
    PermutationalWreathProduct A S G →ₜ* G where
  toMonoidHom := SemidirectProduct.rightHom
  continuous_toFun := continuous_permutationalWreathProduct_right

end Topology

section ProCStructure

open ProCGroups.ProC

variable {C : FiniteGroupClass.{u}}
variable {A : Type u} {S : Type u} {G : Type u}
variable [Group A] [Group G] [MulAction G S] [Fintype S]
variable [TopologicalSpace A] [TopologicalSpace S] [TopologicalSpace G]
variable [IsTopologicalGroup A] [IsTopologicalGroup G]
variable [ContinuousSMul G S]

/-- The kernel of the right projection on a permutational wreath product. -/
abbrev permutationalWreathProductRightKernel :
    Subgroup (PermutationalWreathProduct A S G) :=
  (SemidirectProduct.rightHom : PermutationalWreathProduct A S G →* G).ker

/-- The canonical inclusion of the function factor, with codomain restricted to the kernel of the
right projection. -/
def permutationalWreathProductInlToKernelContinuousHom :
    (S → A) →ₜ* permutationalWreathProductRightKernel (A := A) (S := S) (G := G) where
  toMonoidHom :=
    { toFun := fun f => ⟨SemidirectProduct.inl f, by simp only
        [permutationalWreathProductRightKernel, MonoidHom.mem_ker,
        SemidirectProduct.rightHom_inl]⟩
      map_one' := by
        apply Subtype.ext
        simp only [map_one, OneMemClass.coe_one]
      map_mul' := by
        intro f g
        apply Subtype.ext
        simp only [map_mul, MulMemClass.mk_mul_mk]}
  continuous_toFun :=
    by
      exact Continuous.subtype_mk
        (permutationalWreathProductInlContinuousHom (A := A) (S := S) (G := G)).continuous_toFun
        (by
          intro f
          change (permutationalWreathProductInlContinuousHom (A := A) (S := S) (G := G) f).right = 1
          rfl)

omit [Fintype S] [TopologicalSpace S] [IsTopologicalGroup A] [IsTopologicalGroup G]
    [ContinuousSMul G S] in
/-- Inclusion of the function factor is a bijection onto the kernel of the right projection. -/
theorem permutationalWreathProductInlToKernel_bijective :
    Function.Bijective
      ((permutationalWreathProductInlToKernelContinuousHom (A := A) (S := S) (G := G)) :
        (S → A) → permutationalWreathProductRightKernel (A := A) (S := S) (G := G)) := by
  constructor
  · intro f g hfg
    funext s
    have hs := congrArg
      (fun x : permutationalWreathProductRightKernel (A := A) (S := S) (G := G) =>
        ((x : PermutationalWreathProduct A S G).left s)) hfg
    change f s = g s at hs
    exact hs
  · intro x
    refine ⟨x.1.left, ?_⟩
    have hmem :
        (SemidirectProduct.rightHom : PermutationalWreathProduct A S G →* G)
          x.1 = 1 := by
      exact x.2
    have hright : x.1.right = 1 := by
      simpa using hmem
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rfl
    · change (SemidirectProduct.inl x.1.left : PermutationalWreathProduct A S G).right =
          x.1.right
      simp only [SemidirectProduct.right_inl, hright]

/-- The kernel of the right projection is topologically isomorphic to the function factor. -/
noncomputable def permutationalWreathProductInlKernelContinuousMulEquiv
    [CompactSpace A] [T2Space A]
    [T2Space G] :
    (S → A) ≃ₜ* permutationalWreathProductRightKernel (A := A) (S := S) (G := G) :=
  ContinuousMulEquiv.ofBijectiveCompactToT2
    (permutationalWreathProductInlToKernelContinuousHom (A := A) (S := S) (G := G))
    (permutationalWreathProductInlToKernelContinuousHom (A := A) (S := S) (G := G)).continuous_toFun
    (permutationalWreathProductInlToKernel_bijective (A := A) (S := S) (G := G))

omit [Fintype S] in
/-- A permutational wreath product has an open-normal \(C\)-basis whenever both factors do and `C`
is closed under finite products and extensions. -/
theorem hasOpenNormalBasisInClass_permutationalWreathProduct
    [CompactSpace A] [T2Space A] [TotallyDisconnectedSpace A]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hForm : FiniteGroupClass.Formation C)
    (hIso : FiniteGroupClass.IsomClosed C)
    (hExt : FiniteGroupClass.ExtensionClosed C)
    [DiscreteTopology S]
    (hA : HasOpenNormalBasisInClass C A)
    (hG : HasOpenNormalBasisInClass C G) :
    HasOpenNormalBasisInClass C (PermutationalWreathProduct A S G) := by
  let hFunc : HasOpenNormalBasisInClass C (S → A) :=
    HasOpenNormalBasisInClass.pi (C := C) (α := S) (β := fun _ : S => A) hForm (fun _ => hA)
  have hKernel :
      HasOpenNormalBasisInClass C (permutationalWreathProductRightKernel (A := A) (S := S) (G :=
          G)) := by
    let e :=
      permutationalWreathProductInlKernelContinuousMulEquiv (A := A) (S := S) (G := G)
    exact HasOpenNormalBasisInClass.ofContinuousMulEquiv (C := C) hFunc e
  have hQuot :
      HasOpenNormalBasisInClass C
        ((PermutationalWreathProduct A S G) ⧸
          permutationalWreathProductRightKernel (A := A) (S := S) (G := G)) := by
    let α : PermutationalWreathProduct A S G →* G :=
      SemidirectProduct.rightHom
    have hα : Continuous α := continuous_permutationalWreathProduct_right
    have hαbar :
        Continuous (QuotientGroup.kerLift α :
          (PermutationalWreathProduct A S G) ⧸ α.ker →* G) := by
      refine (QuotientGroup.isQuotientMap_mk α.ker).continuous_iff.2 ?_
      change Continuous α
      exact hα
    let αbar : ((PermutationalWreathProduct A S G) ⧸ α.ker) →ₜ* G :=
      { toMonoidHom := QuotientGroup.kerLift α
        continuous_toFun := hαbar }
    have hαbar_bij : Function.Bijective αbar := by
      constructor
      · exact QuotientGroup.kerLift_injective α
      · intro g
        rcases (SemidirectProduct.rightHom_surjective
          (N := (S → A)) (G := G)
          (φ := mulAutArrow (G := G) (A := S) (M := A)) g) with ⟨x, rfl⟩
        refine ⟨QuotientGroup.mk' α.ker x, ?_⟩
        change α x = x.right
        rfl
    let e : ((PermutationalWreathProduct A S G) ⧸ α.ker) ≃ₜ* G :=
      ContinuousMulEquiv.ofBijectiveCompactToT2 αbar αbar.continuous_toFun hαbar_bij
    exact HasOpenNormalBasisInClass.ofContinuousMulEquiv (C := C) hG e.symm
  exact HasOpenNormalBasisInClass.extension (C := C) hIso hForm.quotientClosed hExt
    (permutationalWreathProductRightKernel (A := A) (S := S) (G := G))
    (ContinuousMonoidHom.isClosed_ker
      (permutationalWreathProductRightContinuousHom (A := A) (S := S) (G := G)))
    hKernel hQuot

end ProCStructure

section BasicLemmas

variable {A : Type u} {S : Type v} {G : Type w}
variable [Group A] [Group G] [MulAction G S]

/-- Pointwise multiplication formula in the permutational wreath product. -/
@[simp] theorem permutationalWreathProduct_mul_left_apply
    (x y : PermutationalWreathProduct A S G) (s : S) :
    (x * y).left s = x.left s * y.left (x.right⁻¹ • s) :=
  rfl

/-- Pointwise inversion formula in the permutational wreath product. -/
@[simp] theorem permutationalWreathProduct_inv_left_apply
    (x : PermutationalWreathProduct A S G) (s : S) :
    x⁻¹.left s = (x.left (x.right • s))⁻¹ := by
  change ((mulAutArrow (G := G) (A := S) (M := A) x.right⁻¹) (x.left⁻¹)) s =
      (x.left (x.right • s))⁻¹
  change x.left⁻¹ ((x.right⁻¹)⁻¹ • s) = (x.left (x.right • s))⁻¹
  simp only [inv_inv, Pi.inv_apply]

/-- The function coordinate of the left-factor inclusion is the included function. -/
@[simp] theorem permutationalWreathProduct_inl_left_apply
    (f : S → A) (s : S) :
    (SemidirectProduct.inl f : PermutationalWreathProduct A S G).left s = f s :=
  rfl

/-- The function coordinate of the right-factor inclusion is constantly one. -/
@[simp] theorem permutationalWreathProduct_inr_left_apply
    (g : G) (s : S) :
    (SemidirectProduct.inr g : PermutationalWreathProduct A S G).left s = 1 :=
  rfl

/-- The right projection is a retraction of the right-factor inclusion. -/
@[simp] theorem permutationalWreathProduct_rightHom_comp_inr :
    (SemidirectProduct.rightHom :
        PermutationalWreathProduct A S G →* G).comp SemidirectProduct.inr =
      MonoidHom.id G := by
  ext g
  rfl

end BasicLemmas

section LeftFactorFunctoriality

variable {A : Type u} {B : Type v} {S : Type w} {G : Type*}
variable [Group A] [Group B] [Group G] [MulAction G S]

/-- Pointwise application of a group homomorphism to the function factor of a wreath product. -/
def permutationalWreathProductMapFun (α : A →* B) : (S → A) →* (S → B) where
  toFun f := α ∘ f
  map_one' := by
    funext s
    simp only [Function.comp_apply, Pi.one_apply, map_one]
  map_mul' f g := by
    funext s
    simp only [Function.comp_apply, Pi.mul_apply, map_mul]

/-- Functoriality of the permutational wreath product in the left factor. -/
def permutationalWreathProductMapLeft (α : A →* B) :
    PermutationalWreathProduct A S G →* PermutationalWreathProduct B S G :=
  SemidirectProduct.map (permutationalWreathProductMapFun (S := S) α) (MonoidHom.id G) fun g => by
    ext f s
    rfl

/-- Mapping the left factor applies the given homomorphism pointwise to the function
coordinate. -/
@[simp] theorem permutationalWreathProductMapLeft_left_apply
    (α : A →* B) (x : PermutationalWreathProduct A S G) (s : S) :
    (permutationalWreathProductMapLeft (S := S) (G := G) α x).left s = α (x.left s) :=
  rfl

/-- Mapping the left factor leaves the acting-group coordinate unchanged. -/
@[simp] theorem permutationalWreathProductMapLeft_right
    (α : A →* B) (x : PermutationalWreathProduct A S G) :
    (permutationalWreathProductMapLeft (S := S) (G := G) α x).right = x.right :=
  rfl

/-- Injectivity of the left-factor map is inherited by the wreath-product map. -/
  theorem permutationalWreathProductMapLeft_injective
    (α : A →* B) (hα : Function.Injective α) :
    Function.Injective (permutationalWreathProductMapLeft (S := S) (G := G) α) := by
  intro x y hxy
  ext s
  · apply hα
    simpa using congrArg (fun z : PermutationalWreathProduct B S G => z.left s) hxy
  · simpa using congrArg (fun z : PermutationalWreathProduct B S G => z.right) hxy

/-- Surjectivity of the left-factor map is inherited by the wreath-product map. -/
theorem permutationalWreathProductMapLeft_surjective
    (α : A →* B) (hα : Function.Surjective α) :
    Function.Surjective (permutationalWreathProductMapLeft (S := S) (G := G) α) := by
  classical
  intro x
  let f : S → A := fun s => Classical.choose (hα (x.left s))
  refine ⟨⟨f, x.right⟩, ?_⟩
  ext s
  · exact Classical.choose_spec (hα (x.left s))
  · rfl

/-- If the wreath-product left-factor map is injective, then the original left-factor map is
injective. A chosen point of `Σ` extracts the relevant coordinate. -/
theorem injective_of_permutationalWreathProductMapLeft_injective
    (α : A →* B) (s : S)
    (hα : Function.Injective (permutationalWreathProductMapLeft (S := S) (G := G) α)) :
    Function.Injective α := by
  intro a b hab
  have hEq :
      permutationalWreathProductMapLeft (S := S) (G := G) α
          (SemidirectProduct.inl (fun _ : S => a) : PermutationalWreathProduct A S G) =
        permutationalWreathProductMapLeft (S := S) (G := G) α
          (SemidirectProduct.inl (fun _ : S => b) : PermutationalWreathProduct A S G) := by
    ext t
    · exact hab
    · rfl
  have hPre := hα hEq
  have := congrArg (fun z : PermutationalWreathProduct A S G => z.left s) hPre
  simpa using this

/-- If the wreath-product left-factor map is surjective, then the original left-factor map is
surjective. A chosen point of `Σ` extracts the relevant coordinate. -/
theorem surjective_of_permutationalWreathProductMapLeft_surjective
    (α : A →* B) (s : S)
    (hα : Function.Surjective (permutationalWreathProductMapLeft (S := S) (G := G) α)) :
    Function.Surjective α := by
  intro b
  obtain ⟨x, hx⟩ :=
    hα (SemidirectProduct.inl (fun _ : S => b) : PermutationalWreathProduct B S G)
  refine ⟨x.left s, ?_⟩
  have := congrArg (fun z : PermutationalWreathProduct B S G => z.left s) hx
  simpa using this

end LeftFactorFunctoriality

section LeftFactorFunctorialityTopological

variable {A : Type u} {B : Type v} {S : Type w} {G : Type*}
variable [Group A] [Group B] [Group G] [MulAction G S]
variable [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace G]

/-- Functoriality of the permutational wreath product in the left factor, upgraded to a continuous
homomorphism. -/
def permutationalWreathProductMapLeftContinuous
    (α : A →ₜ* B) :
    PermutationalWreathProduct A S G →ₜ* PermutationalWreathProduct B S G where
  toMonoidHom := permutationalWreathProductMapLeft (S := S) (G := G) α.toMonoidHom
  continuous_toFun := by
    refine continuous_induced_rng.2 ?_
    change Continuous
      (fun x : PermutationalWreathProduct A S G =>
        ((permutationalWreathProductMapLeft (S := S) (G := G) α.toMonoidHom x).left,
          (permutationalWreathProductMapLeft (S := S) (G := G) α.toMonoidHom x).right))
    have hleft :
        Continuous
          (fun x : PermutationalWreathProduct A S G =>
            (permutationalWreathProductMapLeft (S := S) (G := G) α.toMonoidHom x).left) := by
      refine continuous_pi ?_
      intro s
      change Continuous (fun x : PermutationalWreathProduct A S G => α (x.left s))
      have h := α.continuous_toFun.comp
        (continuous_permutationalWreathProduct_left_apply
          (A := A) (S := S) (G := G) s)
      change Continuous (fun x : PermutationalWreathProduct A S G => α (x.left s)) at h
      exact h
    have hright :
        Continuous
          (fun x : PermutationalWreathProduct A S G =>
            (permutationalWreathProductMapLeft (S := S) (G := G) α.toMonoidHom x).right) := by
      simpa using continuous_permutationalWreathProduct_right
    exact hleft.prodMk hright

end LeftFactorFunctorialityTopological

section StandardEmbedding

variable {G : Type u} [Group G]
variable (H : Subgroup G)

/--
The right-coset standard embedding carries the natural multiplication action used in the
wreath-product construction.
-/
instance instMulActionRightCosetStandardEmbedding :
    MulAction G (Quotient (QuotientGroup.rightRel H)) :=
  rightCosetMulAction H

attribute [-instance] instMulActionRightCosetStandardEmbedding

/-- The underlying section attached to a right transversal. -/
noncomputable def rightTransversalSection {T : Set G}
    (hT : Subgroup.IsComplement (H : Set G) T) :
    Quotient (QuotientGroup.rightRel H) → G :=
  fun q => (hT.rightQuotientEquiv q : G)

/-- The representative selected by a right transversal lies over the prescribed right coset. -/
@[simp] theorem rightTransversalSection_spec {T : Set G}
    (hT : Subgroup.IsComplement (H : Set G) T)
    (q : Quotient (QuotientGroup.rightRel H)) :
    Quotient.mk'' (rightTransversalSection (H := H) hT q) = q :=
  hT.mk''_rightQuotientEquiv q

/-- The cocycle attached to a section of the right quotient by `H`. -/
noncomputable def rightQuotientSectionCocycle
    (τ : Quotient (QuotientGroup.rightRel H) → G)
    (hτ : ∀ q, Quotient.mk'' (τ q) = q)
    (g : G) :
    Quotient (QuotientGroup.rightRel H) → H := by
  intro q
  refine ⟨τ q * g * (τ (g⁻¹ • q))⁻¹, ?_⟩
  have hq :
      Quotient.mk'' (τ q * g) = g⁻¹ • q := by
    calc
      Quotient.mk'' (τ q * g)
          = g⁻¹ • (Quotient.mk'' (τ q) : Quotient (QuotientGroup.rightRel H)) := by
              symm
              rw [rightCosetMulAction_inv_mk_smul (H := H) g (τ q)]
      _ = g⁻¹ • q := by rw [hτ q]
  have hEq :
      (Quotient.mk'' (τ q * g) : Quotient (QuotientGroup.rightRel H)) =
        Quotient.mk'' (τ (g⁻¹ • q)) := by
    calc
      (Quotient.mk'' (τ q * g) : Quotient (QuotientGroup.rightRel H))
          = g⁻¹ • q := hq
      _ = Quotient.mk'' (τ (g⁻¹ • q)) := by symm; exact hτ (g⁻¹ • q)
  have hrel : QuotientGroup.rightRel H (τ q * g) (τ (g⁻¹ • q)) := Quotient.exact' hEq
  rw [QuotientGroup.rightRel_apply] at hrel
  simpa [mul_inv_rev] using H.inv_mem hrel

/-- The standard wreath-product embedding attached to a section of the right quotient by `H`. -/
noncomputable def rightQuotientSectionEmbedding
    (τ : Quotient (QuotientGroup.rightRel H) → G)
    (hτ : ∀ q, Quotient.mk'' (τ q) = q) :
    G →* PermutationalWreathProduct H (Quotient (QuotientGroup.rightRel H)) G where
  toFun g := ⟨rightQuotientSectionCocycle (H := H) τ hτ g, g⟩
  map_one' := by
    apply SemidirectProduct.ext
    · funext q
      apply Subtype.ext
      simp only [rightQuotientSectionCocycle, mul_one, inv_one, one_smul, mul_inv_cancel,
  SemidirectProduct.one_left, Pi.one_apply, OneMemClass.coe_one]
    · rfl
  map_mul' g₁ g₂ := by
    apply SemidirectProduct.ext
    · funext q
      apply Subtype.ext
      simp only [rightQuotientSectionCocycle, mul_inv_rev, mul_smul, mul_assoc,
          SemidirectProduct.mk_eq_inl_mul_inr,
  permutationalWreathProduct_mul_left_apply, permutationalWreathProduct_inl_left_apply,
      SemidirectProduct.right_inl,
  inv_one, one_smul, permutationalWreathProduct_inr_left_apply, SemidirectProduct.right_inr,
      mul_one, one_mul,
  MulMemClass.mk_mul_mk, inv_mul_cancel_left]
    · rfl

/-- Pointwise formula for the standard wreath-product embedding attached to a right-quotient
section. -/
@[simp] theorem rightQuotientSectionEmbedding_left_apply
    (τ : Quotient (QuotientGroup.rightRel H) → G)
    (hτ : ∀ q, Quotient.mk'' (τ q) = q)
    (g : G) (q : Quotient (QuotientGroup.rightRel H)) :
    (rightQuotientSectionEmbedding (H := H) τ hτ g).left q =
      rightQuotientSectionCocycle (H := H) τ hτ g q :=
  rfl

/-- The standard wreath-product embedding preserves the acting-group coordinate. -/
@[simp] theorem rightQuotientSectionEmbedding_right
    (τ : Quotient (QuotientGroup.rightRel H) → G)
    (hτ : ∀ q, Quotient.mk'' (τ q) = q)
    (g : G) :
    (rightQuotientSectionEmbedding (H := H) τ hτ g).right = g :=
  rfl

/-- The right projection is a retraction of the standard right-quotient embedding. -/
@[simp] theorem rightQuotientSectionEmbedding_rightHom
    (τ : Quotient (QuotientGroup.rightRel H) → G)
    (hτ : ∀ q, Quotient.mk'' (τ q) = q) :
    (SemidirectProduct.rightHom :
        PermutationalWreathProduct H (Quotient (QuotientGroup.rightRel H)) G →* G).comp
        (rightQuotientSectionEmbedding (H := H) τ hτ) = MonoidHom.id G := by
  ext g
  rfl

/-- The standard embedding attached to a right-quotient section is injective. -/
theorem rightQuotientSectionEmbedding_injective
    (τ : Quotient (QuotientGroup.rightRel H) → G)
    (hτ : ∀ q, Quotient.mk'' (τ q) = q) :
    Function.Injective (rightQuotientSectionEmbedding (H := H) τ hτ) := by
  intro g₁ g₂ hEq
  simpa using congrArg
    (fun z :
      PermutationalWreathProduct H (Quotient (QuotientGroup.rightRel H)) G => z.right) hEq

end StandardEmbedding

section StandardEmbeddingTopological

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Subgroup G)

/--
The topological right-coset standard embedding carries the natural multiplication action used in
the wreath-product construction.
-/
instance instMulActionRightCosetStandardEmbeddingTopological :
    MulAction G (Quotient (QuotientGroup.rightRel H)) :=
  rightCosetMulAction H

attribute [-instance] instMulActionRightCosetStandardEmbeddingTopological

/-- A continuous right-quotient section gives a continuous standard wreath-product
embedding. -/
theorem continuous_rightQuotientSectionEmbedding
    [TopologicalSpace (Quotient (QuotientGroup.rightRel H))]
    [DiscreteTopology (Quotient (QuotientGroup.rightRel H))]
    (hH : IsOpen (H : Set G))
    (τ : Quotient (QuotientGroup.rightRel H) → G)
    (hτ : ∀ q, Quotient.mk'' (τ q) = q)
    (hτcont : Continuous τ) :
    Continuous
      (rightQuotientSectionEmbedding (H := H) τ hτ :
        G → PermutationalWreathProduct H (Quotient (QuotientGroup.rightRel H)) G) := by
  refine continuous_induced_rng.2 ?_
  change Continuous fun g : G =>
    ((rightQuotientSectionEmbedding (H := H) τ hτ g).left,
      (rightQuotientSectionEmbedding (H := H) τ hτ g).right)
  have hleft :
      Continuous fun g : G =>
        (rightQuotientSectionEmbedding (H := H) τ hτ g).left := by
    refine continuous_pi ?_
    intro q
    refine Continuous.subtype_mk ?_ ?_
    have hqcont :
        Continuous fun g : G => (g⁻¹ • q : Quotient (QuotientGroup.rightRel H)) :=
      continuous_rightCosetMulAction_inv_smul_of_open (G := G) H hH q
    have hcont :
        Continuous fun g : G => τ q * g * (τ (g⁻¹ • q))⁻¹ := by
      exact (continuous_const.mul continuous_id).mul ((hτcont.comp hqcont).inv)
    simpa [rightQuotientSectionEmbedding, rightQuotientSectionCocycle, mul_assoc] using hcont
  have hright :
      Continuous fun g : G =>
        (rightQuotientSectionEmbedding (H := H) τ hτ g).right := by
    change Continuous (id : G → G)
    exact continuous_id
  exact hleft.prodMk hright

end StandardEmbeddingTopological

section CocycleFormulas

variable {A : Type u} {S : Type v} {G : Type w}
variable [Group A] [Group G] [MulAction G S]

/-- The left coordinate of an element of a wreath product, viewed as a function of the group
element on the source. -/
def wreathLeftCoordinate
    (ψ : G →* PermutationalWreathProduct A S G) (s : S) : G → A :=
  fun g => (ψ g).left s

/-- The cocycle formula for the left coordinates of a homomorphism into a wreath product whose
right factor is the identity. -/
theorem wreathLeftCoordinate_mul
    (ψ : G →* PermutationalWreathProduct A S G)
    (hψ :
      (SemidirectProduct.rightHom : PermutationalWreathProduct A S G →* G).comp ψ =
        MonoidHom.id G)
    (s : S) (g₁ g₂ : G) :
    wreathLeftCoordinate ψ s (g₁ * g₂) =
      wreathLeftCoordinate ψ s g₁ *
        wreathLeftCoordinate ψ (g₁⁻¹ • s) g₂ := by
  have hright : (ψ g₁).right = g₁ := by
    simpa using congrArg (fun f : G →* G => f g₁) hψ
  simp only [wreathLeftCoordinate, map_mul, permutationalWreathProduct_mul_left_apply, hright]

/-- Inversion formula for the left coordinates of a homomorphism into a wreath product whose
right factor is the identity. -/
theorem wreathLeftCoordinate_inv
    (ψ : G →* PermutationalWreathProduct A S G)
    (hψ :
      (SemidirectProduct.rightHom : PermutationalWreathProduct A S G →* G).comp ψ =
        MonoidHom.id G)
    (s : S) (g : G) :
    wreathLeftCoordinate ψ s g⁻¹ =
      (wreathLeftCoordinate ψ (g • s) g)⁻¹ := by
  have hright : (ψ g).right = g := by
    simpa using congrArg (fun f : G →* G => f g) hψ
  simp only [wreathLeftCoordinate, map_inv, permutationalWreathProduct_inv_left_apply, hright]

end CocycleFormulas

section RightQuotientCoordinateRecovery

variable {A : Type u} {G : Type v}
variable [Group A] [Group G]
variable (H : Subgroup G)

/--
The coordinate-recovery map for the right-coset standard embedding is compatible with the
natural multiplication action.
-/
instance instMulActionRightCosetCoordinateRecovery :
    MulAction G (Quotient (QuotientGroup.rightRel H)) :=
  rightCosetMulAction H

attribute [-instance] instMulActionRightCosetCoordinateRecovery

/-- Basepoint form: if a homomorphism into the wreath product has identity right
factor and sends the chosen section to elements whose basepoint coordinate is trivial, then the
basepoint coordinate of the induced subgroup cocycle recovers the original left coordinate. -/
theorem wreathLeftCoordinate_eq_basepoint_of_rightQuotientSection
    (τ : Quotient (QuotientGroup.rightRel H) → G)
    (hτ : ∀ q, Quotient.mk'' (τ q) = q)
    (ψ : G →* PermutationalWreathProduct A (Quotient (QuotientGroup.rightRel H)) G)
    (hψ :
      (SemidirectProduct.rightHom :
          PermutationalWreathProduct A (Quotient (QuotientGroup.rightRel H)) G →* G).comp ψ =
        MonoidHom.id G)
    (hτpure :
      ∀ q : Quotient (QuotientGroup.rightRel H),
        wreathLeftCoordinate ψ
            (Quotient.mk'' (1 : G) : Quotient (QuotientGroup.rightRel H)) (τ q) = 1)
    (g : G) (q : Quotient (QuotientGroup.rightRel H)) :
    wreathLeftCoordinate ψ
        (Quotient.mk'' (1 : G) : Quotient (QuotientGroup.rightRel H))
        (rightQuotientSectionCocycle (H := H) τ hτ g q) =
      wreathLeftCoordinate ψ q g := by
  let q' : Quotient (QuotientGroup.rightRel H) := g⁻¹ • q
  have hτq :
      (τ q)⁻¹ • (Quotient.mk'' (1 : G) : Quotient (QuotientGroup.rightRel H)) = q := by
    rw [rightCosetMulAction_inv_mk_smul (H := H) (τ q) 1]
    simpa using hτ q
  have hτq' :
      τ q' • q' = (Quotient.mk'' (1 : G) : Quotient (QuotientGroup.rightRel H)) := by
    calc
      τ q' • q' = τ q' • (Quotient.mk'' (τ q') : Quotient (QuotientGroup.rightRel H)) := by
        rw [hτ q']
      _ = Quotient.mk'' (1 : G) := by
        rw [rightCosetMulAction_mk_smul (H := H) (τ q') (τ q')]
        simp only [mul_inv_cancel]
  have hinv :
      wreathLeftCoordinate ψ q' (τ q')⁻¹ = 1 := by
    rw [wreathLeftCoordinate_inv (ψ := ψ) hψ q' (τ q')]
    simpa [hτq'] using hτpure q'
  have hq' :
      (Quotient.mk'' (τ q * g) : Quotient (QuotientGroup.rightRel H)) = q' := by
    calc
      (Quotient.mk'' (τ q * g) : Quotient (QuotientGroup.rightRel H))
          = (τ q * g)⁻¹ • (Quotient.mk'' (1 : G) : Quotient (QuotientGroup.rightRel H)) := by
              simp only [mul_inv_rev, rightCosetMulAction_mk_smul, inv_inv, one_mul]
      _ = g⁻¹ • ((τ q)⁻¹ • (Quotient.mk'' (1 : G) : Quotient (QuotientGroup.rightRel H))) := by
            simp only [mul_inv_rev, mul_smul, rightCosetMulAction_mk_smul, inv_inv, one_mul]
      _ = g⁻¹ • q := by rw [hτq]
      _ = q' := rfl
  change
      wreathLeftCoordinate ψ
          (Quotient.mk'' (1 : G) : Quotient (QuotientGroup.rightRel H))
          ((τ q * g) * (τ q')⁻¹) =
        wreathLeftCoordinate ψ q g
  rw [wreathLeftCoordinate_mul (ψ := ψ) hψ
      (Quotient.mk'' (1 : G) : Quotient (QuotientGroup.rightRel H))
      (τ q * g) (τ q')⁻¹]
  rw [wreathLeftCoordinate_mul (ψ := ψ) hψ
      (Quotient.mk'' (1 : G) : Quotient (QuotientGroup.rightRel H))
      (τ q) g]
  simp only [hτpure, hτq, one_mul, mul_inv_rev, rightCosetMulAction_mk_smul, inv_inv, hq', hinv,
      mul_one, q']

/-- Basepoint evaluation on the stabilizer subgroup of the trivial right coset, expressed for a
homomorphism into the wreath product whose right factor is the identity. -/
def rightQuotientBasepointProjectionHom
    (ψ : G →* PermutationalWreathProduct A (Quotient (QuotientGroup.rightRel H)) G)
    (hψ :
      (SemidirectProduct.rightHom :
          PermutationalWreathProduct A (Quotient (QuotientGroup.rightRel H)) G →* G).comp ψ =
        MonoidHom.id G) :
    H →* A where
  toFun h :=
    wreathLeftCoordinate ψ
      (Quotient.mk'' (1 : G) : Quotient (QuotientGroup.rightRel H)) h.1
  map_one' := by
    simp only [wreathLeftCoordinate, OneMemClass.coe_one, map_one, SemidirectProduct.one_left,
        Pi.one_apply]
  map_mul' a b := by
    change
      wreathLeftCoordinate ψ
          (Quotient.mk'' (1 : G) : Quotient (QuotientGroup.rightRel H))
          (a.1 * b.1) =
        wreathLeftCoordinate ψ
            (Quotient.mk'' (1 : G) : Quotient (QuotientGroup.rightRel H)) a.1 *
          wreathLeftCoordinate ψ
            (Quotient.mk'' (1 : G) : Quotient (QuotientGroup.rightRel H)) b.1
    rw [wreathLeftCoordinate_mul (ψ := ψ) hψ
      (Quotient.mk'' (1 : G) : Quotient (QuotientGroup.rightRel H)) a.1 b.1]
    have ha :
        a.1⁻¹ • (Quotient.mk'' (1 : G) : Quotient (QuotientGroup.rightRel H)) =
          (Quotient.mk'' (1 : G) : Quotient (QuotientGroup.rightRel H)) := by
      rw [rightCosetMulAction_inv_mk_smul (H := H) a.1 1]
      apply Quotient.sound'
      rw [QuotientGroup.rightRel_apply]
      simp only [one_mul, H.inv_mem a.2]
    simp only [ha]

/-- The basepoint projection on `H` evaluates the section cocycle by the corresponding left
coordinate, provided the chosen section has trivial basepoint coordinate. -/
theorem rightQuotientBasepointProjectionHom_apply_cocycle
    (τ : Quotient (QuotientGroup.rightRel H) → G)
    (hτ : ∀ q, Quotient.mk'' (τ q) = q)
    (ψ : G →* PermutationalWreathProduct A (Quotient (QuotientGroup.rightRel H)) G)
    (hψ :
      (SemidirectProduct.rightHom :
          PermutationalWreathProduct A (Quotient (QuotientGroup.rightRel H)) G →* G).comp ψ =
        MonoidHom.id G)
    (hτpure :
      ∀ q : Quotient (QuotientGroup.rightRel H),
        wreathLeftCoordinate ψ
            (Quotient.mk'' (1 : G) : Quotient (QuotientGroup.rightRel H)) (τ q) = 1)
    (g : G) (q : Quotient (QuotientGroup.rightRel H)) :
    rightQuotientBasepointProjectionHom (H := H) ψ hψ
        (rightQuotientSectionCocycle (H := H) τ hτ g q) =
      wreathLeftCoordinate ψ q g :=
  wreathLeftCoordinate_eq_basepoint_of_rightQuotientSection
    (H := H) τ hτ ψ hψ hτpure g q

end RightQuotientCoordinateRecovery

section StabilizerProjection

variable {A : Type u} {S : Type v} {G : Type w}
variable [Group A] [Group G] [MulAction G S]

/-- Evaluation at a fixed point is a homomorphism on the wreath product over the stabilizer of
that point. -/
def wreathStabilizerProjection (s : S) :
    PermutationalWreathProduct A S (MulAction.stabilizer G s) →* A where
  toFun x := x.left s
  map_one' := rfl
  map_mul' x y := by
    have hx : x.right⁻¹ • s = s := by
      exact MulAction.mem_stabilizer_iff.mp x.right⁻¹.2
    simp only [permutationalWreathProduct_mul_left_apply, hx]

/-- The stabilizer projection evaluates the function coordinate at the fixed point. -/
@[simp] theorem wreathStabilizerProjection_apply
    (s : S) (x : PermutationalWreathProduct A S (MulAction.stabilizer G s)) :
    wreathStabilizerProjection (A := A) (G := G) s x = x.left s :=
  rfl

/-- The stabilizer projection is natural in the left factor. -/
@[simp] theorem wreathStabilizerProjection_mapLeft
    {B : Type*} [Group B]
    (α : A →* B) (s : S)
    (x : PermutationalWreathProduct A S (MulAction.stabilizer G s)) :
    wreathStabilizerProjection (A := B) (G := G) s
        (permutationalWreathProductMapLeft
          (S := S) (G := MulAction.stabilizer G s) α x) =
      α (wreathStabilizerProjection (A := A) (G := G) s x) := by
  rfl

section RightQuotientBasepoint

variable {H : Subgroup G}

/-- Basepoint form: on the subgroup `H`, the left coordinate of the standard
embedding at the trivial right coset is the given element, provided the section is normalized at
the basepoint. -/
@[simp 900] theorem rightQuotientSectionEmbedding_left_basepoint_of_mem
    (τ : Quotient (QuotientGroup.rightRel H) → G)
    (hτ : ∀ q, Quotient.mk'' (τ q) = q)
    (hτ1 : τ (Quotient.mk'' (1 : G) : Quotient (QuotientGroup.rightRel H)) = 1)
    {g : G} (hg : g ∈ H) :
    (rightQuotientSectionEmbedding (H := H) τ hτ g).left
        (Quotient.mk'' (1 : G) : Quotient (QuotientGroup.rightRel H)) =
      ⟨g, hg⟩ := by
  apply Subtype.ext
  have hq :
      (g⁻¹ •
          (Quotient.mk'' (1 : G) : Quotient (QuotientGroup.rightRel H))) =
        (Quotient.mk'' (1 : G) : Quotient (QuotientGroup.rightRel H)) := by
    rw [rightCosetMulAction_mk_smul (H := H) g⁻¹ 1]
    apply Quotient.sound'
    rw [QuotientGroup.rightRel_apply]
    simpa using hg
  simp only [rightQuotientSectionEmbedding, SemidirectProduct.mk_eq_inl_mul_inr, MonoidHom.coe_mk,
  OneHom.coe_mk, permutationalWreathProduct_mul_left_apply,
      permutationalWreathProduct_inl_left_apply,
  rightQuotientSectionCocycle, hτ1, one_mul, hq, inv_one, mul_one, SemidirectProduct.right_inl,
      one_smul,
  permutationalWreathProduct_inr_left_apply]

end RightQuotientBasepoint

end StabilizerProjection

end ProCGroups.WreathProducts

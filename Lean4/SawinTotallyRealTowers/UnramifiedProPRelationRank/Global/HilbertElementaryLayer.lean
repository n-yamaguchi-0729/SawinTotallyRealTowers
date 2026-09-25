/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.AlgebraicNumberTheory.Galois.NormalFieldRange
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.EverywhereUnramifiedBridge
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.PClassGroup
import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldReciprocity.SmallOriginal
import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassFieldMaximalSubextension
import ProCGroups.Topologies.QuotientMaps

set_option autoImplicit false
/-!
# The elementary Hilbert class-field layer

This file cuts out the exponent-`p` layer of the small Hilbert class field and
identifies its Galois group with the ordinary class group modulo `p`th powers.
It also realizes that layer in the canonical algebraic closure and records its
maximality among finite abelian everywhere-unramified exponent-`p` extensions.
-/

open scoped NumberField IsMulCommutative

noncomputable section

open GlobalClassFieldTheory GlobalClassFieldTheory.GlobalClassFields

namespace ClassFieldTower.Martinet

open ClassFieldTower.ProP

variable (K : Type) [Field K] [NumberField K]

/-- The subgroup cutting out the elementary abelian `p` layer of the small
Hilbert class field. -/
def hilbertPSubgroup (p : ℕ) :
    Subgroup Gal((smallHilbertClassField K) / K) :=
  powerSubgroup p Gal((smallHilbertClassField K) / K)

local instance hilbertPSubgroup_normal (p : ℕ) :
    (hilbertPSubgroup K p).Normal := inferInstance

/-- The elementary abelian `p` layer inside the small Hilbert class field. -/
def hilbertElementaryLayer (p : ℕ) :
    IntermediateField K (smallHilbertClassField K) :=
  IntermediateField.fixedField (hilbertPSubgroup K p)

/-- The elementary Hilbert layer is Galois over its base field. -/
theorem hilbertElementaryLayer_isGalois (p : ℕ) :
    IsGalois K (hilbertElementaryLayer K p) :=
  IsGalois.of_fixedField_normal_subgroup (hilbertPSubgroup K p)

/-- The canonical Galois instance for the elementary Hilbert layer. -/
instance hilbertElementaryLayer.instIsGalois (p : ℕ) :
    IsGalois K (hilbertElementaryLayer K p) :=
  hilbertElementaryLayer_isGalois K p

/-- The elementary Hilbert layer is everywhere unramified over its base
field. -/
theorem hilbertElementaryLayer_isEverywhereUnramified (p : ℕ) :
    IsEverywhereUnramified K (hilbertElementaryLayer K p) := by
  exact IsEverywhereUnramified.bot
    (k := K) (K := hilbertElementaryLayer K p)
    (F := smallHilbertClassField K)
    (smallHilbertClassField_isEverywhereUnramified (K := K))

/-- Hilbert reciprocity transports the elementary layer to the ordinary
`p`-class quotient. -/
noncomputable def hilbertElementaryGaloisEquivPClassGroup (p : ℕ) :
    Gal((hilbertElementaryLayer K p) / K) ≃* PClassGroup K p := by
  let e : Gal((smallHilbertClassField K) / K) ≃* ClassGroup (𝓞 K) :=
    smallHilbertClassFieldGaloisEquivClassGroupOverOriginal (K := K)
  let q :
      Gal((smallHilbertClassField K) / K) ⧸ hilbertPSubgroup K p ≃*
        PClassGroup K p :=
    ProCGroups.QuotientGroup.mapMulEquivOfSurjective e.toMonoidHom e.surjective
      (powerSubgroup_map_mulEquiv p e) (by
        intro x hx
        have hx1 : x = 1 := e.injective (by simpa using hx)
        subst x
        exact Subgroup.one_mem _)
  exact (IsGalois.normalAutEquivQuotient (hilbertPSubgroup K p)).symm.trans q

/-- Every automorphism of the elementary Hilbert layer has exponent dividing
`p`. -/
theorem hilbertElementaryGalois_pow_eq_one (p : ℕ)
    (x : Gal((hilbertElementaryLayer K p) / K)) : x ^ p = 1 := by
  let e := hilbertElementaryGaloisEquivPClassGroup K p
  apply e.injective
  calc
    e (x ^ p) = (e x) ^ p := map_pow e x p
    _ = 1 := pClassGroup_pow_eq_one K p (e x)
    _ = e 1 := (map_one e).symm

/-- The Galois rank of the elementary Hilbert layer is the `p`-class rank. -/
theorem finrank_hilbertElementaryGalois_eq_pClassRank
    (p : ℕ) [Fact (Nat.Prime p)] :
    letI : Module (ZMod p)
        (Additive Gal((hilbertElementaryLayer K p) / K)) :=
      AddCommGroup.zmodModule (fun x => by
        change (Additive.toMul x) ^ p = 1
        exact hilbertElementaryGalois_pow_eq_one K p (Additive.toMul x))
    Module.finrank (ZMod p)
        (Additive Gal((hilbertElementaryLayer K p) / K)) = pClassRank K p := by
  let : Module (ZMod p) (Additive (PClassGroup K p)) :=
    AddCommGroup.zmodModule (fun x => by
      change (Additive.toMul x) ^ p = 1
      exact pClassGroup_pow_eq_one K p (Additive.toMul x))
  let : Module (ZMod p)
      (Additive Gal((hilbertElementaryLayer K p) / K)) :=
    AddCommGroup.zmodModule (fun x => by
      change (Additive.toMul x) ^ p = 1
      exact hilbertElementaryGalois_pow_eq_one K p (Additive.toMul x))
  let e : Additive Gal((hilbertElementaryLayer K p) / K) ≃+
      Additive (PClassGroup K p) :=
    (hilbertElementaryGaloisEquivPClassGroup K p).toAdditive
  let eLin : Additive Gal((hilbertElementaryLayer K p) / K) ≃ₗ[ZMod p]
      Additive (PClassGroup K p) :=
    LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap p) e.bijective
  exact eLin.finrank_eq

/-- A chosen realization of the Hilbert elementary layer in the canonical
algebraic closure. -/
noncomputable def hilbertElementaryLayerEmbedding (p : ℕ) :
    hilbertElementaryLayer K p →ₐ[K] AlgebraicClosure K :=
  IsSepClosed.lift

/-- The realized Hilbert elementary layer in `AlgebraicClosure K`. -/
noncomputable def hilbertElementaryLayerInAlgebraicClosure (p : ℕ) :
    IntermediateField K (AlgebraicClosure K) :=
  (hilbertElementaryLayerEmbedding K p).fieldRange

/-- The abstract and realized elementary Hilbert layers are equivalent over
`K`. -/
noncomputable def hilbertElementaryLayerEquivInAlgebraicClosure (p : ℕ) :
    hilbertElementaryLayer K p ≃ₐ[K]
      hilbertElementaryLayerInAlgebraicClosure K p :=
  (hilbertElementaryLayerEmbedding K p).equivFieldRange

/-- The realized elementary Hilbert layer is finite-dimensional over its base
field. -/
instance hilbertElementaryLayerInAlgebraicClosure.instFiniteDimensional
    (p : ℕ) :
    FiniteDimensional K
      (hilbertElementaryLayerInAlgebraicClosure K p) :=
  (hilbertElementaryLayerEquivInAlgebraicClosure K p).toLinearEquiv.finiteDimensional

/-- The realized elementary Hilbert layer is a number field. -/
instance hilbertElementaryLayerInAlgebraicClosure.instNumberField
    (p : ℕ) :
    NumberField (hilbertElementaryLayerInAlgebraicClosure K p) :=
  NumberField.of_module_finite K
    (hilbertElementaryLayerInAlgebraicClosure K p)

/-- The realized elementary Hilbert layer is Galois over its base field. -/
instance hilbertElementaryLayerInAlgebraicClosure.instIsGalois
    (p : ℕ) :
    IsGalois K (hilbertElementaryLayerInAlgebraicClosure K p) :=
  IsGalois.of_algEquiv
    (hilbertElementaryLayerEquivInAlgebraicClosure K p)

/-- The realized elementary Hilbert layer is abelian Galois over its base
field. -/
instance hilbertElementaryLayerInAlgebraicClosure.instIsAbelianGalois
    (p : ℕ) :
    IsAbelianGalois K
      (hilbertElementaryLayerInAlgebraicClosure K p) :=
  IsAbelianGalois.of_algHom
    (hilbertElementaryLayerEquivInAlgebraicClosure K p).symm.toAlgHom

/-- The realized elementary Hilbert layer is everywhere unramified over its
base field. -/
theorem hilbertElementaryLayerInAlgebraicClosure_isEverywhereUnramified
    (p : ℕ) :
    IsEverywhereUnramified K
      (hilbertElementaryLayerInAlgebraicClosure K p) :=
  everywhereUnramified_congrTop
    (hilbertElementaryLayerEquivInAlgebraicClosure K p)
    (hilbertElementaryLayer_isEverywhereUnramified K p)

/-- Every finite abelian everywhere-unramified exponent-`p` subfield of the
canonical algebraic closure lies in the realized Hilbert elementary layer. -/
theorem finiteElementaryUnramified_le_hilbertElementaryLayer
    (p : ℕ)
    (L : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L] [IsAbelianGalois K L] [NumberField L]
    (hL : IsEverywhereUnramified K L)
    (hExp : ∀ σ : Gal(L / K), σ ^ p = 1) :
    L ≤ hilbertElementaryLayerInAlgebraicClosure K p := by
  let : IsUnramifiedAtInfinitePlaces K L := hL.infinitePlaces
  have hRam : ramifiedBaseFinitePlaces (K := K) (L := L) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨P, _hP, hP⟩ :=
      (mem_ramifiedBaseFinitePlaces_iff (K := K) (L := L) v).1 hv
    exact hP (hL.finitePlaces P)
  obtain ⟨j⟩ :=
    finiteAbelianExtension_nonempty_algHom_to_smallHilbertClassField_of_everywhereUnramified
      (K := K) (L := L) hRam
  let R : IntermediateField K (smallHilbertClassField K) := j.fieldRange
  let eLR : L ≃ₐ[K] R := j.equivFieldRange
  let : IsGalois K R := IsGalois.of_algEquiv eLR
  have hRExp : ∀ τ : Gal(R / K), τ ^ p = 1 := by
    intro τ
    let eAut : Gal(L / K) ≃* Gal(R / K) := AlgEquiv.autCongr eLR
    let σ : Gal(L / K) := eAut.symm τ
    calc
      τ ^ p = (eAut σ) ^ p := congrArg (fun z : Gal(R / K) => z ^ p)
        (eAut.apply_symm_apply τ).symm
      _ = eAut (σ ^ p) := (map_pow eAut σ p).symm
      _ = eAut 1 := congrArg eAut (hExp σ)
      _ = 1 := map_one eAut
  have hPowFix : hilbertPSubgroup K p ≤ R.fixingSubgroup := by
    rw [← R.restrictNormalHom_ker]
    rw [hilbertPSubgroup, powerSubgroup, Subgroup.closure_le]
    rintro _ ⟨σ, rfl⟩
    change AlgEquiv.restrictNormalHom R (σ ^ p) = 1
    calc
      AlgEquiv.restrictNormalHom R (σ ^ p) =
          (AlgEquiv.restrictNormalHom R σ) ^ p :=
        map_pow (AlgEquiv.restrictNormalHom R) σ p
      _ = 1 := hRExp (AlgEquiv.restrictNormalHom R σ)
  have hRle : R ≤ hilbertElementaryLayer K p := by
    rw [hilbertElementaryLayer, IntermediateField.le_iff_le]
    exact hPowFix
  let jE : L →ₐ[K] hilbertElementaryLayer K p :=
    j.codRestrict (hilbertElementaryLayer K p).toSubalgebra
      (fun x => hRle (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩))
  let k : L →ₐ[K] AlgebraicClosure K :=
    (hilbertElementaryLayerEmbedding K p).comp jE
  have hkRange : k.fieldRange ≤
      hilbertElementaryLayerInAlgebraicClosure K p := by
    intro x hx
    rcases AlgHom.mem_fieldRange.mp hx with ⟨y, rfl⟩
    exact AlgHom.mem_fieldRange.mpr ⟨jE y, rfl⟩
  have hRangeEq : k.fieldRange = L := by
    calc
      k.fieldRange = (IntermediateField.val L).fieldRange :=
        AlgHom.fieldRange_eq_of_normal k (IntermediateField.val L)
      _ = L := IntermediateField.fieldRange_val L
  rwa [hRangeEq] at hkRange

end ClassFieldTower.Martinet

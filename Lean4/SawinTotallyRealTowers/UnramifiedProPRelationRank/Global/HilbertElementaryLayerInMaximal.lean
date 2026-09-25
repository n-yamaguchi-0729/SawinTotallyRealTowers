/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.HilbertElementaryLayer
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.MaximalEverywhereUnramifiedProP

set_option autoImplicit false
/-!
# The elementary Hilbert layer inside the maximal unramified pro-p extension

This file places the realized elementary Hilbert class-field layer inside the
maximal everywhere-unramified pro-`p` extension. It identifies the resulting
intermediate field with the abstract Hilbert layer and transports its finite,
abelian Galois, exponent, and rank data.
-/

open scoped NumberField IsMulCommutative

noncomputable section

open GlobalClassFieldTheory GlobalClassFieldTheory.GlobalClassFields

namespace ClassFieldTower.Martinet

variable (K : Type) [Field K] [NumberField K]

/-- The realized elementary Hilbert layer is contained in the maximal
everywhere-unramified pro-`p` extension. -/
theorem hilbertElementaryLayerInAlgebraicClosure_le_maximal
    (p : ℕ) [Fact p.Prime] :
    hilbertElementaryLayerInAlgebraicClosure K p ≤
      maximalEverywhereUnramifiedProP K p := by
  let E := hilbertElementaryLayer K p
  let EΩ := hilbertElementaryLayerInAlgebraicClosure K p
  let e : E ≃ₐ[K] EΩ :=
    hilbertElementaryLayerEquivInAlgebraicClosure K p
  let : FiniteDimensional K EΩ :=
    e.toLinearEquiv.finiteDimensional
  let : IsGalois K EΩ := IsGalois.of_algEquiv e
  let : NumberField EΩ := NumberField.of_module_finite K EΩ
  have hAbstract : IsEverywhereUnramified K E :=
    IsEverywhereUnramified.bot
      (smallHilbertClassField_isEverywhereUnramified K)
  have hUnramified : IsEverywhereUnramified K EΩ :=
    everywhereUnramified_congrTop e hAbstract
  have hExp : ∀ τ : Gal(EΩ / K), τ ^ p = 1 := by
    intro τ
    let eAut : Gal(E / K) ≃* Gal(EΩ / K) := AlgEquiv.autCongr e
    let σ : Gal(E / K) := eAut.symm τ
    calc
      τ ^ p = (eAut σ) ^ p :=
        congrArg (fun z : Gal(EΩ / K) ↦ z ^ p)
          (eAut.apply_symm_apply τ).symm
      _ = eAut (σ ^ p) := (map_pow eAut σ p).symm
      _ = eAut 1 :=
        congrArg eAut (hilbertElementaryGalois_pow_eq_one K p σ)
      _ = 1 := map_one eAut
  have hP : IsPGroup p Gal(EΩ / K) := by
    intro τ
    exact ⟨1, by simpa using hExp τ⟩
  exact le_maximalEverywhereUnramifiedProP K p EΩ hP hUnramified

/-- The elementary Hilbert layer, viewed inside the maximal extension. -/
noncomputable def hilbertElementaryLayerInMaximal
    (p : ℕ) [Fact p.Prime] :
    IntermediateField K (maximalEverywhereUnramifiedProP K p) :=
  (hilbertElementaryLayerInAlgebraicClosure K p).comap
    (IntermediateField.val (maximalEverywhereUnramifiedProP K p))

/-- The abstract Hilbert layer is equivalent to its copy inside the maximal
extension. -/
noncomputable def hilbertElementaryLayerEquivInMaximal
    (p : ℕ) [Fact p.Prime] :
    hilbertElementaryLayer K p ≃ₐ[K]
      hilbertElementaryLayerInMaximal K p := by
  let h : hilbertElementaryLayerInAlgebraicClosure K p ≤
      maximalEverywhereUnramifiedProP K p :=
    hilbertElementaryLayerInAlgebraicClosure_le_maximal K p
  have hr : IntermediateField.restrict h =
      hilbertElementaryLayerInMaximal K p := by
    ext x
    rw [IntermediateField.mem_restrict]
    rfl
  exact
    (hilbertElementaryLayerEquivInAlgebraicClosure K p).trans
      ((IntermediateField.restrictAlgEquiv h).trans
        (IntermediateField.equivOfEq hr))

/-- Finite-dimensionality transported to the copy in the maximal extension. -/
noncomputable instance hilbertElementaryLayerInMaximal.instFiniteDimensional
    (p : ℕ) [Fact p.Prime] :
    FiniteDimensional K (hilbertElementaryLayerInMaximal K p) :=
  (hilbertElementaryLayerEquivInMaximal K p).toLinearEquiv.finiteDimensional

/-- Galoisness transported to the copy in the maximal extension. -/
instance hilbertElementaryLayerInMaximal.instIsGalois
    (p : ℕ) [Fact p.Prime] :
    IsGalois K (hilbertElementaryLayerInMaximal K p) :=
  IsGalois.of_algEquiv (hilbertElementaryLayerEquivInMaximal K p)

/-- The copy in the maximal extension is an abelian Galois extension. -/
theorem hilbertElementaryLayerInMaximal_isAbelianGalois
    (p : ℕ) [Fact p.Prime] :
    IsAbelianGalois K (hilbertElementaryLayerInMaximal K p) := by
  let : IsAbelianGalois K (hilbertElementaryLayer K p) :=
    IsAbelianGalois.of_algHom
      (IntermediateField.val (hilbertElementaryLayer K p))
  exact IsAbelianGalois.of_algHom
    (hilbertElementaryLayerEquivInMaximal K p).symm.toAlgHom

/-- The canonical abelian Galois instance for the copy in the maximal
extension. -/
instance hilbertElementaryLayerInMaximal.instIsAbelianGalois
    (p : ℕ) [Fact p.Prime] :
    IsAbelianGalois K (hilbertElementaryLayerInMaximal K p) :=
  hilbertElementaryLayerInMaximal_isAbelianGalois K p

/-- The Galois group of the copy has exponent dividing `p`. -/
theorem hilbertElementaryLayerInMaximal_galois_pow_eq_one
    (p : ℕ) [Fact p.Prime]
    (τ : Gal((hilbertElementaryLayerInMaximal K p) / K)) :
    τ ^ p = 1 := by
  let eAut : Gal((hilbertElementaryLayer K p) / K) ≃*
      Gal((hilbertElementaryLayerInMaximal K p) / K) :=
    AlgEquiv.autCongr (hilbertElementaryLayerEquivInMaximal K p)
  let σ : Gal((hilbertElementaryLayer K p) / K) := eAut.symm τ
  calc
    τ ^ p = (eAut σ) ^ p :=
      congrArg
        (fun z : Gal((hilbertElementaryLayerInMaximal K p) / K) ↦ z ^ p)
        (eAut.apply_symm_apply τ).symm
    _ = eAut (σ ^ p) := (map_pow eAut σ p).symm
    _ = eAut 1 :=
      congrArg eAut (hilbertElementaryGalois_pow_eq_one K p σ)
    _ = 1 := map_one eAut

/-- The Galois rank of the copy is the ordinary `p`-class rank. -/
theorem finrank_hilbertElementaryLayerInMaximal_galois_eq_pClassRank
    (p : ℕ) [Fact p.Prime] :
    letI : Module (ZMod p)
        (Additive Gal((hilbertElementaryLayerInMaximal K p) / K)) :=
      AddCommGroup.zmodModule (fun x => by
        change (Additive.toMul x) ^ p = 1
        exact hilbertElementaryLayerInMaximal_galois_pow_eq_one
          K p (Additive.toMul x))
    Module.finrank (ZMod p)
        (Additive Gal((hilbertElementaryLayerInMaximal K p) / K)) =
      pClassRank K p := by
  let : Module (ZMod p)
      (Additive Gal((hilbertElementaryLayer K p) / K)) :=
    AddCommGroup.zmodModule (fun x => by
      change (Additive.toMul x) ^ p = 1
      exact hilbertElementaryGalois_pow_eq_one K p (Additive.toMul x))
  let : Module (ZMod p)
      (Additive Gal((hilbertElementaryLayerInMaximal K p) / K)) :=
    AddCommGroup.zmodModule (fun x => by
      change (Additive.toMul x) ^ p = 1
      exact hilbertElementaryLayerInMaximal_galois_pow_eq_one
        K p (Additive.toMul x))
  let e : Additive Gal((hilbertElementaryLayer K p) / K) ≃+
      Additive Gal((hilbertElementaryLayerInMaximal K p) / K) :=
    (AlgEquiv.autCongr
      (hilbertElementaryLayerEquivInMaximal K p)).toAdditive
  let eLin : Additive Gal((hilbertElementaryLayer K p) / K) ≃ₗ[ZMod p]
      Additive Gal((hilbertElementaryLayerInMaximal K p) / K) :=
    LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap p) e.bijective
  calc
    Module.finrank (ZMod p)
        (Additive Gal((hilbertElementaryLayerInMaximal K p) / K)) =
        Module.finrank (ZMod p)
          (Additive Gal((hilbertElementaryLayer K p) / K)) :=
      eLin.symm.finrank_eq
    _ = pClassRank K p :=
      finrank_hilbertElementaryGalois_eq_pClassRank K p

end ClassFieldTower.Martinet

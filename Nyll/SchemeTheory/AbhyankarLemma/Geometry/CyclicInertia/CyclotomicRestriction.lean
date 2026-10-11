/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.Geometry.CyclicInertia.CyclotomicInversion

/-!
# Restricting cyclotomic inversion to normal extensions

An automorphism of a separable closure which inverts roots of unity restricts
to every normal separable subextension.  The subextension is first embedded
in the separable closure and the restricted automorphism is then transported
back across that embedding.
-/

noncomputable section


universe u v w x

namespace EtaleFundamentalGroups

private theorem
    exists_intermediateFieldAlgEquiv_inverting_torsionUnits_of_ratEquiv
    {k : Type u} {F : Type v} {Omega : Type w}
    [Field k] [Field F] [Field Omega]
    [Algebra k F] [Algebra F Omega] [Algebra k Omega]
    [IsScalarTower k F Omega] [IsSepClosure F Omega]
    (e : k ≃+* ℚ)
    (hdisjoint : (separableClosure k Omega).LinearDisjoint F)
    (M : IntermediateField F Omega) [Normal F M] :
    ∃ tau : M ≃ₐ[F] M,
      ∀ z : Mˣ, IsOfFinOrder z →
        Units.mapEquiv tau.toMulEquiv z = z⁻¹ := by
  let : CharZero k := e.toRingHom.charZero
  let : PerfectField k := PerfectField.ofCharZero
  obtain ⟨tauOmega, htauOmega⟩ :=
    exists_algEquiv_inverting_torsionUnits_of_separableClosure_linearDisjoint_of_ratEquiv
      (F := F) (Omega := Omega) e hdisjoint
  let tau : M ≃ₐ[F] M := tauOmega.restrictNormal M
  refine ⟨tau, ?_⟩
  intro z hz
  let mapUnits : Mˣ →* Omegaˣ := Units.map (algebraMap M Omega)
  let zOmega : Omegaˣ := mapUnits z
  have hzOmega : IsOfFinOrder zOmega := mapUnits.isOfFinOrder hz
  have hOmega := congrArg Units.val (htauOmega zOmega hzOmega)
  apply Units.ext
  apply (algebraMap M Omega).injective
  rw [Units.coe_mapEquiv, Units.val_inv_eq_inv_val]
  change algebraMap M Omega (tau (z : M)) =
    algebraMap M Omega ((z : M)⁻¹)
  rw [show algebraMap M Omega (tau (z : M)) =
      tauOmega (algebraMap M Omega (z : M)) by
    exact AlgEquiv.restrictNormal_commutes tauOmega M (z : M)]
  simpa [zOmega, mapUnits] using hOmega

/-- Let `Omega` be a separable closure of `F`, with the separable closure of
the rational base linearly disjoint from `F`.  Every normal separable
extension `E / F` embedded in `Omega` inherits an automorphism which inverts
all finite-order units.

The embedding is constructed canonically from separable closedness; `E`
itself is not required to be a separable closure. -/
theorem
    exists_normalAlgEquiv_inverting_torsionUnits_of_separableClosure_linearDisjoint_of_ratEquiv
    {k : Type u} {F : Type v} {E : Type x} {Omega : Type w}
    [Field k] [Field F] [Field E] [Field Omega]
    [Algebra k F] [Algebra F E] [Algebra F Omega] [Algebra k Omega]
    [IsScalarTower k F Omega] [IsSepClosure F Omega]
    [Normal F E] [Algebra.IsSeparable F E]
    (e : k ≃+* ℚ)
    (hdisjoint : (separableClosure k Omega).LinearDisjoint F) :
    ∃ tau : E ≃ₐ[F] E,
      ∀ z : Eˣ, IsOfFinOrder z →
        Units.mapEquiv tau.toMulEquiv z = z⁻¹ := by
  let : IsSepClosed Omega := IsSepClosure.sep_closed F
  let j : E →ₐ[F] Omega := IsSepClosed.lift
  let M : IntermediateField F Omega := j.fieldRange
  let eM : E ≃ₐ[F] M := AlgEquiv.ofInjective j j.injective
  let : Normal F M := Normal.of_algEquiv eM
  obtain ⟨tauM, htauM⟩ :=
    exists_intermediateFieldAlgEquiv_inverting_torsionUnits_of_ratEquiv
      e hdisjoint M
  let tau : E ≃ₐ[F] E := eM.symm.autCongr tauM
  refine ⟨tau, ?_⟩
  intro z hz
  let zM : Mˣ := Units.map eM.toMonoidHom z
  have hzM : IsOfFinOrder zM :=
    (Units.map eM.toMonoidHom).isOfFinOrder hz
  have hM := congrArg Units.val (htauM zM hzM)
  apply Units.ext
  apply eM.injective
  simpa [tau, zM, AlgEquiv.autCongr_apply] using hM

end EtaleFundamentalGroups

end

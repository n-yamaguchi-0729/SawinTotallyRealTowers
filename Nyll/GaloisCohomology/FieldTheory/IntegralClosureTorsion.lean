/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.GroupTheory.Torsion

/-!
# Torsion units and integral closure
-/

namespace FieldTheory

universe u v
variable (R : Type u) (K : Type v) [CommRing R] [Field K] [Algebra R K]

/-- Roots of unity are integral over any coefficient ring. -/
theorem isIntegral_torsionUnit (z : Kˣ) (hz : IsOfFinOrder z) :
    IsIntegral R (z : K) := by
  apply IsIntegral.of_pow hz.orderOf_pos
  have hp : (z : K) ^ orderOf z = 1 := congrArg Units.val (pow_orderOf_eq_one z)
  rw [hp]
  exact isIntegral_one

/-- Every torsion unit has a unique lift to a torsion unit in the integral closure. -/
noncomputable def torsionUnitsIntegralClosureEquiv :
    CommGroup.torsion Kˣ ≃* CommGroup.torsion (integralClosure R K)ˣ := by
  let g : (integralClosure R K)ˣ →* Kˣ :=
    Units.map (integralClosure R K).val.toMonoidHom
  let f : CommGroup.torsion (integralClosure R K)ˣ →* CommGroup.torsion Kˣ :=
    { toFun := fun z => ⟨g z.1, isOfFinOrder_iff_pow_eq_one.mpr
        ⟨orderOf z.1, z.property.orderOf_pos, by rw [← map_pow, pow_orderOf_eq_one, map_one]⟩⟩
      map_one' := Subtype.ext (map_one g)
      map_mul' := fun x y => Subtype.ext (map_mul g x.1 y.1) }
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Units.ext
    apply Subtype.ext
    exact congrArg (fun z : CommGroup.torsion Kˣ => (z.1 : K)) h
  have hs : Function.Surjective f := by
    intro z
    let u : (integralClosure R K)ˣ :=
      { val := ⟨(z.1 : K), isIntegral_torsionUnit R K z.1 z.property⟩
        inv := ⟨(↑z.1⁻¹ : K), isIntegral_torsionUnit R K z.1⁻¹ z.property.inv⟩
        val_inv := Subtype.ext (Units.val_inv z.1)
        inv_val := Subtype.ext (Units.inv_val z.1) }
    have hu : IsOfFinOrder u := by
      refine isOfFinOrder_iff_pow_eq_one.mpr ⟨orderOf z.1, z.property.orderOf_pos, ?_⟩
      apply Units.ext
      apply Subtype.ext
      exact congrArg Units.val (pow_orderOf_eq_one z.1)
    exact ⟨⟨u, hu⟩, rfl⟩
  exact (MulEquiv.ofBijective f ⟨hf, hs⟩).symm

end FieldTheory

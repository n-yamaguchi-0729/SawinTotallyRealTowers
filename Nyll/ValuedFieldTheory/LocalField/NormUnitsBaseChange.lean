/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ValuedFieldTheory.LocalField.NormUnits

/-!
# Field norm under changes of base and extension

Compatible field equivalences transport the norm on units and its image.
-/

@[expose] public section

noncomputable section

namespace LocalFieldTheory

universe u v w x

variable {F : Type u} {M : Type v} {F' : Type w} {M' : Type x}
  [Field F] [Field M] [Field F'] [Field M']
  [Algebra F M] [Algebra F' M']

/-- The field-norm homomorphisms commute with compatible field equivalences. -/
theorem normUnits_map_ringEquiv
    (eF : F ≃+* F') (eM : M ≃+* M')
    (he : (algebraMap F' M').comp eF.toRingHom =
      eM.toRingHom.comp (algebraMap F M))
    (y : Mˣ) :
    (Units.mapEquiv eF.toMulEquiv) (normUnits F M y) =
      normUnits F' M' (Units.mapEquiv eM.toMulEquiv y) := by
  apply Units.ext
  change eF (Algebra.norm F (y : M)) =
    Algebra.norm F' (eM (y : M))
  rw [Algebra.norm_eq_of_equiv_equiv eF eM he]
  exact eF.apply_symm_apply _

/-- The image of a field-norm subgroup under a base-field equivalence is
exactly the norm subgroup of the transported extension. -/
theorem localNormSubgroup_map_ringEquiv
    (eF : F ≃+* F') (eM : M ≃+* M')
    (he : (algebraMap F' M').comp eF.toRingHom =
      eM.toRingHom.comp (algebraMap F M)) :
    (localNormSubgroup F M).map
        (Units.mapEquiv eF.toMulEquiv).toMonoidHom =
      localNormSubgroup F' M' := by
  ext z
  constructor
  · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
    exact ⟨Units.mapEquiv eM.toMulEquiv x,
      (normUnits_map_ringEquiv eF eM he x).symm⟩
  · rintro ⟨x, rfl⟩
    let y := (Units.mapEquiv eM.toMulEquiv).symm x
    refine ⟨normUnits F M y, ⟨y, rfl⟩, ?_⟩
    change (Units.mapEquiv eF.toMulEquiv) (normUnits F M y) =
      normUnits F' M' x
    simpa only [y, MulEquiv.apply_symm_apply] using
      normUnits_map_ringEquiv eF eM he y

end LocalFieldTheory

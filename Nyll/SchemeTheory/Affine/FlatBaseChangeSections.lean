/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Flat base change on affine sections

The actual maps on sections form a pushout for a qcqs source and a flat
base change. The tensor comparison retains those maps as its scalar owners.
The four section rings retain their canonical bundled ring structures. The
three displayed algebra structures are the only explicit scalar owners; the
tensor product uses its canonical structure. No target is redeclared.
The construction is extracted from Andrew Yang's normalization base-change proof:
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/AlgebraicGeometry/Normalization.lean
-/


noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

variable {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
variable [QuasiCompact f] [QuasiSeparated f] [Flat g]
variable {U : S.Opens} {V : T.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
variable (hVU : V ≤ g ⁻¹ᵁ U)

/-- Flat qcqs base change identifies the actual sections with the tensor product. -/
def affinePullbackSectionsTensorEquiv :
    let : Algebra Γ(S, U) Γ(T, V) := (g.appLE U V hVU).hom.toAlgebra
    let : Algebra Γ(S, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
    let : Algebra Γ(T, V) Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V) :=
      ((pullback.snd f g).app V).hom.toAlgebra
    Γ(T, V) ⊗[Γ(S, U)] Γ(X, f ⁻¹ᵁ U) ≃ₐ[Γ(T, V)]
      Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V) := by
  intro hRT hRX hTP
  have hOpen : pullback.snd f g ⁻¹ᵁ V =
      pullback.fst f g ⁻¹ᵁ (f ⁻¹ᵁ U) ⊓ pullback.snd f g ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage,
      ← Scheme.Hom.preimage_inf, inf_eq_right.mpr hVU]
  have hSourceSection := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (IsPullback.of_hasPullback f g) hVU le_rfl (UY := pullback.snd f g ⁻¹ᵁ V)
    hOpen
    hU hV (f.isCompact_preimage hU.isCompact) (f.isQuasiSeparated_preimage hU.isQuasiSeparated)
  let e₀ := (CommRingCat.isPushout_tensorProduct Γ(S, U) Γ(T, V) Γ(X, f ⁻¹ᵁ U)).flip.isoPushout ≪≫
    (pushout.congrHom f.app_eq_appLE rfl ≪≫ asIso
      (pushoutSection (IsPullback.of_hasPullback f g) hVU le_rfl
        (UY := pullback.snd f g ⁻¹ᵁ V) hOpen))
  let e : Γ(T, V) ⊗[Γ(S, U)] Γ(X, f ⁻¹ᵁ U) ≃ₐ[Γ(T, V)]
      Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V) :=
    { toRingEquiv := e₀.commRingCatIsoToRingEquiv
      commutes' r := by
        change (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ e₀.hom) r =
          (pullback.snd f g).app V r
        congr 2
        simp only [e₀, Iso.trans_hom, asIso_hom,
          IsPushout.inr_isoPushout_hom_assoc, pushout.congrHom_hom, pushout.inr_desc_assoc,
          Category.id_comp, pushout.inr_desc, Scheme.Hom.app_eq_appLE] }
  exact e

/-- The tensor comparison agrees with restriction from the source on its right
factor; this fixes the actual map, as opposed to only its isomorphism class. -/
theorem affinePullbackSectionsTensorEquiv_one_tmul :
    let : Algebra Γ(S, U) Γ(T, V) := (g.appLE U V hVU).hom.toAlgebra
    let : Algebra Γ(S, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
    let : Algebra Γ(T, V) Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V) :=
      ((pullback.snd f g).app V).hom.toAlgebra
    ∀ x : Γ(X, f ⁻¹ᵁ U),
      affinePullbackSectionsTensorEquiv f g hU hV hVU (1 ⊗ₜ[Γ(S, U)] x) =
        (pullback.fst f g).appLE _ _ (by
          rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage]
          exact Scheme.Hom.preimage_mono _ hVU) x := by
  intro hRT hRX hTP x
  have hOpen : pullback.snd f g ⁻¹ᵁ V =
      pullback.fst f g ⁻¹ᵁ (f ⁻¹ᵁ U) ⊓ pullback.snd f g ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage,
      ← Scheme.Hom.preimage_inf, inf_eq_right.mpr hVU]
  have hSourceSection := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (IsPullback.of_hasPullback f g) hVU le_rfl (UY := pullback.snd f g ⁻¹ᵁ V)
    hOpen
    hU hV (f.isCompact_preimage hU.isCompact) (f.isQuasiSeparated_preimage hU.isQuasiSeparated)
  change (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫
    ((CommRingCat.isPushout_tensorProduct Γ(S, U) Γ(T, V) Γ(X, f ⁻¹ᵁ U)).flip.isoPushout ≪≫
      (pushout.congrHom f.app_eq_appLE rfl ≪≫ asIso _)).hom) x = _
  congr 2
  simp only [Iso.trans_hom, asIso_hom,
    IsPushout.inl_isoPushout_hom_assoc, pushout.congrHom_hom,
    pushout.inl_desc_assoc, Category.id_comp, pushout.inl_desc]

end AlgebraicGeometry

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RingInertiaCharacter
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Conjugation of the DVR inertia character

Proves normality of maximal-ideal inertia and computes the conjugation of uniformizer-ratio
units. The residue character intertwines group conjugation with the induced residue-field
action.
-/

noncomputable section

namespace RamificationTheory.HilbertRamification.DiscreteValuationRing

open IsLocalRing
open scoped Pointwise

universe u v

/-- Ring automorphisms preserve the unique maximal ideal, so its actual
inertia subgroup is normal in the full acting group. -/
theorem maximalIdeal_inertia_normal
    (R : Type u) [CommRing R] [IsLocalRing R]
    (G : Type v) [Group G] [MulSemiringAction G R] :
    ((maximalIdeal R).inertia G).Normal := by
  apply Subgroup.normal_iff_map_conj_eq.mpr
  intro g
  have : IsLocalHom (MulSemiringAction.toRingAut G R g).symm.toRingHom :=
    isLocalHom_toRingHom (MulSemiringAction.toRingAut G R g).symm
  have hmax : (maximalIdeal R).comap
      (MulSemiringAction.toRingAut G R g).symm.toRingHom = maximalIdeal R :=
    IsLocalRing.maximalIdeal_comap (MulSemiringAction.toRingAut G R g).symm.toRingHom
  have hstable : g • maximalIdeal R = maximalIdeal R :=
    (Ideal.pointwise_smul_eq_comap (a := g) (maximalIdeal R)).trans hmax
  exact (Ideal.inertia_smul g (maximalIdeal R)).symm.trans
    (congrArg (fun J : Ideal R => J.inertia G) hstable)

attribute [local instance] maximalIdeal_inertia_normal

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (G : Type v) [Group G] [MulSemiringAction G R]

/-- Conjugation carries the actual ratio unit at a uniformizer to the
ratio unit at its image. This is an identity in the original DVR. -/
theorem uniformizerRatioUnit_conj
    (π : R) (hπ : Irreducible π) (g s : G) :
    uniformizerRatioUnit R G (g • π)
        (hπ.map (MulDistribMulAction.toMulEquiv R g)) (g * s * g⁻¹) =
      (Units.map (MulSemiringAction.toRingHom G R g).toMonoidHom).toFun
        (uniformizerRatioUnit R G π hπ s) := by
  have hgπ : Irreducible (g • π) :=
    hπ.map (MulDistribMulAction.toMulEquiv R g)
  apply Units.ext
  apply mul_left_cancel₀ hgπ.ne_zero
  change (g • π) *
      (uniformizerRatioUnit R G (g • π) hgπ (g * s * g⁻¹)).val =
    (g • π) * (g • (uniformizerRatioUnit R G π hπ s).val)
  calc
    (g • π) * (uniformizerRatioUnit R G (g • π) hgπ (g * s * g⁻¹)).val =
        (g * s * g⁻¹) • (g • π) :=
      uniformizerRatioUnit_spec R G (g • π) hgπ (g * s * g⁻¹)
    _ = g • (s • π) := by
      simp only [mul_smul, inv_smul_smul]
    _ = g • (π * (uniformizerRatioUnit R G π hπ s).val) :=
      congrArg (fun x : R => g • x) (uniformizerRatioUnit_spec R G π hπ s).symm
    _ = (g • π) * (g • (uniformizerRatioUnit R G π hπ s).val) :=
      smul_mul' g π (uniformizerRatioUnit R G π hπ s).val

/-- The same uniformizer-independent inertia character intertwines actual
group conjugation with the standard action on residue-field units. -/
theorem inertiaResidueCharacter_conj
    (g : G) (σ : (maximalIdeal R).inertia G) :
    (inertiaResidueCharacter R G).toFun
        (((MulAut.conjNormal (H := (maximalIdeal R).inertia G)).toFun g).toFun σ) =
      (Units.map
        (MulSemiringAction.toRingHom G (ResidueField R) g).toMonoidHom).toFun
        ((inertiaResidueCharacter R G).toFun σ) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hgπ : Irreducible (g • π) :=
    hπ.map (MulDistribMulAction.toMulEquiv R g)
  let τ : (maximalIdeal R).inertia G :=
    ((MulAut.conjNormal (H := (maximalIdeal R).inertia G)).toFun g).toFun σ
  have hleft : ((inertiaResidueCharacter R G).toFun τ).val =
      residue R (uniformizerRatioUnit R G (g • π) hgπ (g * σ.val * g⁻¹)).val :=
    congrArg
      (fun f : (maximalIdeal R).inertia G →* (ResidueField R)ˣ => (f.toFun τ).val)
      (inertiaResidueCharacter_eq_uniformizer R G (g • π) hgπ)
  have hright : ((inertiaResidueCharacter R G).toFun σ).val =
      residue R (uniformizerRatioUnit R G π hπ σ.val).val :=
    congrArg
      (fun f : (maximalIdeal R).inertia G →* (ResidueField R)ˣ => (f.toFun σ).val)
      (inertiaResidueCharacter_eq_uniformizer R G π hπ)
  have hratio : uniformizerRatioUnit R G (g • π) hgπ (g * σ.val * g⁻¹) =
      (Units.map (MulSemiringAction.toRingHom G R g).toMonoidHom).toFun
        (uniformizerRatioUnit R G π hπ σ.val) :=
    uniformizerRatioUnit_conj R G π hπ g σ.val
  apply Units.ext
  change ((inertiaResidueCharacter R G).toFun τ).val =
    g • ((inertiaResidueCharacter R G).toFun σ).val
  rw [hleft, hright]
  exact (congrArg (fun a : Rˣ => residue R a.val)
    hratio).trans
      (ResidueField.residue_smul G g (uniformizerRatioUnit R G π hπ σ.val).val)

end RamificationTheory.HilbertRamification.DiscreteValuationRing

end

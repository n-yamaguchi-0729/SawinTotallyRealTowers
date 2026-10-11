/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_GeometricallyIntegral_of_isPullback_of_geometricallyIntegral.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Descent of geometric integrality across field base change

Geometric integrality is recovered from a pullback over a field extension. The argument
combines faithful flat descent of reducedness with the geometric irreducibility
comparison.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Curves.Proofs
namespace GeometricallyIntegral_of_isPullback_of_geometricallyIntegral

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open scoped TensorProduct

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry

scoped instance : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme) IsIntegral :=
  ⟨fun {X Y} e hX => by
    have := hX
    have : Nonempty Y := ⟨e.hom.base (Classical.arbitrary X)⟩
    exact isIntegral_of_isOpenImmersion e.inv⟩

private theorem surjective_specMap_of_fields {K Ω : Type u} [Field K] [Field Ω] (φ : K →+* Ω) :
    Surjective (Spec.map (CommRingCat.ofHom φ)) :=
  ⟨fun _ => ⟨default, Subsingleton.elim _ _⟩⟩

private theorem flat_specMap_of_fields {K Ω : Type u} [Field K] [Field Ω] (φ : K →+* Ω) :
    Flat (Spec.map (CommRingCat.ofHom φ)) := by
  rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom]
  let := φ.toAlgebra
  exact (RingHom.flat_algebraMap_iff (R := K) (S := Ω)).mpr inferInstance

private theorem isReduced_of_flat_of_surjective {X Y : Scheme.{u}}
    (π : X ⟶ Y) [Flat π] [Surjective π]
    [IsReduced X] : IsReduced Y := by
  have hst : ∀ y : Y, _root_.IsReduced (Y.presheaf.stalk y) := by
    intro y
    obtain ⟨x, rfl⟩ := π.surjective y
    let ψ := (π.stalkMap x).hom
    let := ψ.toAlgebra
    have : Module.Flat (Y.presheaf.stalk (π.base x)) (X.presheaf.stalk x) := Flat.stalkMap π x
    have : IsLocalHom (algebraMap (Y.presheaf.stalk (π.base x)) (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom ψ)
    have : Module.FaithfullyFlat (Y.presheaf.stalk (π.base x)) (X.presheaf.stalk x) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact isReduced_of_injective (algebraMap (Y.presheaf.stalk (π.base x)) (X.presheaf.stalk x))
      (FaithfulSMul.algebraMap_injective _ _)
  exact isReduced_of_isReduced_stalk Y

end AlgebraicGeometry

open _root_.AlgebraicGeometry in
open GeometricallyIntegral_of_isPullback_of_geometricallyIntegral.AlgebraicGeometry in
theorem _root_.AlgebraicGeometry.GeometricallyIntegral.of_isPullback_of_geometricallyIntegral
    {κ k : Type u} [Field κ] [Field k] [Algebra κ k]
    {C C' : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of κ))
    (c' : C' ⟶ Spec (CommRingCat.of k)) (g : C' ⟶ C)
    (h : IsPullback g c' c (Spec.map (CommRingCat.ofHom (algebraMap κ k))))
    [GeometricallyIntegral c'] :
    GeometricallyIntegral c := by
  have hc' : geometrically IsIntegral c' := by
    have := ‹GeometricallyIntegral c'›; rwa [GeometricallyIntegral.eq_geometrically] at this
  rw [GeometricallyIntegral.eq_geometrically,
    geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K' _ _
  have : Nontrivial (K' ⊗[κ] k) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left
      (R := κ) K' k (algebraMap κ k).injective
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal (K' ⊗[κ] k)
  let Ω : Type u := (K' ⊗[κ] k) ⧸ 𝔪
  let : Field Ω := Ideal.Quotient.field 𝔪
  let φK : K' →+* Ω := algebraMap K' Ω
  let φk : k →+* Ω := (Ideal.Quotient.mk 𝔪).comp
    (Algebra.TensorProduct.includeRight (R := κ) (A := K') (B := k)).toRingHom
  have hφK : φK.comp (algebraMap κ K') = algebraMap κ Ω := (IsScalarTower.algebraMap_eq κ K' Ω).symm
  have hφk : φk.comp (algebraMap κ k) = algebraMap κ Ω := by
    ext a
    simp only [φk, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, AlgHom.commutes]
    rfl
  let sK : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of κ) :=
    Spec.map (CommRingCat.ofHom (algebraMap κ K'))
  let sk : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of κ) :=
    Spec.map (CommRingCat.ofHom (algebraMap κ k))
  let sΩK : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of K') := Spec.map (CommRingCat.ofHom φK)
  let sΩk : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom φk)
  have hcomm : sΩk ≫ sk = sΩK ≫ sK := by
    simp only [sΩk, sk, sΩK, sK, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφK, hφk]
  have hint : IsIntegral (pullback c' sΩk) := pullback_of_geometrically hc' Ω sΩk
  let π : pullback c' sΩk ⟶ pullback c sK :=
    pullback.lift (pullback.fst c' sΩk ≫ g) (pullback.snd c' sΩk ≫ sΩK) (by
      rw [Category.assoc, h.w, ← Category.assoc, pullback.condition,
        Category.assoc, Category.assoc, hcomm])
  have hbig : IsPullback (pullback.fst c' sΩk ≫ g) (pullback.snd c' sΩk) c (sΩK ≫ sK) := by
    rw [← hcomm]; exact (IsPullback.of_hasPullback c' sΩk).paste_horiz h
  have hsq : IsPullback π (pullback.snd c' sΩk) (pullback.snd c sK) sΩK := by
    refine IsPullback.of_right (h₁₂ := pullback.fst c sK) ?_
      (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback c sK)
    simpa only [π, pullback.lift_fst] using hbig
  have : Surjective π :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      hsq.flip (surjective_specMap_of_fields φK)
  have : Flat π :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip (flat_specMap_of_fields φK)
  have : IrreducibleSpace ↥(pullback c sK) := π.surjective.irreducibleSpace π.continuous
  have : IsReduced (pullback c sK) := isReduced_of_flat_of_surjective π
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end GeometricallyIntegral_of_isPullback_of_geometricallyIntegral
end AlgebraicCurves.Geometry.Curves.Proofs
end ProofImplementation

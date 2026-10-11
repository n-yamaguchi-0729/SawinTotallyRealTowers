/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Etale.UniversalHomeomorphismSections
public import Nyll.SchemeTheory.Morphisms.UnramifiedHomExt
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Algebra maps across a universal homeomorphism

For an étale algebra `A` and an arbitrary algebra `B`, every map from `A`
to the scalar extension of `B` descends uniquely through an affine universal
homeomorphism. The source spectrum for this lifting problem is arbitrary;
in particular, the assertion applies to the tensor algebras in a coaction.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Algebra

/-- Algebra maps from an étale algebra to an arbitrary algebra are unchanged
by extending the target through a universal homeomorphism. -/
theorem Etale.includeRight_comp_bijective_of_universalHomeomorphism
    (R S A B : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra R B] [Etale R A]
    [IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    [UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    [Surjective (Spec.map (CommRingCat.ofHom (algebraMap R S)))] :
    Function.Bijective (fun φ : A →ₐ[R] B ↦
      (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B).comp φ) := by
  let f : Spec (.of S) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R S))
  let g : Spec (.of B) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R B))
  let p : Spec (.of A) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R A))
  let η : B →ₐ[R] S ⊗[R] B := Algebra.TensorProduct.includeRight
  let k : Spec (.of (S ⊗[R] B)) ⟶ Spec (.of B) :=
    Spec.map (CommRingCat.ofHom η.toRingHom)
  have hk : k = (pullbackSpecIso R S B).inv ≫ pullback.snd f g :=
    (pullbackSpecIso_inv_snd R S B).symm
  let : UniversallyInjective (pullback.snd f g) :=
    UniversallyInjective.isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f g) inferInstance
  let : IsIntegralHom k := by rw [hk]; infer_instance
  let : UniversallyInjective k := by
    rw [hk]
    exact MorphismProperty.comp_mem
      (@UniversallyInjective : MorphismProperty Scheme.{u})
      (pullbackSpecIso R S B).inv (pullback.snd f g) inferInstance inferInstance
  let : Surjective k := by rw [hk]; infer_instance
  let : AlgebraicGeometry.Etale p :=
    (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  have spec_w (φ : A →ₐ[R] B) :
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ p = g := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact φ.commutes r
  constructor
  · intro φ ψ hφψ
    let a : Over.mk g ⟶ Over.mk p :=
      Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (spec_w φ)
    let b : Over.mk g ⟶ Over.mk p :=
      Over.homMk (Spec.map (CommRingCat.ofHom ψ.toRingHom)) (spec_w ψ)
    let j : Over.mk (k ≫ g) ⟶ Over.mk g := Over.homMk k rfl
    have hab : j ≫ a = j ≫ b := by
      apply Over.OverMorphism.ext
      change k ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) =
        k ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom)
      change Spec.map (CommRingCat.ofHom η.toRingHom) ≫
          Spec.map (CommRingCat.ofHom φ.toRingHom) =
        Spec.map (CommRingCat.ofHom η.toRingHom) ≫
          Spec.map (CommRingCat.ofHom ψ.toRingHom)
      rw [← Spec.map_comp, ← Spec.map_comp]
      exact congrArg (fun τ : A →ₐ[R] S ⊗[R] B ↦
        Spec.map (CommRingCat.ofHom τ.toRingHom)) hφψ
    let : AlgebraicGeometry.FormallyUnramified (Over.mk p).hom :=
      inferInstanceAs (AlgebraicGeometry.FormallyUnramified p)
    let : LocallyOfFiniteType (Over.mk p).hom := inferInstanceAs (LocallyOfFiniteType p)
    let : IsSeparated (Over.mk p).hom := inferInstanceAs (IsSeparated p)
    let : IsDominant j.left := inferInstanceAs (IsDominant k)
    have h := AlgebraicGeometry.Over.hom_ext_of_isDominant_of_unramified a b j hab
    have hs : Spec.map (CommRingCat.ofHom φ.toRingHom) =
        Spec.map (CommRingCat.ofHom ψ.toRingHom) :=
      congrArg (fun τ : Over.mk g ⟶ Over.mk p ↦ τ.left) h
    have hr := Spec.map_injective hs
    apply AlgHom.ext
    intro x
    exact congrArg (fun τ : CommRingCat.of A ⟶ CommRingCat.of B ↦ τ.hom x) hr
  · intro σ
    let w : Spec (.of (S ⊗[R] B)) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom σ.toRingHom)
    have hw : w ≫ p = k ≫ g := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      apply congrArg Spec.map
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro r
      exact (σ.commutes r).trans (η.commutes r).symm
    obtain ⟨t, htp, hkt⟩ :=
      AlgebraicGeometry.Etale.exists_lift_of_integral_universallyInjective_surjective
        k p g w hw
    obtain ⟨φ, hφ⟩ := Spec.map_surjective t
    have hφR : CommRingCat.ofHom (algebraMap R A) ≫ φ =
        CommRingCat.ofHom (algebraMap R B) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hφ]
      exact htp
    let φA : A →ₐ[R] B := {
      __ := φ.hom
      commutes' r :=
        congrArg (fun τ : CommRingCat.of R ⟶ CommRingCat.of B ↦ τ.hom r) hφR
    }
    refine ⟨φA, ?_⟩
    have hφη : φ ≫ CommRingCat.ofHom η.toRingHom =
        CommRingCat.ofHom σ.toRingHom := by
      apply Spec.map_injective
      rw [Spec.map_comp, hφ]
      exact hkt
    apply AlgHom.ext
    intro x
    exact congrArg
      (fun τ : CommRingCat.of A ⟶ CommRingCat.of (S ⊗[R] B) ↦ τ.hom x) hφη

end Algebra

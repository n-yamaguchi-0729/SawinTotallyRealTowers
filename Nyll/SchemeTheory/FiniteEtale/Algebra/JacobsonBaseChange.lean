/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FiniteEtale.Algebra.JacobsonConservativity
public import Nyll.SchemeTheory.FiniteEtale.Algebra.JacobsonRigidity
public import Nyll.SchemeTheory.RingTheory.JacobsonIntegral
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.RingTheory.Etale.Finite
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Finite étale reduction modulo a Jacobson ideal

An integral algebra carries an ideal in the base Jacobson radical into its
own Jacobson radical. Unramified rigidity then makes reduction injective on
algebra maps. Transporting through the quotient/tensor comparison proves
faithfulness of the canonical finite étale base-change functor. Nakayama
and the idempotent-kernel argument also make this functor reflect isomorphisms. In
particular, the Jacobson condition is supplied by `HenselianRing.jac` for
every henselian pair.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace Algebra.FormallyUnramified

/-- Scalar extension to a Jacobson quotient detects maps from unramified
essentially finite type algebras into integral algebras. -/
theorem baseChange_injective_of_le_jacobson
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [FormallyUnramified R A] [EssFiniteType R A] [Algebra.IsIntegral R B]
    (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥) :
    Function.Injective (fun f : A →ₐ[R] B ↦
      Algebra.TensorProduct.map (.id (R ⧸ I) (R ⧸ I)) f) := by
  intro f g hfg
  apply comp_injective_of_le_jacobson (I.map (algebraMap R B))
    (Ideal.map_le_jacobson_bot_of_isIntegral hI)
  apply AlgHom.ext
  intro a
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I
  apply e.injective
  change (1 : R ⧸ I) ⊗ₜ[R] f a = (1 : R ⧸ I) ⊗ₜ[R] g a
  simpa only [Algebra.TensorProduct.map_tmul, map_one] using
    AlgHom.congr_fun hfg ((1 : R ⧸ I) ⊗ₜ[R] a)

end Algebra.FormallyUnramified

namespace CommAlgCat.FiniteEtale

/-- Finite étale base change to a quotient by a Jacobson ideal is faithful. -/
theorem baseChange_faithful_of_le_jacobson
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥) :
    (baseChange R (R ⧸ I) : CommAlgCat.FiniteEtale.{v} R ⥤
      CommAlgCat.FiniteEtale.{max u v} (R ⧸ I)).Faithful where
  map_injective {A B} f g hfg := by
    apply ObjectProperty.hom_ext
    apply CommAlgCat.Hom.ext
    apply Algebra.FormallyUnramified.baseChange_injective_of_le_jacobson I hI
    exact congrArg (fun k : (baseChange R (R ⧸ I)).obj A ⟶
      (baseChange R (R ⧸ I)).obj B ↦ k.hom.hom) hfg

/-- Finite étale base change to a quotient by a Jacobson ideal reflects
isomorphisms. -/
theorem baseChange_reflectsIsomorphisms_of_le_jacobson
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥) :
    (baseChange R (R ⧸ I) : CommAlgCat.FiniteEtale.{v} R ⥤
      CommAlgCat.FiniteEtale.{max u v} (R ⧸ I)).ReflectsIsomorphisms where
  reflects {A B} f _ := by
    apply (ObjectProperty.isIso_hom_iff f).mp
    have hbij : Function.Bijective f.hom := by
      apply Algebra.FiniteEtale.bijective_of_baseChange_quotient I hI f.hom.hom
      exact ConcreteCategory.bijective_of_isIso ((baseChange R (R ⧸ I)).map f).hom
    let e : A.obj ≃ₐ[R] B.obj := AlgEquiv.ofBijective f.hom.hom hbij
    let baseIso : A.obj ≅ B.obj := CommAlgCat.isoMk e
    let eIso : A ≅ B := ObjectProperty.isoMk _ baseIso
    have he : eIso.hom = f := by
      apply ObjectProperty.hom_ext
      apply CommAlgCat.Hom.ext
      rfl
    rw [← he]
    infer_instance

end CommAlgCat.FiniteEtale

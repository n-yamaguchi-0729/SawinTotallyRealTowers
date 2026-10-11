/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FiniteEtale.Algebra.FinitelyGeneratedModel
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Finite étale objects descend through filtered ring colimits

First construct a finite étale model over a finitely generated coefficient
ring. This ring is finitely presented over the initial ring, so its actual
map to the colimit factors through a stage. Scalar extension of the model
to that stage supplies both finiteness and étaleness there.

This is the affine object supplier for Stacks Project, tag 0BTV. No
injectivity or integrality assumption is imposed on the diagram maps.
-/

@[expose] public section

open CategoryTheory Limits
open scoped TensorProduct

universe u v

namespace Algebra.FiniteEtale

/-- Every finite étale algebra over a filtered colimit of commutative rings
comes by scalar extension from a finite étale algebra at one actual stage. -/
theorem exists_filtered_colimit_stage_model
    {J : Type u} [Category.{u} J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (B : Type v) [CommRing B] [Algebra c.pt B]
    [Module.Finite c.pt B] [Algebra.Etale c.pt B] :
    ∃ i : J,
      let : Algebra (F.obj i) c.pt := (c.ι.app i).hom.toAlgebra
      ∃ (Bᵢ : Type u) (_ : CommRing Bᵢ) (_ : Algebra (F.obj i) Bᵢ),
        Module.Finite (F.obj i) Bᵢ ∧ Algebra.Etale (F.obj i) Bᵢ ∧
          Nonempty (B ≃ₐ[c.pt] c.pt ⊗[F.obj i] Bᵢ) := by
  let Z : CommRingCat.{u} := CommRingCat.of (ULift.{u} ℤ)
  let hZ : IsInitial Z := CommRingCat.isInitial
  let : Algebra Z c.pt := (hZ.to c.pt).hom.toAlgebra
  have : IsNoetherianRing Z := isNoetherianRing_of_ringEquiv ℤ
    (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).symm
  obtain ⟨T, B₀, hring, halgebra, hfg, hfinite, hetale, ⟨e⟩⟩ :=
    exists_fg_subalgebra_model Z c.pt B
  let : CommRing B₀ := hring
  let : Algebra T B₀ := halgebra
  have : Module.Finite T B₀ := hfinite
  have : Algebra.Etale T B₀ := hetale
  have hft : Algebra.FiniteType Z T := (Subalgebra.fg_iff_finiteType T).mp hfg
  have hfp : Algebra.FinitePresentation Z T :=
    Algebra.FinitePresentation.of_finiteType.mp hft
  let α : (Functor.const J).obj Z ⟶ F :=
    { app := fun i ↦ hZ.to (F.obj i)
      naturality := fun _ _ _ ↦ hZ.hom_ext _ _ }
  let f : Z ⟶ CommRingCat.of T := CommRingCat.ofHom (algebraMap Z T)
  have hf : f.hom.FinitePresentation := RingHom.finitePresentation_algebraMap.mpr hfp
  let g : CommRingCat.of T ⟶ c.pt := CommRingCat.ofHom T.val.toRingHom
  obtain ⟨i, gᵢ, _, hfactor⟩ :=
    RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
      (R := Z) (F := F) (α := α) (f := f) (c := c) (hc := hc) hf g
      (fun _ ↦ hZ.hom_ext _ _)
  refine ⟨i, ?_⟩
  let : Algebra (F.obj i) c.pt := (c.ι.app i).hom.toAlgebra
  let : Algebra T (F.obj i) := gᵢ.hom.toAlgebra
  have : IsScalarTower T (F.obj i) c.pt :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hfactor)
  let Bᵢ : Type u := F.obj i ⊗[T] B₀
  refine ⟨Bᵢ, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  exact ⟨e.trans (Algebra.TensorProduct.cancelBaseChange T (F.obj i) c.pt c.pt B₀).symm⟩

end Algebra.FiniteEtale

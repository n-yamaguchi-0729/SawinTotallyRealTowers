/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Isomorphism neighborhoods of finite étale morphisms

The rank-one locus of a finite flat finitely presented morphism is open,
and the restriction to it is an isomorphism. For an étale morphism, a
singleton fiber with unchanged residue field is an isomorphism: the
residue-field point is a surjective étale monomorphism onto that fiber.
Together these give an isomorphism neighborhood for finite étale morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Rank one at a point gives an actual open neighborhood on which a finite
flat finitely presented morphism is an isomorphism. -/
theorem Scheme.Hom.exists_isIso_restrict_of_finrank_eq_one
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    [Flat p] [IsFinite p] [LocallyOfFinitePresentation p]
    (y : Y) (hy : p.finrank y = 1) :
    ∃ U : Y.Opens, y ∈ U ∧ IsIso (p ∣_ U) := by
  let U : Y.Opens := ⟨{z | p.finrank z = 1}, p.isLocallyConstant_finrank.isOpen_fiber 1⟩
  refine ⟨U, hy, (Scheme.Hom.isIso_iff_finrank_eq (p ∣_ U)).mpr ?_⟩
  funext z
  calc
    (p ∣_ U).finrank z = p.finrank (U.ι z) :=
      Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_morphismRestrict p U).flip z
    _ = 1 := z.property

/-- A singleton étale fiber with unchanged residue field is an isomorphism
over the residue field of the base point. -/
theorem Etale.isIso_fiberToSpecResidueField_of_unique_preimage
    {X Y : Scheme.{u}} (p : X ⟶ Y) [Etale p] (x : X)
    (hx : ∀ x' : X, p x' = p x → x' = x) [IsIso (p.residueFieldMap x)] :
    IsIso (p.fiberToSpecResidueField (p x)) := by
  let q := p.fiberToSpecResidueField (p x)
  let s := p.asFiberHom x
  let : Etale q := by
    change Etale (pullback.snd p (Y.fromSpecResidueField (p x)))
    exact (Etale.etale_isStableUnderBaseChange).of_isPullback
      (IsPullback.of_hasPullback p (Y.fromSpecResidueField (p x))) ‹Etale p›
  have hs : s ≫ q = Spec.map (p.residueFieldMap x) :=
    p.asFiberHom_fiberToSpecResidueField x
  let : IsIso (s ≫ q) := hs.symm ▸ inferInstanceAs (IsIso (Spec.map (p.residueFieldMap x)))
  let : Etale s := Etale.of_comp s q
  let : Mono s := mono_of_mono_fac hs
  let : Surjective s := ⟨fun z ↦ by
    let c : Spec (X.residueField x) := IsLocalRing.closedPoint _
    refine ⟨c, ?_⟩
    change p.asFiberHom x c = z
    rw [p.asFiberHom_apply]
    apply (p.fiberι (p x)).isEmbedding.injective
    rw [p.fiberι_asFiber]
    exact (hx _ (p.fiberHomeo (p x) z).property).symm⟩
  let : IsOpenImmersion s := IsOpenImmersion.of_flat_of_mono s
  let : IsIso s := (isIso_iff_isOpenImmersion_and_surjective s).mpr
    ⟨inferInstance, inferInstance⟩
  exact (isIso_comp_left_iff s q).mp inferInstance

/-- A finite étale morphism with a singleton fiber and unchanged residue
field is an isomorphism on an open neighborhood of that fiber. -/
theorem Etale.exists_isIso_restrict_of_unique_preimage
    {X Y : Scheme.{u}} (p : X ⟶ Y) [IsFinite p] [Etale p] (x : X)
    (hx : ∀ x' : X, p x' = p x → x' = x) [IsIso (p.residueFieldMap x)] :
    ∃ U : Y.Opens, p x ∈ U ∧ IsIso (p ∣_ U) := by
  let : IsIso (p.fiberToSpecResidueField (p x)) :=
    Etale.isIso_fiberToSpecResidueField_of_unique_preimage p x hx
  apply p.exists_isIso_restrict_of_finrank_eq_one (p x)
  let c : Spec (Y.residueField (p x)) := IsLocalRing.closedPoint _
  have h := congrFun
    (Scheme.Hom.finrank_eq_one_of_isIso (p.fiberToSpecResidueField (p x))) c
  change (pullback.snd p (Y.fromSpecResidueField (p x))).finrank c = 1 at h
  rw [Scheme.Hom.finrank_pullback_snd] at h
  simpa only [Scheme.fromSpecResidueField_apply] using h

/-- A finite étale morphism whose fiber is a single point with purely
inseparable residue extension is an isomorphism on a neighborhood. -/
@[stacks 04DH]
theorem Etale.exists_isIso_restrict_of_unique_preimage_of_isPurelyInseparable
    {X Y : Scheme.{u}} (p : X ⟶ Y) [IsFinite p] [Etale p] (x : X)
    (hx : ∀ x' : X, p x' = p x → x' = x)
    (hκ : (p.residueFieldMap x).hom.IsPurelyInseparable) :
    ∃ U : Y.Opens, p x ∈ U ∧ IsIso (p ∣_ U) := by
  let : Algebra (Y.residueField (p x)) (X.residueField x) :=
    (p.residueFieldMap x).hom.toAlgebra
  let : IsPurelyInseparable (Y.residueField (p x)) (X.residueField x) := hκ
  let : IsIso (p.residueFieldMap x) :=
    (ConcreteCategory.isIso_iff_bijective (p.residueFieldMap x)).mpr
      (IsPurelyInseparable.bijective_algebraMap_of_isSeparable
        (Y.residueField (p x)) (X.residueField x))
  exact Etale.exists_isIso_restrict_of_unique_preimage p x hx

end AlgebraicGeometry

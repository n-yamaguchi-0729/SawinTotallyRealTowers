/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Nyll.SchemeTheory.Divisors.ArithmeticBoundary
import Nyll.SchemeTheory.Divisors.Basic
import Nyll.SchemeTheory.Divisors.EtaleRegularity
import Nyll.SchemeTheory.Pi1.FiniteEtale.Geometry

/-!
# Arithmetic boundaries under finite etale morphisms

This file develops the finite-etale stability of the arithmetic boundary
conditions.  It first records the topological fact that a closed
generalizing map sends every irreducible component onto an irreducible
component.  Applied to the finite-etale morphism between a pulled-back
boundary and the original boundary, this supplies points on each component
of the pullback without adding a component-dominance hypothesis.
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace TopologicalSpace

universe u v

/-- A generalizing map sends generic points of irreducible components to
generic points of irreducible components. -/
lemma mem_genericPoints_image_of_generalizingMap
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [T0Space X] [QuasiSober Y] {f : X → Y} (hf : GeneralizingMap f)
    (x : genericPoints X) : f x.1 ∈ genericPoints Y := by
  rw [genericPoints]
  refine ⟨isIrreducible_singleton.closure, ?_⟩
  intro T hT hsub
  let y : Y := hT.genericPoint
  have hy : IsGenericPoint y (closure T) :=
    hT.isGenericPoint_genericPoint_closure
  have hfy : f x.1 ∈ closure {y} := by
    rw [hy.def]
    apply subset_closure
    exact hsub (subset_closure (Set.mem_singleton _))
  obtain ⟨z, hzx, hzy⟩ := hf (specializes_iff_mem_closure.mpr hfy)
  have hclosure : closure {z} ⊆ closure {x.1} := by
    apply x.2.2 isIrreducible_singleton.closure
    exact closure_minimal
      (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hzx))
      isClosed_closure
  have hxz : x.1 ∈ closure {z} := specializes_iff_mem_closure.mp hzx
  have hzx' : z ∈ closure {x.1} :=
    hclosure (subset_closure (Set.mem_singleton _))
  have hz : z = x.1 := Inseparable.eq <|
    inseparable_iff_specializes_and.mpr
      ⟨hzx, specializes_iff_mem_closure.mpr hzx'⟩
  have hyfx : y = f x.1 := by
    rw [← hzy, hz]
  calc
    T ⊆ closure T := subset_closure
    _ = closure {y} := hy.def.symm
    _ = closure {f x.1} := by rw [hyfx]

/-- A closed generalizing map maps each irreducible component onto an
irreducible component.  The result is stated with the actual image equality,
which is the surjectivity needed to lift a chosen point componentwise. -/
lemma exists_irreducibleComponent_image_eq
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [T0Space X] [QuasiSober X] [QuasiSober Y]
    {f : X → Y} (hfc : Continuous f) (hfclosed : IsClosedMap f)
    (hfgeneral : GeneralizingMap f) (Z : Set X)
    (hZ : Z ∈ irreducibleComponents X) :
    ∃ W : Set Y, W ∈ irreducibleComponents Y ∧ f '' Z = W := by
  let η : genericPoints X := genericPoints.ofComponent ⟨Z, hZ⟩
  let W : Set Y := closure {f η.1}
  have hη : IsGenericPoint η.1 Z := genericPoints.isGenericPoint_ofComponent ⟨Z, hZ⟩
  refine ⟨W, mem_genericPoints_image_of_generalizingMap hfgeneral η, ?_⟩
  apply Set.Subset.antisymm
  · rw [← hη.def]
    simpa [W] using
      (image_closure_subset_closure_image (s := ({η.1} : Set X)) hfc)
  · apply closure_minimal
    · exact Set.singleton_subset_iff.mpr ⟨η.1, hη.mem, rfl⟩
    · exact hfclosed Z (isClosed_of_mem_irreducibleComponents Z hZ)

end TopologicalSpace

namespace CommRingCat

universe u

/-- In a pushout of commutative rings, base-changing a surjection extends
its kernel to the other leg. -/
lemma ker_inr_of_isPushout_of_surjective
    {R A B P : CommRingCat.{u}} {f : R ⟶ A} {g : R ⟶ B}
    {inl : A ⟶ P} {inr : B ⟶ P}
    (h : IsPushout f g inl inr) (hf : Function.Surjective f.hom) :
    RingHom.ker inr.hom = (RingHom.ker f.hom).map g.hom := by
  let J : Ideal B := (RingHom.ker f.hom).map g.hom
  let q : B →+* B ⧸ J := Ideal.Quotient.mk J
  let lift : R ⧸ RingHom.ker f.hom →+* B ⧸ J :=
    Ideal.Quotient.lift (RingHom.ker f.hom) (q.comp g.hom) (by
      intro r hr
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact Ideal.mem_map_of_mem g.hom hr)
  let e : R ⧸ RingHom.ker f.hom ≃+* A :=
    RingHom.quotientKerEquivOfSurjective hf
  let a : A →+* B ⧸ J := lift.comp e.symm.toRingHom
  have hcomm : f ≫ ofHom a = g ≫ ofHom q := by
    ext r
    change lift (e.symm (f.hom r)) = q (g.hom r)
    rw [RingHom.quotientKerEquivOfSurjective_symm_apply]
    rfl
  let d : P ⟶ of (B ⧸ J) := h.desc (ofHom a) (ofHom q) hcomm
  apply le_antisymm
  · intro x hx
    change x ∈ J
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q x = 0
    have hd := congr($(h.inr_desc (ofHom a) (ofHom q) hcomm).hom x)
    simp only [hom_comp, RingHom.coe_comp, Function.comp_apply, hom_ofHom] at hd
    rw [← hd]
    change d.hom (inr.hom x) = 0
    rw [show inr.hom x = 0 from hx]
    exact d.hom.map_zero
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change inr.hom (g.hom r) = 0
    have hw := congr($(h.w).hom r)
    simp only [hom_comp, RingHom.coe_comp, Function.comp_apply] at hw
    rw [← hw, show f.hom r = 0 from hr, map_zero]

end CommRingCat

namespace RingHom

universe u

/-- A regular system of parameters remains one after an etale local-ring
extension.  The assumptions are the three ring-map properties supplied by
an etale morphism on stalks. -/
lemma isRegularSystemOfParameters_map_of_flat_of_formallyUnramified_of_essFiniteType
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) [IsLocalRing R] [IsLocalRing S] [IsLocalHom f]
    (hflat : f.Flat) (hunramified : f.FormallyUnramified)
    (hfiniteType : f.EssFiniteType) {d : ℕ} (t : Fin d → R)
    (ht : AlgebraicGeometry.Scheme.IsRegularSystemOfParameters t) :
    AlgebraicGeometry.Scheme.IsRegularSystemOfParameters (fun i ↦ f (t i)) := by
  algebraize [f]
  let : Module.Flat R S := hflat
  let : Module.FaithfullyFlat R S :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  let : Algebra.FormallyUnramified R S := hunramified
  let : Algebra.EssFiniteType R S := hfiniteType
  change AlgebraicGeometry.Scheme.IsRegularSystemOfParameters
    (fun i ↦ algebraMap R S (t i))
  have hlist : List.ofFn (fun i ↦ algebraMap R S (t i)) =
      (List.ofFn t).map (algebraMap R S) := by
    rw [List.map_ofFn]
    congr 1
  constructor
  · rw [hlist]
    exact ht.1.of_faithfullyFlat (S := S)
  · rw [hlist, ← Ideal.map_ofList, ht.2,
      Algebra.FormallyUnramified.map_maximalIdeal]

end RingHom

namespace AlgebraicGeometry

universe u

namespace Scheme

/-- Residue characteristic is unchanged along a morphism of schemes. -/
lemma Hom.ringChar_residueField_eq {X Y : Scheme.{u}} (f : Y ⟶ X) (y : Y) :
    ringChar (Y.residueField y) = ringChar (X.residueField (f y)) := by
  let : Algebra (X.residueField (f y)) (Y.residueField y) :=
    (f.residueFieldMap y).hom.toAlgebra
  exact (Algebra.ringChar_eq (X.residueField (f y)) (Y.residueField y)).symm

namespace IdealSheafData

variable {X Y : Scheme.{u}}

/-- The stalk ideal can be computed from any affine neighbourhood of the
point.  This is the chart-independence source needed for local pullback
arguments; it follows from the localization compatibility built into
`IdealSheafData`. -/
lemma stalkIdeal_eq_map_ideal (I : X.IdealSheafData) (x : X)
    (U : X.affineOpens) (hxU : x ∈ U.1) :
    I.stalkIdeal x =
      (I.ideal U).map (X.presheaf.germ U.1 x hxU).hom := by
  apply le_antisymm
  · refine iSup_le fun V ↦ iSup_le fun hxV ↦ ?_
    obtain ⟨W, hW, hxW, hWle⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (U := U.1 ⊓ V.1)
        (x := x) ⟨hxU, hxV⟩
    let W' : X.affineOpens := ⟨W, hW⟩
    have hWU : W' ≤ U := fun z hz ↦ (hWle hz).1
    have hWV : W' ≤ V := fun z hz ↦ (hWle hz).2
    have hU := I.map_ideal hWU
    have hV := I.map_ideal hWV
    apply_fun Ideal.map (X.presheaf.germ W x hxW).hom at hU hV
    simp only [Ideal.map_map, ← CommRingCat.hom_comp] at hU hV
    simpa only [homOfLE_leOfHom, TopCat.Presheaf.germ_res'] using
      (hV.trans hU.symm).le
  · exact I.map_ideal_le_stalkIdeal x U hxU

/-- Taking the stalk ideal preserves multiplication of ideal sheaves. -/
lemma stalkIdeal_mul (I J : X.IdealSheafData) (x : X) :
    (I * J).stalkIdeal x = I.stalkIdeal x * J.stalkIdeal x := by
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x)
      (show x ∈ (⊤ : X.Opens) from trivial)
  let V : X.affineOpens := ⟨U, hU⟩
  rw [(I * J).stalkIdeal_eq_map_ideal x V hxU,
    I.stalkIdeal_eq_map_ideal x V hxU, J.stalkIdeal_eq_map_ideal x V hxU,
    Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Ideal.map_mul]

/-- Taking the stalk ideal commutes with finite products of ideal sheaves. -/
lemma stalkIdeal_finset_prod {ι : Type*} (s : Finset ι)
    (I : ι → X.IdealSheafData) (x : X) :
    (∏ i ∈ s, I i).stalkIdeal x = ∏ i ∈ s, (I i).stalkIdeal x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty, Scheme.IdealSheafData.one_eq_top,
      stalkIdeal_top, Ideal.one_eq_top]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, stalkIdeal_mul, ih]

/-- On an affine target chart, the ideal of a pulled-back closed subscheme is
the extension of the original ideal. -/
lemma ideal_comap_preimage_of_isAffineHom
    (I : X.IdealSheafData) (f : Y ⟶ X) [IsAffineHom f]
    (U : X.affineOpens) :
    (I.comap f).ideal ⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩ =
      (I.ideal U).map (f.app U.1).hom := by
  let i := I.subschemeι
  let P := pullback f i
  let fst : P ⟶ Y := pullback.fst f i
  let snd : P ⟶ I.subscheme := pullback.snd f i
  let V : Y.Opens := f ⁻¹ᵁ U.1
  let UX : I.subscheme.Opens := i ⁻¹ᵁ U.1
  let UY : P.Opens := fst ⁻¹ᵁ V
  have H : IsPullback snd fst i f := (IsPullback.of_hasPullback f i).flip
  have hUY : UY = snd ⁻¹ᵁ UX ⊓ fst ⁻¹ᵁ V := by
    ext z
    constructor
    · intro hz
      refine ⟨?_, hz⟩
      change i (snd z) ∈ U.1
      change f (fst z) ∈ U.1 at hz
      rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply]
      exact hz
    · exact fun hz ↦ hz.2
  have hUX : IsAffineOpen UX := U.2.preimage i
  have hV : IsAffineOpen V := U.2.preimage f
  let : IsIso (pushoutSection H (show V ≤ f ⁻¹ᵁ U.1 from le_rfl)
      (show UX ≤ i ⁻¹ᵁ U.1 from le_rfl) hUY) :=
    isIso_pushoutSection_of_isAffineOpen H le_rfl le_rfl hUY U.2 hV hUX
  have hpush : IsPushout (i.appLE U.1 UX le_rfl) (f.appLE U.1 V le_rfl)
      (snd.appLE UX UY (by simp [hUY])) (fst.appLE V UY (by simp [hUY])) :=
    (isIso_pushoutSection_iff H le_rfl le_rfl hUY).mp inferInstance
  have hi : i.appLE U.1 UX le_rfl = i.app U.1 := by
    dsimp [UX]
    exact i.appLE_eq_app
  have hf : f.appLE U.1 V le_rfl = f.app U.1 := by
    dsimp [V]
    exact f.appLE_eq_app
  have hfst : fst.appLE V UY (by simp [hUY]) = fst.app V := by
    dsimp [UY]
    exact fst.appLE_eq_app
  have hpush' : IsPushout (i.app U.1) (f.app U.1)
      (snd.appLE UX UY (by simp [hUY])) (fst.app V) := by
    rw [hi, hf, hfst] at hpush
    exact hpush
  rw [comap, Scheme.Hom.ker_apply]
  change RingHom.ker (fst.app V).hom = _
  rw [CommRingCat.ker_inr_of_isPushout_of_surjective hpush'
    (i.app_surjective U.1 U.2)]
  rw [I.ker_subschemeι_app U]

/-- For an affine morphism, the stalk ideal of a pulled-back ideal sheaf is
the extension of the original stalk ideal. -/
lemma stalkIdeal_comap_of_isAffineHom
    (I : X.IdealSheafData) (f : Y ⟶ X) [IsAffineHom f] (y : Y) :
    (I.comap f).stalkIdeal y =
      (I.stalkIdeal (f y)).map (f.stalkMap y).hom := by
  obtain ⟨U, hU, hfyU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := f y) (by simp)
  let U' : X.affineOpens := ⟨U, hU⟩
  let V' : Y.affineOpens := ⟨f ⁻¹ᵁ U, hU.preimage f⟩
  have hyV : y ∈ V'.1 := hfyU
  rw [stalkIdeal_eq_map_ideal (I.comap f) y V' hyV,
    ideal_comap_preimage_of_isAffineHom I f U',
    stalkIdeal_eq_map_ideal I (f y) U' hfyU,
    Ideal.map_map, Ideal.map_map]
  congr 1
  exact congrArg CommRingCat.Hom.hom (f.germ_stalkMap U (y : Y) hfyU).symm

/-- Ring homomorphisms commute with the product of an initial segment of a
parameter family. -/
lemma _root_.AlgebraicGeometry.Scheme.initialParameterProduct_map
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    {d : ℕ} (t : Fin d → R) (r : ℕ) (hr : r ≤ d) :
    φ (Scheme.initialParameterProduct t r hr) =
      Scheme.initialParameterProduct (fun j ↦ φ (t j)) r hr := by
  simp [Scheme.initialParameterProduct]

/-- Strict normal crossings at a point are preserved by finite-etale
pullback. -/
lemma IsStrictNormalCrossingsAt.comap_of_finiteEtale
    (I : X.IdealSheafData) (f : Y ⟶ X) [IsFiniteEtale f] (y : Y)
    (hI : I.IsStrictNormalCrossingsAt (f y)) :
    (I.comap f).IsStrictNormalCrossingsAt y := by
  obtain ⟨hreg, d, r, t, hrpos, hrd, ht, hideal⟩ := hI
  refine ⟨Scheme.IsRegularAt.of_etale f y hreg, d, r,
    (fun j ↦ (f.stalkMap y).hom (t j)), hrpos, hrd, ?_, ?_⟩
  · exact RingHom.isRegularSystemOfParameters_map_of_flat_of_formallyUnramified_of_essFiniteType
      (f.stalkMap y).hom (Flat.stalkMap f y) (FormallyUnramified.stalkMap f y)
        (LocallyOfFiniteType.stalkMap f y) t ht
  · rw [stalkIdeal_comap_of_isAffineHom I f y, hideal, Ideal.map_span,
      Set.image_singleton, initialParameterProduct_map]

/-- Normal crossings at a point are preserved by finite-etale pullback. -/
lemma IsNormalCrossingsAt.comap_of_finiteEtale
    (I : X.IdealSheafData) (f : Y ⟶ X) [IsFiniteEtale f] (y : Y)
    (hI : I.IsNormalCrossingsAt (f y)) :
    (I.comap f).IsNormalCrossingsAt y := by
  obtain ⟨U, g, u, hg, hgu, hstrict⟩ := hI
  let : Etale g := hg
  let P := pullback g f
  let fst : P ⟶ U := pullback.fst g f
  let snd : P ⟶ Y := pullback.snd g f
  let : IsFiniteEtale fst :=
    MorphismProperty.of_isPullback
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback g f).flip (show IsFiniteEtale f from inferInstance)
  let : Etale snd :=
    MorphismProperty.of_isPullback
      (P := (@Etale : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback g f) (show Etale g from inferInstance)
  obtain ⟨v, hvfst, hvsnd⟩ := Scheme.Pullback.exists_preimage_pullback u y hgu
  refine ⟨P, snd, v, inferInstance, hvsnd, ?_⟩
  have hcomap : (I.comap f).comap snd = (I.comap g).comap fst := by
    rw [← I.comap_comp, ← I.comap_comp, pullback.condition]
  rw [hcomap]
  intro z hz
  apply IsStrictNormalCrossingsAt.comap_of_finiteEtale (I.comap g) fst z
  apply hstrict (fst z)
  rw [support_comap] at hz
  exact hz

/-- The canonical morphism from the subscheme cut out by a pulled-back ideal
sheaf to the original subscheme.  It is presented as a pullback projection so
that morphism properties are inherited directly. -/
noncomputable def comapSubschemeTo (I : X.IdealSheafData) (f : Y ⟶ X) :
    (I.comap f).subscheme ⟶ I.subscheme :=
  (I.comapIso f).hom ≫ pullback.snd f I.subschemeι

instance (I : X.IdealSheafData) (f : Y ⟶ X) [IsFiniteEtale f] :
    IsFiniteEtale (I.comapSubschemeTo f) := by
  dsimp only [comapSubschemeTo]
  apply MorphismProperty.comp_mem @IsFiniteEtale
  · exact @IsFiniteEtale.mk _ _ _ inferInstance inferInstance
  · infer_instance

@[reassoc (attr := simp)]
lemma comapSubschemeTo_subschemeι (I : X.IdealSheafData) (f : Y ⟶ X) :
    I.comapSubschemeTo f ≫ I.subschemeι = (I.comap f).subschemeι ≫ f := by
  rw [comapSubschemeTo, I.comapIso_hom_snd]
  exact (I.comap f).subschemeMap_subschemeι I f (I.le_map_comap f)

/-- Every irreducible component of a finite-etale pullback of a closed
subscheme maps onto an irreducible component of the original subscheme. -/
lemma exists_irreducibleComponent_image_comapSubschemeTo_eq
    (I : X.IdealSheafData) (f : Y ⟶ X) [IsFiniteEtale f]
    (Z : Set (I.comap f).subscheme)
    (hZ : Z ∈ irreducibleComponents (I.comap f).subscheme) :
    ∃ W : Set I.subscheme,
      W ∈ irreducibleComponents I.subscheme ∧ I.comapSubschemeTo f '' Z = W := by
  let g := I.comapSubschemeTo f
  let : IsFiniteEtale g := inferInstance
  exact TopologicalSpace.exists_irreducibleComponent_image_eq
    g.continuous g.isClosedMap (Flat.generalizingMap g) Z hZ

end IdealSheafData

namespace EffectiveCartierDivisor

variable {X Y S : Scheme.{u}}

/-- A residue-characteristic point on an original boundary component lifts
to every irreducible component of a finite-etale pullback lying over it.
The normal-crossings assertion is retained at the image point; upgrading it
to normal crossings for the pulled-back ideal sheaf is the separate local
strict-normal-crossings base-change step. -/
lemma exists_residueCharacteristicPoint_on_comapComponent
    (D : EffectiveCartierDivisor X) (f : Y ⟶ X) [IsFiniteEtale f]
    (q : ℕ) (hD : D.HasNormalCrossingPointOfResidueCharacteristicOnEachComponent q)
    (Z : Set (D.1.comap f).subscheme)
    (hZ : Z ∈ irreducibleComponents (D.1.comap f).subscheme) :
    ∃ y : (D.1.comap f).subscheme,
      y ∈ Z ∧
        ringChar (Y.residueField ((D.1.comap f).subschemeι y)) = q ∧
          D.IsNormalCrossingsAt (f ((D.1.comap f).subschemeι y)) := by
  let g := D.1.comapSubschemeTo f
  obtain ⟨W, hW, himage⟩ :=
    D.1.exists_irreducibleComponent_image_comapSubschemeTo_eq f Z hZ
  obtain ⟨x, hxW, hxchar, hxnc⟩ := hD W hW
  have hximage : x ∈ g '' Z := by
    rw [himage]
    exact hxW
  obtain ⟨y, hyZ, hgy⟩ := hximage
  change D.1.comapSubschemeTo f y = x at hgy
  have hpoint : f ((D.1.comap f).subschemeι y) = D.1.subschemeι x := by
    rw [← Scheme.Hom.comp_apply, ← D.1.comapSubschemeTo_subschemeι]
    simp only [Scheme.Hom.comp_apply, hgy]
  refine ⟨y, hyZ, ?_, ?_⟩
  · refine (f.ringChar_residueField_eq ((D.1.comap f).subschemeι y)).trans ?_
    rw [hpoint]
    exact hxchar
  · rw [hpoint]
    exact hxnc

/-- Every component of a finite-etale pullback contains a point of the
prescribed residue characteristic where the pulled-back boundary itself has
normal crossings. -/
lemma exists_normalCrossingPointOfResidueCharacteristic_on_comapComponent
    (D : EffectiveCartierDivisor X) (f : Y ⟶ X) [IsFiniteEtale f]
    (q : ℕ) (hD : D.HasNormalCrossingPointOfResidueCharacteristicOnEachComponent q)
    (Z : Set (D.1.comap f).subscheme)
    (hZ : Z ∈ irreducibleComponents (D.1.comap f).subscheme) :
    ∃ y : (D.1.comap f).subscheme,
      y ∈ Z ∧
        ringChar (Y.residueField ((D.1.comap f).subschemeι y)) = q ∧
          (D.1.comap f).IsNormalCrossingsAt ((D.1.comap f).subschemeι y) := by
  obtain ⟨y, hyZ, hychar, hync⟩ :=
    D.exists_residueCharacteristicPoint_on_comapComponent f q hD Z hZ
  exact ⟨y, hyZ, hychar,
    IdealSheafData.IsNormalCrossingsAt.comap_of_finiteEtale D.1 f _ hync⟩

end EffectiveCartierDivisor

end Scheme

end AlgebraicGeometry

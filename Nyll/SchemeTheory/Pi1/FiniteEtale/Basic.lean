/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/

/-
Adapted from the pinned pi1 source:
https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/FundamentalGroup/FiniteEtale.lean
-/

/-
This is a Nyll-maintained port, not an unmodified upstream file.
Local changes adapt imports, proofs and API compatibility to the pinned Nyll toolchain.
Upstream notices above apply to the upstream-derived code; they are not replaced by
Nyll authorship. Revision, file hashes and modification provenance are recorded in
Nyll/EtaleFundamentalGroups/Pi1/UPSTREAM.json and ATTRIBUTION.md.

Local proof adaptations and compatibility additions:
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Authors of local modifications: Naganori Yamaguchi (assisted by OpenAI Codex).
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Nyll.SchemeTheory.Pi1.Morphisms.Finite
public import Nyll.SchemeTheory.Pi1.Etale.RingHom
public import Nyll.SchemeTheory.Pi1.Affine.Property
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Algebra.Splitting

/-!
# Finite étale morphisms

We say a morphism is finite étale if it is finite and étale. The category `FiniteEtale X` is
the category of finite etale schemes over `X`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace Algebra

end Algebra

namespace RingHom

/-- A ring homomorphism is finite étale if the induced algebra is finite étale. -/
def FiniteEtale {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.FiniteEtale R S

lemma finiteEtale_algebraMap_iff {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    (algebraMap R S).FiniteEtale ↔ Algebra.FiniteEtale R S := by
  simp only [RingHom.FiniteEtale]
  congr!
  exact Algebra.algebra_ext _ _ fun _ ↦ rfl

namespace FiniteEtale

lemma iff_finite_and_etale
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    f.FiniteEtale ↔ f.Etale ∧ f.Finite := by
  rw [FiniteEtale, Finite, Etale]
  rw [Algebra.finiteEtale_iff]

lemma eq_and :
    @FiniteEtale = (fun R S (_ : CommRing R) (_ : CommRing S) f ↦ f.Etale ∧ f.Finite) := by
  ext
  rw [iff_finite_and_etale]

lemma isStableUnderBaseChange : IsStableUnderBaseChange FiniteEtale := by
  rw [eq_and]
  exact Etale.isStableUnderBaseChange.and finite_isStableUnderBaseChange

lemma respectsIso : RespectsIso FiniteEtale := by
  rw [eq_and]
  apply Etale.respectsIso.and finite_respectsIso

lemma hasFiniteProducts : HasFiniteProducts FiniteEtale := by
  introv R _ hf
  simp_rw [finiteEtale_algebraMap_iff] at hf ⊢
  constructor

lemma hasEqualizers : HasEqualizers FiniteEtale := by
  introv R hS hT
  rw [finiteEtale_algebraMap_iff] at hS hT ⊢
  apply Algebra.Etale.equalizer

lemma hasStableEqualizers : HasStableEqualizers FiniteEtale := by
  introv R hA hB
  rw [finiteEtale_algebraMap_iff] at hA hB
  exact Algebra.tensorEqualizer_bijective_of_finite_of_etale f g

instance : (toMorphismProperty RingHom.FiniteEtale).IsStableUnderCobaseChange := by
  rw [isStableUnderCobaseChange_toMorphismProperty_iff]
  exact isStableUnderBaseChange

end FiniteEtale

end RingHom

namespace AlgebraicGeometry

/-- A morphism is finite étale if it is finite and étale. -/
@[mk_iff]
class IsFiniteEtale {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop
  extends IsFinite f, Etale f

namespace IsFiniteEtale

open MorphismProperty

lemma eq_inf :
    (@IsFiniteEtale : MorphismProperty Scheme.{u}) =
      (show MorphismProperty Scheme.{u} from
        (@IsFinite : MorphismProperty Scheme.{u}) ⊓
          (@Etale : MorphismProperty Scheme.{u})) := by
  ext f
  rw [isFiniteEtale_iff]
  rfl

instance : ContainsIdentities
    (@IsFiniteEtale : MorphismProperty Scheme.{u}) where
  id_mem X := @IsFiniteEtale.mk _ _ _
    (by infer_instance) (by infer_instance)

instance : IsStableUnderComposition
    (@IsFiniteEtale : MorphismProperty Scheme.{u}) where
  comp_mem f g hf hg := by
    let _ : IsFinite f := hf.toIsFinite
    let _ : IsFinite g := hg.toIsFinite
    let _ : Etale f := hf.toEtale
    let _ : Etale g := hg.toEtale
    exact @IsFiniteEtale.mk _ _ _ inferInstance inferInstance

instance : IsMultiplicative
    (@IsFiniteEtale : MorphismProperty Scheme.{u}) where

instance : IsStableUnderBaseChange
    (@IsFiniteEtale : MorphismProperty Scheme.{u}) where
  of_isPullback h hg := @IsFiniteEtale.mk _ _ _
    (MorphismProperty.of_isPullback
      (P := (@IsFinite : MorphismProperty Scheme.{u})) h hg.toIsFinite)
    (MorphismProperty.of_isPullback
      (P := (@Etale : MorphismProperty Scheme.{u})) h hg.toEtale)

instance : HasOfPostcompProperty
    (@IsFiniteEtale : MorphismProperty Scheme.{u})
    (@IsFiniteEtale : MorphismProperty Scheme.{u}) where
  of_postcomp f g hg hfg := @IsFiniteEtale.mk _ _ _
    (MorphismProperty.of_postcomp
      (@IsFinite : MorphismProperty Scheme.{u}) f g hg.toIsFinite hfg.toIsFinite)
    (MorphismProperty.of_postcomp
      (@Etale : MorphismProperty Scheme.{u}) f g hg.toEtale hfg.toEtale)

instance : HasAffineProperty
    (@IsFiniteEtale : MorphismProperty Scheme.{u})
    (affineAnd RingHom.FiniteEtale) := by
  let hFiniteAffine : HasAffineProperty
      (@IsFinite : MorphismProperty Scheme.{u})
      (affineAnd RingHom.Finite) := by
    rw [HasAffineProperty.affineAnd_iff
      (@IsFinite : MorphismProperty Scheme.{u})
      RingHom.finite_respectsIso
      RingHom.finite_localizationPreserves.away
      RingHom.finite_ofLocalizationSpan]
    intro X Y f
    exact isFinite_iff f
  let hEtaleRing : HasRingHomProperty
      (@Etale : MorphismProperty Scheme.{u}) RingHom.Etale :=
    { isLocal_ringHomProperty := RingHom.Etale.propertyIsLocal
      eq_affineLocally' := by
        ext X Y f
        rw [etale_iff, affineLocally_iff_forall_isAffineOpen] }
  let _ : HasAffineProperty
      (@IsFinite : MorphismProperty Scheme.{u})
      (affineAnd RingHom.Finite) := hFiniteAffine
  let _ : HasRingHomProperty
      (@Etale : MorphismProperty Scheme.{u}) RingHom.Etale := hEtaleRing
  have hFiniteLocal : IsZariskiLocalAtTarget
      (@IsFinite : MorphismProperty Scheme.{u}) :=
    (HasAffineProperty.iff
      (P := (@IsFinite : MorphismProperty Scheme.{u}))
      (Q := affineAnd RingHom.Finite)).mp hFiniteAffine |>.1
  have hEtaleAffine : HasAffineProperty
      (@Etale : MorphismProperty Scheme.{u})
      (sourceAffineLocally RingHom.Etale) :=
    { isLocal_affineProperty := sourceAffineLocally_isLocal _
        hEtaleRing.isLocal_ringHomProperty.respectsIso
        hEtaleRing.isLocal_ringHomProperty.localizationAwayPreserves
        hEtaleRing.isLocal_ringHomProperty.ofLocalizationSpan
      eq_targetAffineLocally' := hEtaleRing.eq_affineLocally' }
  have hEtaleLocal : IsZariskiLocalAtTarget
      (@Etale : MorphismProperty Scheme.{u}) :=
    (HasAffineProperty.iff
      (P := (@Etale : MorphismProperty Scheme.{u}))
      (Q := sourceAffineLocally RingHom.Etale)).mp hEtaleAffine |>.1
  have hInfLocal : IsZariskiLocalAtTarget
      (show MorphismProperty Scheme.{u} from
        (@IsFinite : MorphismProperty Scheme.{u}) ⊓
          (@Etale : MorphismProperty Scheme.{u})) :=
    @MorphismProperty.IsLocalAtTarget.inf _ _ _
      (@IsFinite : MorphismProperty Scheme.{u})
      (@Etale : MorphismProperty Scheme.{u}) hFiniteLocal hEtaleLocal
  have hEq : affineAnd RingHom.FiniteEtale =
      AffineTargetMorphismProperty.of
        (show MorphismProperty Scheme.{u} from
          (@IsFinite : MorphismProperty Scheme.{u}) ⊓
            (@Etale : MorphismProperty Scheme.{u})) := by
    ext X Y f _
    change affineAnd RingHom.FiniteEtale f ↔ IsFinite f ∧ Etale f
    rw [affineAnd_apply, RingHom.FiniteEtale.iff_finite_and_etale]
    constructor
    · rintro ⟨hX, hEtale, hFinite⟩
      let _ : IsAffine X := hX
      exact ⟨
        (HasAffineProperty.iff_of_isAffine
          (P := (@IsFinite : MorphismProperty Scheme.{u}))
          (Q := affineAnd RingHom.Finite) (f := f)).mpr ⟨hX, hFinite⟩,
        (HasRingHomProperty.iff_of_isAffine
          (P := (@Etale : MorphismProperty Scheme.{u}))
          (Q := RingHom.Etale) (f := f)).mpr hEtale⟩
    · rintro ⟨hFinite, hEtale⟩
      have hAffineFinite : affineAnd RingHom.Finite f :=
        (HasAffineProperty.iff_of_isAffine
          (P := (@IsFinite : MorphismProperty Scheme.{u}))
          (Q := affineAnd RingHom.Finite) (f := f)).mp hFinite
      obtain ⟨hX, hFinite⟩ := hAffineFinite
      let _ : IsAffine X := hX
      have hEtale' : RingHom.Etale (f.appTop).hom :=
        (HasRingHomProperty.iff_of_isAffine
          (P := (@Etale : MorphismProperty Scheme.{u}))
          (Q := RingHom.Etale) (f := f)).mp hEtale
      exact ⟨hX, hEtale', hFinite⟩
  have hInfHAP : HasAffineProperty
      (show MorphismProperty Scheme.{u} from
        (@IsFinite : MorphismProperty Scheme.{u}) ⊓
          (@Etale : MorphismProperty Scheme.{u}))
      (affineAnd RingHom.FiniteEtale) :=
    (HasAffineProperty.iff
      (P := (show MorphismProperty Scheme.{u} from
        (@IsFinite : MorphismProperty Scheme.{u}) ⊓
          (@Etale : MorphismProperty Scheme.{u})))
      (Q := affineAnd RingHom.FiniteEtale)).mpr ⟨hInfLocal, hEq⟩
  exact eq_inf.symm ▸ hInfHAP

instance {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsFiniteEtale f] [IsFiniteEtale g] :
    IsFiniteEtale (f ≫ g) where

lemma mono_iff {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFiniteEtale f] :
    Mono f ↔ IsOpenImmersion f ∧ IsClosedImmersion f := by
  refine ⟨fun hf ↦ ⟨inferInstance, ?_⟩, fun ⟨hfo, _⟩ ↦ inferInstance⟩
  · rw [IsClosedImmersion.iff_isFinite_and_mono]
    exact ⟨inferInstance, inferInstance⟩

end IsFiniteEtale

/-- The category of schemes finite étale over `X`. -/
def FiniteEtale (X : Scheme.{u}) : Type _ :=
  MorphismProperty.Over
    (@IsFiniteEtale : MorphismProperty Scheme.{u})
    (⊤ : MorphismProperty Scheme.{u}) X

namespace FiniteEtale

variable (X : Scheme.{u})

instance : Category (FiniteEtale X) := by
  unfold FiniteEtale
  exact MorphismProperty.Comma.instCategory
    (Functor.id Scheme) (Functor.fromPUnit X)
    (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ ⊤

local instance finiteEtaleOverCategory (X : Scheme.{u}) :
    Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme.{u})
      (⊤ : MorphismProperty Scheme.{u}) X) :=
  instCategory X

local instance finiteEtaleHasPullbacksAlong
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun _ _ ↦ inferInstance⟩

local instance finiteEtaleIsStableUnderBaseChangeAlong
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) h hf⟩

/-- The forgetful functor from schemes finite étale over `X` to schemes over `X`. -/
def forget : FiniteEtale X ⥤ Over X :=
  MorphismProperty.Over.forget
    (@IsFiniteEtale : MorphismProperty Scheme.{u})
    (⊤ : MorphismProperty Scheme.{u}) X

/-- The forgetful functor from schemes finite étale over `X` to schemes over `X` is fully
faithful. -/
def forgetFullyFaithful : (FiniteEtale.forget X).FullyFaithful :=
  MorphismProperty.Comma.forgetFullyFaithful
    (Functor.id Scheme) (Functor.fromPUnit X)
    (@IsFiniteEtale : MorphismProperty Scheme.{u})

instance : (FiniteEtale.forget X).Full :=
  (forgetFullyFaithful X).full
instance : (FiniteEtale.forget X).Faithful :=
  (forgetFullyFaithful X).faithful

instance : HasTerminal (FiniteEtale X) :=
  (MorphismProperty.Over.mkIdTerminal
    (@IsFiniteEtale : MorphismProperty Scheme.{u}) X).hasTerminal

instance : HasPullbacks (FiniteEtale X) :=
  MorphismProperty.Over.hasPullbacks
    (@IsFiniteEtale : MorphismProperty Scheme.{u}) X

instance (f : FiniteEtale X) : IsFiniteEtale f.hom := f.2

/-- The forgetful functor to the category of schemes affine over `X`. -/
def toAffine : FiniteEtale X ⥤ Affine X where
  obj f := ⟨f.toComma, inferInstance⟩
  map {X Y} f := ⟨f.toCommaMorphism, trivial, trivial⟩

/-- The fully faithful embedding of finite étale schemes over `X` into affine schemes over `X`. -/
def toAffineFullyFaithful : (toAffine X).FullyFaithful where
  preimage f := ⟨f.toCommaMorphism, trivial, trivial⟩

instance : (toAffine X).Faithful := (toAffineFullyFaithful X).faithful
instance : (toAffine X).Full := (toAffineFullyFaithful X).full

instance : HasFiniteColimits (FiniteEtale X) :=
  AffineAnd.hasFiniteColimits
    (@IsFiniteEtale : MorphismProperty Scheme.{u})
    RingHom.FiniteEtale.respectsIso
    RingHom.FiniteEtale.hasFiniteProducts
    RingHom.FiniteEtale.hasEqualizers

instance (f g : FiniteEtale X) (i : f ⟶ g) : IsFiniteEtale i.hom.left := by
  apply MorphismProperty.of_postcomp
    (@IsFiniteEtale : MorphismProperty Scheme.{u})
    (W' := (@IsFiniteEtale : MorphismProperty Scheme.{u})) _ g.hom
  · exact g.2
  · rw [MorphismProperty.Over.w i]
    exact f.2

lemma mono_iff (f g : FiniteEtale X) (i : f ⟶ g) :
    Mono i ↔ IsOpenImmersion i.hom.left ∧ IsClosedImmersion i.hom.left := by
  rw [← IsFiniteEtale.mono_iff]
  let G : FiniteEtale X ⥤ Over X := FiniteEtale.forget X
  let _ : CreatesLimitsOfShape WalkingCospan G := by
    dsimp only [G, FiniteEtale.forget]
    exact MorphismProperty.Over.createsLimitsOfShape_walkingCospan
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) X
  have : PreservesLimitsOfShape WalkingCospan G := by
    infer_instance
  let F : FiniteEtale X ⥤ Scheme.{u} :=
    G ⋙ Over.forget X
  have : PreservesLimitsOfShape WalkingCospan F := inferInstance
  refine ⟨fun hi ↦ ?_, fun hi ↦ ?_⟩
  · change Mono (F.map i)
    exact @Functor.map_mono _ _ _ _ F inferInstance _ _ i hi
  · apply F.mono_of_mono_map (f := i)
    change Mono i.hom.left
    exact hi

variable {X}

/-- Base change of finite étale schemes along `f`. -/
abbrev pullback {Y : Scheme.{u}} (f : X ⟶ Y) : FiniteEtale Y ⥤ FiniteEtale X :=
  MorphismProperty.Over.pullback
    (@IsFiniteEtale : MorphismProperty Scheme.{u})
    (⊤ : MorphismProperty Scheme.{u}) f

/-- A finite étale morphism `f : T ⟶ X` viewed as an object of `FiniteEtale X`. -/
def mk {T : Scheme.{u}} (f : T ⟶ X) [IsFiniteEtale f] : FiniteEtale X :=
  MorphismProperty.Over.mk
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u}))
    (⊤ : MorphismProperty Scheme.{u}) f inferInstance

@[simp]
lemma mk_hom {T : Scheme.{u}} (f : T ⟶ X) [IsFiniteEtale f] : (mk f).hom = f := rfl

@[simp]
lemma mk_left {T : Scheme.{u}} (f : T ⟶ X) [IsFiniteEtale f] : (mk f).left = T := rfl

open RingHom in
instance {Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (pullback f) := by
  have (R S : CommRingCat.{u}) (f : R ⟶ S) :
      PreservesFiniteLimits (MorphismProperty.Under.pushout
        (RingHom.toMorphismProperty RingHom.FiniteEtale) ⊤ f) := by
    exact FiniteEtale.hasStableEqualizers.preservesFiniteLimits_pushout
      FiniteEtale.respectsIso FiniteEtale.hasFiniteProducts FiniteEtale.hasEqualizers f
  change PreservesFiniteColimits (MorphismProperty.Over.pullback
    (@IsFiniteEtale : MorphismProperty Scheme.{u})
    (⊤ : MorphismProperty Scheme.{u}) f)
  exact AffineAnd.preservesFiniteColimits_pullback
    (X := X) (Y := Y)
    (@IsFiniteEtale : MorphismProperty Scheme.{u})
    FiniteEtale.respectsIso
    FiniteEtale.hasFiniteProducts
    FiniteEtale.hasEqualizers f

end FiniteEtale

end AlgebraicGeometry

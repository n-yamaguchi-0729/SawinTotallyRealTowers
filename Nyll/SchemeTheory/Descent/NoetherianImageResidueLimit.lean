/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.SchemeTheory.RingTheory.SubalgebraResidueFieldColimit
import Nyll.SchemeTheory.Descent.NoetherianImageApproximation
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Actual residue fibers of the Noetherian image approximation

The fibers of the actual stage images over the contracted primes form an
inverse system. Its limit is the actual fiber of the original closed
subscheme. The three limits used here are supplied by the image construction,
the exhaustive subalgebra construction, and the residue-field colimit theorem.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.SubalgebraStages

universe u

variable {A₀ A : Type u} [CommRing A₀] [CommRing A] [Algebra A₀ A]
variable {ι : Type u} [Preorder ι] (S : ι →o Subalgebra A₀ A)
variable (p : Ideal A) [p.IsPrime]

/-- The spectra of the actual residue fields at the contracted stage primes. -/
abbrev residueSpecDiagram : ιᵒᵖ ⥤ Scheme.{u} :=
  (residueDiagram S p).op ⋙ Scheme.Spec

instance (i : ιᵒᵖ) : IsAffine ((residueSpecDiagram S p).obj i) :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of (residuePrime S p i.unop).ResidueField)))

instance (i : ιᵒᵖ) : CompactSpace ((residueSpecDiagram S p).obj i) :=
  inferInstanceAs (CompactSpace (Spec (CommRingCat.of (residuePrime S p i.unop).ResidueField)))

instance (i : ιᵒᵖ) : QuasiSeparatedSpace ((residueSpecDiagram S p).obj i) :=
  inferInstanceAs
    (QuasiSeparatedSpace (Spec (CommRingCat.of (residuePrime S p i.unop).ResidueField)))

/-- The cone from the spectrum of the original residue field. -/
abbrev residueSpecCone : Cone (residueSpecDiagram S p) :=
  Scheme.Spec.mapCone (residueCocone S p).op

/-- The residue point of a stage is its actual algebra-map spectrum morphism. -/
abbrev residueSpecBase (i : ιᵒᵖ) :
    (residueSpecDiagram S p).obj i ⟶ (specDiagram S).obj i :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (S i.unop) (residuePrime S p i.unop).ResidueField))

/-- The original residue point, before approximation. -/
abbrev residueSpecBaseTop : Spec (CommRingCat.of p.ResidueField) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))

@[reassoc]
lemma residueSpecBase_naturality {i j : ιᵒᵖ} (h : i ⟶ j) :
    (residueSpecDiagram S p).map h ≫ residueSpecBase S p j =
      residueSpecBase S p i ≫ (specDiagram S).map h := by
  change Spec.map (CommRingCat.ofHom (residueTrans S p h.unop.le)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (S j.unop) _)) =
    Spec.map (CommRingCat.ofHom (algebraMap (S i.unop) _)) ≫
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (S.mono h.unop.le)).toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact residueTrans_algebraMap S p h.unop.le a

/-- The actual residue points constitute a natural transformation over the stage spectra. -/
def residueSpecBaseMaps : residueSpecDiagram S p ⟶ specDiagram S where
  app i := residueSpecBase S p i
  naturality _ _ h := residueSpecBase_naturality S p h

@[reassoc]
lemma residueSpecCone_projection_base (i : ιᵒᵖ) :
    (residueSpecCone S p).π.app i ≫ residueSpecBase S p i =
      residueSpecBaseTop p ≫ (specCone S).π.app i := by
  change Spec.map (CommRingCat.ofHom (residueLeg S p i.unop)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (S i.unop) _)) =
    Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField)) ≫
      Spec.map (CommRingCat.ofHom (S i.unop).val.toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact residueLeg_algebraMap S p i.unop a

/-- Spectra turn the actual residue-field colimit into the actual residue-point limit. -/
def residueSpecConeIsLimit [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (hS : ∀ a : A, ∃ i, a ∈ S i) : IsLimit (residueSpecCone S p) :=
  isLimitOfPreserves Scheme.Spec (residueCoconeIsColimit S p hS).op

end AlgebraicGeometry.SubalgebraStages

namespace AlgebraicGeometry.NoetherianImageApproximation

universe u

variable (A₀ A : Type u) [CommRing A₀] [CommRing A] [Algebra A₀ A]
variable {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
variable {Z : Scheme.{u}} (j : Z ⟶ (ambientCone A₀ A f₀).pt)
variable (p : Ideal A) [p.IsPrime]

open SubalgebraStages in
/-- The actual fiber of a stage image at the contraction of the original prime. -/
abbrev residueFiberObj (i : (FGSubalgebra A₀ A)ᵒᵖ) : Scheme.{u} :=
  pullback (baseMap A₀ A f₀ j i) (residueSpecBase (subalgebras A₀ A) p i)

instance (i : (FGSubalgebra A₀ A)ᵒᵖ) :
    IsAffineHom (pullback.fst (baseMap A₀ A f₀ j i)
      (SubalgebraStages.residueSpecBase (subalgebras A₀ A) p i)) := by
  have : MorphismProperty.IsStableUnderBaseChange (@IsAffineHom) :=
    isAffineHom_isStableUnderBaseChange
  exact MorphismProperty.of_isPullback (P := @IsAffineHom)
    (IsPullback.of_hasPullback (baseMap A₀ A f₀ j i)
      (SubalgebraStages.residueSpecBase (subalgebras A₀ A) p i)).flip
    (isAffineHom_of_isAffine (SubalgebraStages.residueSpecBase (subalgebras A₀ A) p i))

open SubalgebraStages in
/-- The actual fiber transition induced by the image and residue-field maps. -/
def residueFiberTrans {i k : (FGSubalgebra A₀ A)ᵒᵖ} (h : i ⟶ k) :
    residueFiberObj A₀ A f₀ j p i ⟶ residueFiberObj A₀ A f₀ j p k :=
  pullback.map _ _ _ _ ((diagram A₀ A f₀ j).map h)
    ((residueSpecDiagram (subalgebras A₀ A) p).map h)
    ((specDiagram (subalgebras A₀ A)).map h)
    (transition_baseMap A₀ A f₀ j h).symm
    (residueSpecBase_naturality (subalgebras A₀ A) p h).symm

@[reassoc]
lemma residueFiberTrans_fst {i k : (FGSubalgebra A₀ A)ᵒᵖ} (h : i ⟶ k) :
    residueFiberTrans A₀ A f₀ j p h ≫
        pullback.fst (baseMap A₀ A f₀ j k)
          (SubalgebraStages.residueSpecBase (subalgebras A₀ A) p k) =
      pullback.fst (baseMap A₀ A f₀ j i)
        (SubalgebraStages.residueSpecBase (subalgebras A₀ A) p i) ≫
          (diagram A₀ A f₀ j).map h :=
  pullback.lift_fst _ _ _

@[reassoc]
lemma residueFiberTrans_snd {i k : (FGSubalgebra A₀ A)ᵒᵖ} (h : i ⟶ k) :
    residueFiberTrans A₀ A f₀ j p h ≫
        pullback.snd (baseMap A₀ A f₀ j k)
          (SubalgebraStages.residueSpecBase (subalgebras A₀ A) p k) =
      pullback.snd (baseMap A₀ A f₀ j i)
        (SubalgebraStages.residueSpecBase (subalgebras A₀ A) p i) ≫
          (SubalgebraStages.residueSpecDiagram (subalgebras A₀ A) p).map h :=
  pullback.lift_snd _ _ _

/-- The inverse system of actual residue fibers of the actual image stages. -/
@[reducible] def residueFiberDiagram : (FGSubalgebra A₀ A)ᵒᵖ ⥤ Scheme.{u} where
  obj i := residueFiberObj A₀ A f₀ j p i
  map h := residueFiberTrans A₀ A f₀ j p h
  map_id i := by
    apply pullback.hom_ext
    · rw [residueFiberTrans_fst, CategoryTheory.Functor.map_id,
        Category.comp_id, Category.id_comp]
    · rw [residueFiberTrans_snd, CategoryTheory.Functor.map_id,
        Category.comp_id, Category.id_comp]
  map_comp h h' := by
    apply pullback.hom_ext
    · rw [residueFiberTrans_fst, Category.assoc, residueFiberTrans_fst,
        residueFiberTrans_fst_assoc, CategoryTheory.Functor.map_comp]
    · rw [residueFiberTrans_snd, Category.assoc, residueFiberTrans_snd,
        residueFiberTrans_snd_assoc, CategoryTheory.Functor.map_comp]
      simp only [SubalgebraStages.residueSpecDiagram, CategoryTheory.Functor.comp_map]

/-- Projection of the actual fiber system to the image system. -/
def residueFiberFst : residueFiberDiagram A₀ A f₀ j p ⟶ diagram A₀ A f₀ j where
  app i := pullback.fst (baseMap A₀ A f₀ j i)
    (SubalgebraStages.residueSpecBase (subalgebras A₀ A) p i)
  naturality _ _ h := residueFiberTrans_fst A₀ A f₀ j p h

/-- Projection of the actual fiber system to the residue-field spectrum system. -/
def residueFiberSnd : residueFiberDiagram A₀ A f₀ j p ⟶
    SubalgebraStages.residueSpecDiagram (subalgebras A₀ A) p where
  app i := pullback.snd (baseMap A₀ A f₀ j i)
    (SubalgebraStages.residueSpecBase (subalgebras A₀ A) p i)
  naturality _ _ h := residueFiberTrans_snd A₀ A f₀ j p h

/-- The actual structure map of the original closed subscheme to the ambient ring. -/
abbrev originalBaseMap : Z ⟶ Spec (CommRingCat.of A) :=
  j ≫ pullback.snd f₀ (SubalgebraStages.specHomTop (A₀ := A₀) (A := A))

/-- The original fiber over the actual original residue field. -/
abbrev originalResidueFiber : Scheme.{u} :=
  pullback (originalBaseMap A₀ A f₀ j) (SubalgebraStages.residueSpecBaseTop p)

open SubalgebraStages in
/-- The original fiber maps to each actual stage fiber. -/
def residueFiberLeg (i : (FGSubalgebra A₀ A)ᵒᵖ) :
    originalResidueFiber A₀ A f₀ j p ⟶ residueFiberObj A₀ A f₀ j p i :=
  pullback.map _ _ _ _ ((cone A₀ A f₀ j).π.app i)
    ((residueSpecCone (subalgebras A₀ A) p).π.app i)
    ((specCone (subalgebras A₀ A)).π.app i)
    (cone_projection_baseMap A₀ A f₀ j i).symm
    (residueSpecCone_projection_base (subalgebras A₀ A) p i).symm

@[reassoc]
lemma residueFiberLeg_fst (i : (FGSubalgebra A₀ A)ᵒᵖ) :
    residueFiberLeg A₀ A f₀ j p i ≫
        pullback.fst (baseMap A₀ A f₀ j i)
          (SubalgebraStages.residueSpecBase (subalgebras A₀ A) p i) =
      pullback.fst (originalBaseMap A₀ A f₀ j) (SubalgebraStages.residueSpecBaseTop p) ≫
        (cone A₀ A f₀ j).π.app i :=
  pullback.lift_fst _ _ _

@[reassoc]
lemma residueFiberLeg_snd (i : (FGSubalgebra A₀ A)ᵒᵖ) :
    residueFiberLeg A₀ A f₀ j p i ≫
        pullback.snd (baseMap A₀ A f₀ j i)
          (SubalgebraStages.residueSpecBase (subalgebras A₀ A) p i) =
      pullback.snd (originalBaseMap A₀ A f₀ j) (SubalgebraStages.residueSpecBaseTop p) ≫
        (SubalgebraStages.residueSpecCone (subalgebras A₀ A) p).π.app i :=
  pullback.lift_snd _ _ _

/-- The actual original fiber is a cone over the actual stage fibers. -/
@[reducible] def residueFiberCone : Cone (residueFiberDiagram A₀ A f₀ j p) where
  pt := originalResidueFiber A₀ A f₀ j p
  π :=
    { app i := residueFiberLeg A₀ A f₀ j p i
      naturality i k h := by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
        apply pullback.hom_ext
        · rw [Category.assoc, residueFiberTrans_fst, residueFiberLeg_fst_assoc,
            (cone A₀ A f₀ j).w h, residueFiberLeg_fst]
        · rw [Category.assoc, residueFiberTrans_snd, residueFiberLeg_snd_assoc,
            (SubalgebraStages.residueSpecCone (subalgebras A₀ A) p).w h,
            residueFiberLeg_snd] }

/-- Each actual residue-fiber transition is affine. -/
instance {i k : (FGSubalgebra A₀ A)ᵒᵖ} (h : i ⟶ k) :
    IsAffineHom ((residueFiberDiagram A₀ A f₀ j p).map h) := by
  change IsAffineHom (residueFiberTrans A₀ A f₀ j p h)
  have : IsAffineHom ((ambientDiagram A₀ A f₀).map h) :=
    SubalgebraStages.isAffineHom_diagram_map (subalgebras A₀ A) f₀ h
  have : IsAffineHom ((diagram A₀ A f₀ j).map h) :=
    inferInstanceAs (IsAffineHom ((AffineTransitionImage.diagram
      (ambientDiagram A₀ A f₀) (ambientCone A₀ A f₀) j).map h))
  have : IsAffineHom (residueFiberTrans A₀ A f₀ j p h ≫
      pullback.fst (baseMap A₀ A f₀ j k)
        (SubalgebraStages.residueSpecBase (subalgebras A₀ A) p k)) := by
    rw [residueFiberTrans_fst]
    infer_instance
  exact IsAffineHom.of_comp _ (pullback.fst (baseMap A₀ A f₀ j k)
    (SubalgebraStages.residueSpecBase (subalgebras A₀ A) p k))

instance [IsProper f₀] (i : (FGSubalgebra A₀ A)ᵒᵖ) :
    CompactSpace ((residueFiberDiagram A₀ A f₀ j p).obj i) :=
  QuasiCompact.compactSpace_of_compactSpace
    (pullback.snd (baseMap A₀ A f₀ j i)
      (SubalgebraStages.residueSpecBase (subalgebras A₀ A) p i))

instance [IsProper f₀] (i : (FGSubalgebra A₀ A)ᵒᵖ) :
    QuasiSeparatedSpace ((residueFiberDiagram A₀ A f₀ j p).obj i) :=
  quasiSeparatedSpace_of_quasiSeparated
    (pullback.snd (baseMap A₀ A f₀ j i)
      (SubalgebraStages.residueSpecBase (subalgebras A₀ A) p i))

open AlgebraicCurves.Geometry.Schemes.Proofs.SubalgebraStages_nonempty_isLimit_cone in
open SubalgebraStages in
/-- The original residue fiber is the limit of the actual contracted residue fibers. -/
def residueFiberConeIsLimit [IsProper f₀] [IsClosedImmersion j] :
    IsLimit (residueFiberCone A₀ A f₀ j p) := by
  let hX : IsLimit (cone A₀ A f₀ j) := coneIsLimit A₀ A f₀ j
  let hK : IsLimit (residueSpecCone (subalgebras A₀ A) p) :=
    residueSpecConeIsLimit (subalgebras A₀ A) p (exhaustive A₀ A)
  let hB : IsLimit (specCone (subalgebras A₀ A)) :=
    (LimBC.nonempty_isLimit_specCone (subalgebras A₀ A) (exhaustive A₀ A)).some
  let leftCone : Cone (residueFiberDiagram A₀ A f₀ j p) → Cone (diagram A₀ A f₀ j) :=
    fun t => { pt := t.pt, π := t.π ≫ residueFiberFst A₀ A f₀ j p }
  let rightCone : Cone (residueFiberDiagram A₀ A f₀ j p) →
      Cone (residueSpecDiagram (subalgebras A₀ A) p) :=
    fun t => { pt := t.pt, π := t.π ≫ residueFiberSnd A₀ A f₀ j p }
  let leftLift : ∀ t : Cone (residueFiberDiagram A₀ A f₀ j p), t.pt ⟶ Z :=
    fun t => hX.lift (leftCone t)
  let rightLift : ∀ t : Cone (residueFiberDiagram A₀ A f₀ j p),
      t.pt ⟶ Spec (CommRingCat.of p.ResidueField) :=
    fun t => hK.lift (rightCone t)
  have hleft (t : Cone (residueFiberDiagram A₀ A f₀ j p))
      (i : (FGSubalgebra A₀ A)ᵒᵖ) :
      leftLift t ≫ (cone A₀ A f₀ j).π.app i = t.π.app i ≫
        pullback.fst (baseMap A₀ A f₀ j i) (residueSpecBase (subalgebras A₀ A) p i) :=
    hX.fac (leftCone t) i
  have hright (t : Cone (residueFiberDiagram A₀ A f₀ j p))
      (i : (FGSubalgebra A₀ A)ᵒᵖ) :
      rightLift t ≫ (residueSpecCone (subalgebras A₀ A) p).π.app i = t.π.app i ≫
        pullback.snd (baseMap A₀ A f₀ j i) (residueSpecBase (subalgebras A₀ A) p i) :=
    hK.fac (rightCone t) i
  have hbase (i : (FGSubalgebra A₀ A)ᵒᵖ) :
      (cone A₀ A f₀ j).π.app i ≫ baseMap A₀ A f₀ j i =
        originalBaseMap A₀ A f₀ j ≫ (specCone (subalgebras A₀ A)).π.app i := by
    simpa only [originalBaseMap, Category.assoc] using cone_projection_baseMap A₀ A f₀ j i
  have hcompat (t : Cone (residueFiberDiagram A₀ A f₀ j p)) :
      leftLift t ≫ originalBaseMap A₀ A f₀ j = rightLift t ≫ residueSpecBaseTop p := by
    apply hB.hom_ext
    intro i
    calc
      (leftLift t ≫ originalBaseMap A₀ A f₀ j) ≫
          (specCone (subalgebras A₀ A)).π.app i =
        leftLift t ≫ ((cone A₀ A f₀ j).π.app i ≫ baseMap A₀ A f₀ j i) := by
          rw [hbase, Category.assoc]
      _ = (t.π.app i ≫ pullback.fst _ _) ≫ baseMap A₀ A f₀ j i := by
          rw [← Category.assoc, hleft]
      _ = (t.π.app i ≫ pullback.snd _ _) ≫ residueSpecBase (subalgebras A₀ A) p i := by
          rw [Category.assoc, pullback.condition, ← Category.assoc]
      _ = rightLift t ≫ ((residueSpecCone (subalgebras A₀ A) p).π.app i ≫
          residueSpecBase (subalgebras A₀ A) p i) := by
          rw [← Category.assoc, hright]
      _ = (rightLift t ≫ residueSpecBaseTop p) ≫
          (specCone (subalgebras A₀ A)).π.app i := by
          rw [residueSpecCone_projection_base, Category.assoc]
  refine
    { lift := fun t => pullback.lift (leftLift t) (rightLift t) (hcompat t)
      fac := ?_
      uniq := ?_ }
  · intro t i
    change pullback.lift (leftLift t) (rightLift t) (hcompat t) ≫
      residueFiberLeg A₀ A f₀ j p i = t.π.app i
    apply pullback.hom_ext
    · rw [Category.assoc, residueFiberLeg_fst, pullback.lift_fst_assoc]
      exact hleft t i
    · rw [Category.assoc, residueFiberLeg_snd, pullback.lift_snd_assoc]
      exact hright t i
  · intro t m hm
    have hm' (i : (FGSubalgebra A₀ A)ᵒᵖ) :
        m ≫ residueFiberLeg A₀ A f₀ j p i = t.π.app i := hm i
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      apply hX.hom_ext
      intro i
      rw [Category.assoc, ← residueFiberLeg_fst, ← Category.assoc, hm', hleft]
    · rw [pullback.lift_snd]
      apply hK.hom_ext
      intro i
      rw [Category.assoc, ← residueFiberLeg_snd, ← Category.assoc, hm', hright]

end AlgebraicGeometry.NoetherianImageApproximation

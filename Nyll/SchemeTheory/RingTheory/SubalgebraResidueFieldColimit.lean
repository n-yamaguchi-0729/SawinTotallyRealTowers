/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Residue fields of exhaustive subalgebra stages

For an exhaustive directed family of subalgebras, contraction of one prime of the
ambient ring gives a diagram of actual residue fields. Its canonical cocone has
the ambient residue field as its colimit: every fraction has numerator and
denominator in a common stage, and every cocone leg is injective.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.SubalgebraStages

universe u

variable {A₀ A : Type u} [CommRing A₀] [CommRing A] [Algebra A₀ A]
variable {ι : Type u} [Preorder ι] (S : ι →o Subalgebra A₀ A)
variable (p : Ideal A) [p.IsPrime]

/-- The prime at a stage obtained by contracting the original ambient prime. -/
abbrev residuePrime (i : ι) : Ideal (S i) :=
  p.comap (S i).val.toRingHom

/-- The map on actual residue fields induced by a stage inclusion. -/
def residueTrans {i j : ι} (h : i ≤ j) :
    (residuePrime S p i).ResidueField →+* (residuePrime S p j).ResidueField :=
  Ideal.ResidueField.map (residuePrime S p i) (residuePrime S p j)
    (Subalgebra.inclusion (S.mono h)).toRingHom (Ideal.ext fun _ => Iff.rfl)

/-- The actual residue-field embedding induced by inclusion in the ambient ring. -/
def residueLeg (i : ι) : (residuePrime S p i).ResidueField →+* p.ResidueField :=
  Ideal.ResidueField.map (residuePrime S p i) p (S i).val.toRingHom rfl

@[simp]
lemma residueTrans_algebraMap {i j : ι} (h : i ≤ j) (a : S i) :
    residueTrans S p h (algebraMap (S i) (residuePrime S p i).ResidueField a) =
      algebraMap (S j) (residuePrime S p j).ResidueField
        (Subalgebra.inclusion (S.mono h) a) :=
  Ideal.ResidueField.map_algebraMap _ _ _ _ a

@[simp]
lemma residueLeg_algebraMap (i : ι) (a : S i) :
    residueLeg S p i (algebraMap (S i) (residuePrime S p i).ResidueField a) =
      algebraMap A p.ResidueField (a : A) :=
  Ideal.ResidueField.map_algebraMap _ _ _ _ a

/-- Each stage residue field embeds in the original residue field. -/
theorem residueLeg_injective (i : ι) : Function.Injective (residueLeg S p i) :=
  RingHom.injective (residueLeg S p i)

@[simp]
lemma residueTrans_refl (i : ι) : residueTrans S p (le_refl i) = RingHom.id _ := by
  apply Ideal.ResidueField.ringHom_ext
  ext a
  simp only [RingHom.comp_apply, residueTrans_algebraMap, RingHom.id_apply]
  rfl

lemma residueTrans_comp {i j k : ι} (h : i ≤ j) (h' : j ≤ k) :
    (residueTrans S p h').comp (residueTrans S p h) = residueTrans S p (h.trans h') := by
  apply Ideal.ResidueField.ringHom_ext
  ext a
  simp only [RingHom.comp_apply, residueTrans_algebraMap]
  rfl

lemma residueLeg_trans {i j : ι} (h : i ≤ j) :
    (residueLeg S p j).comp (residueTrans S p h) = residueLeg S p i := by
  apply Ideal.ResidueField.ringHom_ext
  ext a
  simp only [RingHom.comp_apply, residueTrans_algebraMap, residueLeg_algebraMap]
  rfl

/-- The diagram of the actual residue fields at the contracted stage primes. -/
@[reducible] def residueDiagram : ι ⥤ CommRingCat.{u} where
  obj i := CommRingCat.of (residuePrime S p i).ResidueField
  map h := CommRingCat.ofHom (residueTrans S p h.le)
  map_id i := CommRingCat.hom_ext (residueTrans_refl S p i)
  map_comp h h' := CommRingCat.hom_ext (residueTrans_comp S p h.le h'.le).symm

/-- The cocone of actual residue-field embeddings with vertex the ambient residue field. -/
@[reducible] def residueCocone : Cocone (residueDiagram S p) where
  pt := CommRingCat.of p.ResidueField
  ι :=
    { app i := CommRingCat.ofHom (residueLeg S p i)
      naturality i j h := by
        apply CommRingCat.hom_ext
        exact residueLeg_trans S p h.le }

/-- A residue-field fraction is represented at a stage containing its numerator and denominator. -/
theorem exists_residueLeg_eq [IsDirected ι (· ≤ ·)]
    (hS : ∀ a : A, ∃ i, a ∈ S i) (x : p.ResidueField) :
    ∃ (i : ι) (y : (residuePrime S p i).ResidueField), residueLeg S p i y = x := by
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A ⧸ p) x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨i, hi⟩ := hS a
  obtain ⟨j, hj⟩ := hS b
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  refine ⟨k, algebraMap (S k) (residuePrime S p k).ResidueField ⟨a, S.mono hik hi⟩ /
    algebraMap (S k) (residuePrime S p k).ResidueField ⟨b, S.mono hjk hj⟩, ?_⟩
  simp only [map_div₀, residueLeg_algebraMap, Ideal.algebraMap_quotient_residueField_mk]

/-- The actual ambient residue field is the colimit of the contracted stage residue fields. -/
def residueCoconeIsColimit [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (hS : ∀ a : A, ∃ i, a ∈ S i) : IsColimit (residueCocone S p) := by
  have : ReflectsColimit (residueDiagram S p) (CategoryTheory.forget CommRingCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  apply isColimitOfReflects (CategoryTheory.forget CommRingCat.{u})
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro x
    obtain ⟨i, y, hy⟩ := exists_residueLeg_eq S p hS x
    exact ⟨i, y, hy.symm⟩
  · intro i j
    rintro (x : (residuePrime S p i).ResidueField)
      (y : (residuePrime S p j).ResidueField)
      (hxy : residueLeg S p i x = residueLeg S p j y)
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    refine ⟨k, homOfLE hik, homOfLE hjk, ?_⟩
    apply residueLeg_injective S p k
    change residueLeg S p k (residueTrans S p hik x) =
      residueLeg S p k (residueTrans S p hjk y)
    rw [← RingHom.comp_apply, residueLeg_trans, ← RingHom.comp_apply, residueLeg_trans]
    exact hxy

end AlgebraicGeometry.SubalgebraStages

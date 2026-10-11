/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Affine.WeilRestriction.InternalHom
public import Nyll.SchemeTheory.WeilRestriction.Sheaf
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

/-!
# Affine Weil restriction on arbitrary test schemes

For finite free `A/R` and finitely presented `B/R`, the algebraic Weil
restriction represents the relative internal Hom on every scheme over `Spec R`.
The proof extends the affine comparison along the cover-dense affine subsite.
The final representing object is the spectrum of the explicit representing algebra.

This is the finite-free affine-base step towards Stacks Project, Tag 0BL7.
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open AlgebraicGeometry

universe u

noncomputable section

namespace SchemeTheory.Affine

/-- Affine schemes over an affine base cover every object of its big Zariski site. -/
instance affineForgetCoverDense (R : CommRingCat.{u}) :
    (affineForget R).IsCoverDense (Scheme.zariskiTopology.over (Spec R)) where
  is_cover T := by
    rw [GrothendieckTopology.mem_over_iff]
    refine Scheme.zariskiTopology.superset_covering ?_
      T.left.affineCover.mem_grothendieckTopology
    rw [Sieve.generate_le_iff]
    intro X f hf
    obtain ⟨i⟩ := hf
    rw [Sieve.overEquiv_iff]
    have h : IsAffineHom (T.left.affineCover.f i ≫ T.hom) :=
      isAffineHom_of_isAffine (T.left.affineCover.f i ≫ T.hom)
    let Y : affineHomProperty.Over ⊤ (Spec R) :=
      MorphismProperty.Over.mk ⊤ (T.left.affineCover.f i ≫ T.hom) h
    let g : (affineForget R).obj Y ⟶ T := Over.homMk (T.left.affineCover.f i)
    change Nonempty (Presieve.CoverByImageStructure (affineForget R) _)
    refine ⟨⟨Y, 𝟙 _, g, ?_⟩⟩
    ext
    rfl

/-- Restricting the Yoneda presheaf of an affine object gives its affine Yoneda presheaf. -/
def affineForgetYonedaIso (R : CommRingCat.{u})
    (X : affineHomProperty.Over ⊤ (Spec R)) :
    (affineForget R).op ⋙ yoneda.obj ((affineForget R).obj X) ≅ yoneda.obj X := by
  let ff : (affineForget R).FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful (affineForget R)
  exact NatIso.ofComponents
    (fun _ ↦ ff.homEquiv.symm.toIso)
    (fun f ↦ by
      ext g
      change ff.preimage ((affineForget R).map f.unop ≫ g) =
        f.unop ≫ ff.preimage g
      rw [ff.preimage_comp, ff.preimage_map])

section FiniteFree

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Module.Free R A] [Module.Finite R A]
  [Algebra.FinitePresentation R B]

/-- The relative internal Hom on all schemes over `Spec R`. -/
abbrev globalInternalHomFunctor :
    (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type u :=
  (MonoidalCategory.tensorRight (specAOver (R := R) (A := A))).op ⋙
    yoneda.obj (specBOver (R := R) (B := B))

/-- The affine representer viewed in the category of all schemes over `Spec R`. -/
abbrev globalInternalHomRepresenter : Over (Spec (CommRingCat.of R)) :=
  (affineForget (CommRingCat.of R)).obj
    (affineInternalHomRepresenter (R := R) (A := A) (B := B))

/-- The opposite affine fibre-product functor is the composite of the opposite forgetful and
fibre-product functors. -/
def affineActualProductOpIso :
    (affineActualProductFunctor (R := R) (A := A)).op ≅
      (affineForget (CommRingCat.of R)).op ⋙
        (MonoidalCategory.tensorRight (specAOver (R := R) (A := A))).op :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- The affine internal-Hom functor is the restriction of the global internal-Hom functor to
affine test schemes. -/
def affineInternalHomRestrictionIso :
    affineInternalHomFunctor (R := R) (A := A) (B := B) ≅
      (affineForget (CommRingCat.of R)).op ⋙
        globalInternalHomFunctor (R := R) (A := A) (B := B) :=
  (Functor.isoWhiskerRight
    (affineActualProductOpIso (R := R) (A := A)) _).trans
      (Functor.associator _ _ _)

/-- The global internal-Hom representation restricts to its natural representation on affine
test schemes. -/
def restrictedGlobalInternalHomIso :
    (affineForget (CommRingCat.of R)).op ⋙
        yoneda.obj (globalInternalHomRepresenter (R := R) (A := A) (B := B)) ≅
      (affineForget (CommRingCat.of R)).op ⋙
        globalInternalHomFunctor (R := R) (A := A) (B := B) :=
  (affineForgetYonedaIso (CommRingCat.of R)
      (affineInternalHomRepresenter (R := R) (A := A) (B := B))).trans <|
    (affineInternalHomRepresentable (R := R) (A := A) (B := B)).toIso.trans <|
      affineInternalHomRestrictionIso (R := R) (A := A) (B := B)

/-- The affine representer represents the internal Hom on arbitrary test schemes. -/
def globalInternalHomRepresentable :
    (globalInternalHomFunctor (R := R) (A := A) (B := B)).RepresentableBy
      (globalInternalHomRepresenter (R := R) (A := A) (B := B)) := by
  let K : GrothendieckTopology (Over (Spec (CommRingCat.of R))) :=
    Scheme.zariskiTopology.over (Spec (CommRingCat.of R))
  have hW : Presheaf.IsSheaf K
      (yoneda.obj (globalInternalHomRepresenter (R := R) (A := A) (B := B))) := by
    rw [isSheaf_iff_isSheaf_of_type]
    exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  have hF : Presheaf.IsSheaf K
      (globalInternalHomFunctor (R := R) (A := A) (B := B)) :=
    SchemeTheory.WeilRestriction.relativeInternalHom_isSheaf Scheme.zariskiTopology
      (specAOver (R := R) (A := A)) (specBOver (R := R) (B := B))
  let e : yoneda.obj (globalInternalHomRepresenter (R := R) (A := A) (B := B)) ≅
      globalInternalHomFunctor (R := R) (A := A) (B := B) :=
    Functor.IsCoverDense.presheafIso
      (G := affineForget (CommRingCat.of R)) (K := K)
      (ℱ := ⟨_, hW⟩) (ℱ' := ⟨_, hF⟩)
      (restrictedGlobalInternalHomIso (R := R) (A := A) (B := B))
  exact Functor.representableByEquiv.symm e

/-- The spectrum of the algebraic Weil restriction, with its structure map to `Spec R`. -/
abbrev globalInternalHomSpecRepresenter : Over (Spec (CommRingCat.of R)) :=
  (specOverFunctor (CommRingCat.of R)).obj
    (Opposite.op (algebraRepresenter (R := R) (A := A) (B := B)))

/-- Identify the affine-category construction with the explicit spectrum. -/
def globalInternalHomRepresenterIsoSpec :
    globalInternalHomRepresenter (R := R) (A := A) (B := B) ≅
      globalInternalHomSpecRepresenter (R := R) (A := A) (B := B) :=
  ((affineToSpecGammaIso (CommRingCat.of R)).app
    (affineInternalHomRepresenter (R := R) (A := A) (B := B))).trans <|
      (specOverFunctor (CommRingCat.of R)).mapIso
        ((affineAlgebraEquiv (CommRingCat.of R)).counitIso.app
          (algebraRepresenter (R := R) (A := A) (B := B))).symm.op

/-- The explicit spectrum represents the relative internal Hom on all test schemes. -/
def globalInternalHomSpecRepresentable :
    (globalInternalHomFunctor (R := R) (A := A) (B := B)).RepresentableBy
      (globalInternalHomSpecRepresenter (R := R) (A := A) (B := B)) :=
  (globalInternalHomRepresentable (R := R) (A := A) (B := B)).ofIsoObj
    (globalInternalHomRepresenterIsoSpec (R := R) (A := A) (B := B)).symm

end FiniteFree

end SchemeTheory.Affine

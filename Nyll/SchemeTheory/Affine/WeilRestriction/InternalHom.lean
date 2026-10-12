/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Affine.WeilRestriction.FiniteEtale
public import Nyll.SchemeTheory.Pi1.Affine.Property
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Affine internal Homs over an affine base

This file promotes the algebraic affine Weil restriction from
`SchemeTheory.Affine.WeilRestriction.Basic` to the corresponding geometric
representability statement for affine schemes over `Spec R`.

For finite free `A/R` and finitely presented `B/R`, the functor sending an
affine `T` over `Spec R` to morphisms over `Spec R`
`T x_{Spec R} Spec A -> Spec B` is representable by the affine scheme
associated to `CommAlgCat.affineWeilRestriction`.
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open AlgebraicGeometry
open scoped TensorProduct

noncomputable section

universe u u₁ u₂ v₁ v₂ w

namespace SchemeTheory.Affine

/-- The ring-homomorphism property satisfied by every homomorphism. -/
def allRingHom
    {R S : Type u} [CommRing R] [CommRing S] (_ : R →+* S) : Prop := True

lemma allRingHom_respectsIso : RingHom.RespectsIso (@allRingHom.{u}) := by
  constructor <;> intros <;> trivial

lemma allRingHom_localizationAwayPreserves :
    RingHom.LocalizationAwayPreserves (@allRingHom.{u}) := by
  simp [RingHom.LocalizationAwayPreserves, allRingHom]

lemma allRingHom_ofLocalizationSpan :
    RingHom.OfLocalizationSpan (@allRingHom.{u}) := by
  simp [RingHom.OfLocalizationSpan, allRingHom]

/-- The morphism property selecting affine morphisms of schemes. -/
abbrev affineHomProperty : MorphismProperty Scheme.{u} := @IsAffineHom

local instance : HasAffineProperty (affineHomProperty : MorphismProperty Scheme.{u})
    (affineAnd (@allRingHom.{u})) :=
  (HasAffineProperty.affineAnd_iff _ allRingHom_respectsIso
    allRingHom_localizationAwayPreserves allRingHom_ofLocalizationSpan).2 (by
      intro X Y f
      simp [affineHomProperty, allRingHom])

/-- View a ring under R in the under-category restricted by the universal ring-homomorphism
property. -/
def allUnderInverse (R : CommRingCat.{u}) :
    Under R ⥤ (RingHom.toMorphismProperty (@allRingHom.{u})).Under ⊤ R :=
  MorphismProperty.Comma.lift (𝟭 (Under R)) (fun _ ↦ trivial)
    (fun _ ↦ trivial) (fun _ ↦ trivial)

/-- The restricted under-category for the universal ring-homomorphism property is equivalent to
the category of rings under R. -/
def allUnderEquiv (R : CommRingCat.{u}) :
    (RingHom.toMorphismProperty (@allRingHom.{u})).Under ⊤ R ≌ Under R :=
  CategoryTheory.Equivalence.mk
    (MorphismProperty.Under.forget _ ⊤ R)
    (allUnderInverse R)
    (NatIso.ofComponents
      (fun X ↦ MorphismProperty.Under.isoMk (Iso.refl X.right))
      (fun f ↦ by ext; rfl))
    (Iso.refl _)

/-- Affine schemes over Spec R, with arrows reversed, are equivalent to commutative R-algebras. -/
def affineAlgebraEquiv (R : CommRingCat.{u}) :
    (affineHomProperty.Over ⊤ (Spec R))ᵒᵖ ≌
      CommAlgCat.{u} R :=
  (AffineAnd.overSpecEquivUnder affineHomProperty
      allRingHom_respectsIso R).trans
    ((allUnderEquiv R).trans (commAlgCatEquivUnder R).symm)

/-- The spectrum functor from commutative R-algebras, with arrows reversed, to schemes over
Spec R. -/
def specOverFunctor (R : CommRingCat.{u}) :
    (CommAlgCat.{u} R)ᵒᵖ ⥤ Over (Spec R) :=
  (commAlgCatEquivUnder R).op.functor ⋙
    (CategoryTheory.Over.opEquivOpUnder R).inverse ⋙
    AlgebraicGeometry.Over.Spec R

/-- The spectrum functor on commutative R-algebras is fully faithful over Spec R. -/
def specOverFunctorFullyFaithful (R : CommRingCat.{u}) :
    (specOverFunctor R).FullyFaithful :=
  (commAlgCatEquivUnder R).op.fullyFaithfulFunctor.comp
    ((CategoryTheory.Over.opEquivOpUnder R).symm.fullyFaithfulFunctor.comp
      (AlgebraicGeometry.Spec.fullyFaithful.over (Opposite.op R)))

/-- Forget that the source of a scheme over Spec R is affine. -/
abbrev affineForget (R : CommRingCat.{u}) :
    affineHomProperty.Over ⊤ (Spec R) ⥤ Over (Spec R) :=
  MorphismProperty.Over.forget affineHomProperty ⊤ (Spec R)

/-- Send an affine scheme over Spec R to the spectrum of its global-sections R-algebra. -/
abbrev affineSpecGamma (R : CommRingCat.{u}) :
    affineHomProperty.Over ⊤ (Spec R) ⥤ Over (Spec R) :=
  (affineAlgebraEquiv R).functor.rightOp ⋙ specOverFunctor R

/-- Every affine scheme over Spec R is naturally isomorphic, over Spec R, to the spectrum of
its global sections. -/
def affineToSpecGammaIso (R : CommRingCat.{u}) :
    affineForget R ≅ affineSpecGamma R :=
  NatIso.ofComponents
    (fun T ↦
      let : IsAffine T.left :=
        @isAffine_of_isAffineHom T.left (Spec R) T.hom T.prop inferInstance
      letI : IsAffine ((affineForget R).obj T).left := inferInstanceAs (IsAffine T.left)
      Over.isoMk T.left.isoSpec (by
      apply Scheme.Hom.appTop_bijective_of_isAffine.injective
      change (Spec.map (CommRingCat.ofHom (algebraMap R
        ((affineAlgebraEquiv R).functor.obj (Opposite.op T) : Type u)))).appTop ≫
          T.left.isoSpec.hom.appTop = T.hom.appTop
      change (Spec.map ((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop)).appTop ≫
          T.left.isoSpec.hom.appTop = T.hom.appTop
      simp only [Scheme.isoSpec, asIso_hom, Scheme.toSpecΓ_appTop]
      change (Spec.map ((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop)).appTop ≫
          (Scheme.ΓSpecIso Γ((𝟭 Scheme).obj T.left, ⊤)).hom = T.hom.appTop
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
        Scheme.ΓSpecIso_naturality ((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop)))
    (fun {T U} f ↦ by
      let : IsAffine T.left :=
        @isAffine_of_isAffineHom T.left (Spec R) T.hom T.prop inferInstance
      let : IsAffine U.left :=
        @isAffine_of_isAffineHom U.left (Spec R) U.hom U.prop inferInstance
      ext
      change f.left ≫ U.left.isoSpec.hom =
        T.left.isoSpec.hom ≫ Spec.map f.left.appTop
      exact (Scheme.isoSpec_hom_naturality f.left).symm)

/-- Taking spectra identifies tensoring R-algebras with A with fibre products by Spec A over
Spec R. -/
def specTensorIso
    (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] :
    (MonoidalCategory.tensorRight (CommAlgCat.of R A)).op ⋙
        specOverFunctor (CommRingCat.of R) ≅
      specOverFunctor (CommRingCat.of R) ⋙
        MonoidalCategory.tensorRight
          ((specOverFunctor (CommRingCat.of R)).obj
            (Opposite.op (CommAlgCat.of R A))) :=
  NatIso.ofComponents
    (fun C ↦ Over.isoMk (pullbackSpecIso R C.unop A).symm (by
      change (pullbackSpecIso R C.unop A).inv ≫
          (pullback.fst
            (Spec.map (CommRingCat.ofHom (algebraMap R C.unop)))
            (Spec.map (CommRingCat.ofHom (algebraMap R A))) ≫
              Spec.map (CommRingCat.ofHom (algebraMap R C.unop))) =
        Spec.map (CommRingCat.ofHom (algebraMap R (C.unop ⊗[R] A)))
      rw [← Category.assoc, pullbackSpecIso_inv_fst]
      rw [← Spec.map_comp]
      congr 1))
    (fun {C D} f ↦ by
      ext
      change Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.map f.unop.hom (AlgHom.id R A))) ≫
          (pullbackSpecIso R D.unop A).inv =
        (pullbackSpecIso R C.unop A).inv ≫
          pullback.lift
            (pullback.fst
                (Spec.map (CommRingCat.ofHom (algebraMap R C.unop)))
                (Spec.map (CommRingCat.ofHom (algebraMap R A))) ≫
              Spec.map (CommRingCat.ofHom f.unop.hom))
            (pullback.snd
              (Spec.map (CommRingCat.ofHom (algebraMap R C.unop)))
              (Spec.map (CommRingCat.ofHom (algebraMap R A)))) (by
                rw [Category.assoc, ← Spec.map_comp]
                convert pullback.condition using 1
                congr 1
                congr 1
                ext x
                simp)
      apply pullback.hom_ext
      · rw [Category.assoc, pullbackSpecIso_inv_fst]
        rw [Category.assoc, pullback.lift_fst]
        rw [← Category.assoc, pullbackSpecIso_inv_fst]
        rw [← Spec.map_comp, ← Spec.map_comp]
        congr 1
      · rw [Category.assoc, pullbackSpecIso_inv_snd]
        rw [Category.assoc, pullback.lift_snd]
        rw [pullbackSpecIso_inv_snd]
        rw [← Spec.map_comp]
        congr 1
        ext x
        simp)

/-- Transport a corepresentation of a functor through an equivalence of its source category. -/
def corepresentableByCompEquivalence
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (E : C ≌ D) {F : D ⥤ Type w} {H : D} (r : F.CorepresentableBy H) :
    (E.functor ⋙ F).CorepresentableBy (E.inverse.obj H) where
  homEquiv {Y} :=
    (E.symm.toAdjunction.homEquiv H Y).trans r.homEquiv
  homEquiv_comp {Y Y'} g f := by
    change r.homEquiv (E.symm.toAdjunction.homEquiv H Y' (f ≫ g)) = _
    rw [E.symm.toAdjunction.homEquiv_naturality_right]
    exact r.homEquiv_comp _ _

/-- A corepresentation on the opposite category gives a representation of the corresponding
presheaf. -/
def representableByOfCorepresentableOp
    {C : Type u₁} [Category.{v₁} C] {F : Cᵒᵖ ⥤ Type w} {W : Cᵒᵖ}
    (r : F.CorepresentableBy W) : F.RepresentableBy W.unop where
  homEquiv {X} := (opEquiv W (Opposite.op X)).symm.trans r.homEquiv
  homEquiv_comp {X X'} f g := by
    change r.homEquiv ((f ≫ g).op) = F.map f.op (r.homEquiv g.op)
    exact r.homEquiv_comp f.op g.op

lemma map_op_comp
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (F : Cᵒᵖ ⥤ D) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map (f ≫ g).op = F.map g.op ≫ F.map f.op := by
  rw [← F.map_comp]
  rfl

section Weil

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Module.Free R A] [Module.Finite R A]
  [Algebra.FinitePresentation R B]

/-- The functor tensoring commutative R-algebras on the right with A. -/
abbrev tensorRightAlg : CommAlgCat.{u} R ⥤ CommAlgCat.{u} R :=
  MonoidalCategory.tensorRight (CommAlgCat.of R A)

/-- The functor sending an R-algebra C to R-algebra homomorphisms from B to C tensor A. -/
abbrev algebraHomFunctor : CommAlgCat.{u} R ⥤ Type u :=
  tensorRightAlg (R := R) (A := A) ⋙
    coyoneda.obj (Opposite.op (CommAlgCat.of R B))

/-- The finitely presented algebra B as an object where the partial left adjoint to tensoring
with A is defined. -/
def algebraTargetSource :
    (tensorRightAlg (R := R) (A := A)).PartialLeftAdjointSource :=
  ⟨CommAlgCat.of R B, CommAlgCat.tensorRight_leftAdjointObjIsDefined⟩

/-- The R-algebra corepresenting homomorphisms from B to tensor products with A. -/
abbrev algebraRepresenter : CommAlgCat.{u} R :=
  (tensorRightAlg (R := R) (A := A)).partialLeftAdjointObj
    (algebraTargetSource (R := R) (A := A) (B := B))

/-- The partial left adjoint to tensoring with A corepresents the algebra-homomorphism functor
for B. -/
def algebraCorepresentableBy :
    (algebraHomFunctor (R := R) (A := A) (B := B)).CorepresentableBy
      (algebraRepresenter (R := R) (A := A) (B := B)) :=
  { homEquiv :=
      (tensorRightAlg (R := R) (A := A)).partialLeftAdjointHomEquiv
    homEquiv_comp := fun g f ↦
      (tensorRightAlg (R := R) (A := A)).partialLeftAdjointHomEquiv_comp f g }

/-- The algebra-homomorphism functor for B and tensoring with A, viewed on affine test schemes
over Spec R. -/
abbrev affineTransportedFunctor :
    (affineHomProperty.Over ⊤ (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type u :=
  (affineAlgebraEquiv (CommRingCat.of R)).functor ⋙
    algebraHomFunctor (R := R) (A := A) (B := B)

/-- The affine scheme over Spec R corresponding to the algebraic corepresenter. -/
abbrev affineTransportedRepresenter :
    affineHomProperty.Over ⊤ (Spec (CommRingCat.of R)) :=
  ((affineAlgebraEquiv (CommRingCat.of R)).inverse.obj
    (algebraRepresenter (R := R) (A := A) (B := B))).unop

/-- The affine scheme obtained from the algebraic corepresenter represents the transported
affine functor. -/
def affineTransportedRepresentable :
    (affineTransportedFunctor (R := R) (A := A) (B := B)).RepresentableBy
      (affineTransportedRepresenter (R := R) (A := A) (B := B)) :=
  representableByOfCorepresentableOp <|
    corepresentableByCompEquivalence (affineAlgebraEquiv (CommRingCat.of R))
      (algebraCorepresentableBy (R := R) (A := A) (B := B))

/-- Spec A with its structural morphism to Spec R. -/
abbrev specAOver :
    Over (Spec (CommRingCat.of R)) :=
  (specOverFunctor (CommRingCat.of R)).obj
    (Opposite.op (CommAlgCat.of R A))

/-- Spec B with its structural morphism to Spec R. -/
abbrev specBOver :
    Over (Spec (CommRingCat.of R)) :=
  (specOverFunctor (CommRingCat.of R)).obj
    (Opposite.op (CommAlgCat.of R B))

/-- The functor taking the fibre product of an affine test scheme with Spec A over Spec R. -/
abbrev affineActualProductFunctor :
    affineHomProperty.Over ⊤ (Spec (CommRingCat.of R)) ⥤
      Over (Spec (CommRingCat.of R)) :=
  affineForget (CommRingCat.of R) ⋙
    MonoidalCategory.tensorRight (specAOver (R := R) (A := A))

/-- The functor taking the spectrum of the global-sections R-algebra of an affine test scheme
tensored with A. -/
abbrev affineTensorSpecFunctor :
    affineHomProperty.Over ⊤ (Spec (CommRingCat.of R)) ⥤
      Over (Spec (CommRingCat.of R)) :=
  (affineAlgebraEquiv (CommRingCat.of R)).functor.rightOp ⋙
    (tensorRightAlg (R := R) (A := A)).op ⋙
    specOverFunctor (CommRingCat.of R)

/-- The fibre product of an affine test scheme with Spec A is naturally isomorphic to the
spectrum of its global sections tensored with A. -/
def affineProductSpecIso :
    affineActualProductFunctor (R := R) (A := A) ≅
      affineTensorSpecFunctor (R := R) (A := A) :=
  (Functor.isoWhiskerRight
      (affineToSpecGammaIso (CommRingCat.of R))
      (MonoidalCategory.tensorRight (specAOver (R := R) (A := A)))).trans <|
    (Functor.associator
      (affineAlgebraEquiv (CommRingCat.of R)).functor.rightOp
      (specOverFunctor (CommRingCat.of R))
      (MonoidalCategory.tensorRight (specAOver (R := R) (A := A)))).trans <|
    (Functor.isoWhiskerLeft
      (affineAlgebraEquiv (CommRingCat.of R)).functor.rightOp
      (specTensorIso R A).symm).trans <|
    (Functor.associator
      (affineAlgebraEquiv (CommRingCat.of R)).functor.rightOp
      (tensorRightAlg (R := R) (A := A)).op
      (specOverFunctor (CommRingCat.of R))).symm

/-- The geometric affine internal Hom functor over `Spec R`.

On an affine `T` over `Spec R`, this is the set of morphisms over `Spec R`
from `T x_{Spec R} Spec A` to `Spec B`.
-/
abbrev affineInternalHomFunctor :
    (affineHomProperty.Over ⊤ (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type u :=
  (affineActualProductFunctor (R := R) (A := A)).op ⋙
    yoneda.obj (specBOver (R := R) (B := B))

/-- The affine scheme over `Spec R` representing `affineInternalHomFunctor`. -/
abbrev affineInternalHomRepresenter :
    affineHomProperty.Over ⊤ (Spec (CommRingCat.of R)) :=
  affineTransportedRepresenter (R := R) (A := A) (B := B)

/-- For an affine test scheme T, algebra homomorphisms from B to its global sections tensored
with A correspond to morphisms from T fibre-product Spec A to Spec B over Spec R. -/
def transportedGeometricEquiv
    (T : (affineHomProperty.Over ⊤ (Spec (CommRingCat.of R)))ᵒᵖ) :
    (affineTransportedFunctor (R := R) (A := A) (B := B)).obj T ≃
      (affineInternalHomFunctor (R := R) (A := A) (B := B)).obj T := by
  let e :
      (affineActualProductFunctor (R := R) (A := A)).obj T.unop ≅
        (specOverFunctor (CommRingCat.of R)).obj
          (Opposite.op <| (tensorRightAlg (R := R) (A := A)).obj
            ((affineAlgebraEquiv (CommRingCat.of R)).functor.obj T)) :=
    (affineProductSpecIso (R := R) (A := A)).app T.unop
  let ff := specOverFunctorFullyFaithful (CommRingCat.of R)
  exact
  { toFun := fun g ↦ e.hom ≫
        (specOverFunctor (CommRingCat.of R)).map g.op
    invFun := fun h ↦ (ff.preimage (e.inv ≫ h)).unop
    left_inv := fun g ↦ by
      apply Quiver.Hom.op_inj
      change ff.preimage (e.inv ≫ e.hom ≫
        (specOverFunctor (CommRingCat.of R)).map g.op) = g.op
      rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      exact ff.preimage_map g.op
    right_inv := fun h ↦ by
      change e.hom ≫ (specOverFunctor (CommRingCat.of R)).map
        (ff.preimage (e.inv ≫ h)) = h
      rw [ff.map_preimage]
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp] }

omit [Module.Free R A] [Module.Finite R A] [Algebra.FinitePresentation R B] in
lemma transportedGeometricEquiv_apply
    (T : (affineHomProperty.Over ⊤ (Spec (CommRingCat.of R)))ᵒᵖ)
    (g : (affineTransportedFunctor (R := R) (A := A) (B := B)).obj T) :
    transportedGeometricEquiv (R := R) (A := A) (B := B) T g =
      (affineProductSpecIso (R := R) (A := A)).hom.app T.unop ≫
        (specOverFunctor (CommRingCat.of R)).map g.op := rfl

omit [Module.Free R A] [Module.Finite R A] [Algebra.FinitePresentation R B] in
lemma affineTransportedFunctor_map_apply
    {T U : (affineHomProperty.Over ⊤ (Spec (CommRingCat.of R)))ᵒᵖ}
    (f : T ⟶ U)
    (g : (affineTransportedFunctor (R := R) (A := A) (B := B)).obj T) :
    (affineTransportedFunctor (R := R) (A := A) (B := B)).map f g =
      g ≫ (tensorRightAlg (R := R) (A := A)).map
        ((affineAlgebraEquiv (CommRingCat.of R)).functor.map f) := rfl

omit [Module.Free R A] [Module.Finite R A] [Algebra.FinitePresentation R B] in
lemma affineInternalHomFunctor_map_apply
    {T U : (affineHomProperty.Over ⊤ (Spec (CommRingCat.of R)))ᵒᵖ}
    (f : T ⟶ U)
    (g : (affineInternalHomFunctor (R := R) (A := A) (B := B)).obj T) :
    (affineInternalHomFunctor (R := R) (A := A) (B := B)).map f g =
      (affineActualProductFunctor (R := R) (A := A)).map f.unop ≫ g := rfl

/-- The algebraic and geometric affine internal-Hom functors are naturally isomorphic. -/
def affineTransportedGeometricIso :
    affineTransportedFunctor (R := R) (A := A) (B := B) ≅
      affineInternalHomFunctor (R := R) (A := A) (B := B) :=
  NatIso.ofComponents
    (fun T ↦ (transportedGeometricEquiv (R := R) (A := A) (B := B) T).toIso)
    (fun {T U} f ↦ by
      ext g
      change transportedGeometricEquiv (R := R) (A := A) (B := B) U
          ((affineTransportedFunctor (R := R) (A := A) (B := B)).map f g) =
        (affineInternalHomFunctor (R := R) (A := A) (B := B)).map f
          (transportedGeometricEquiv (R := R) (A := A) (B := B) T g)
      rw [transportedGeometricEquiv_apply, transportedGeometricEquiv_apply]
      rw [affineTransportedFunctor_map_apply,
        affineInternalHomFunctor_map_apply]
      change
        (affineProductSpecIso (R := R) (A := A)).hom.app U.unop ≫
            (specOverFunctor (CommRingCat.of R)).map
              (((tensorRightAlg (R := R) (A := A)).map
                  ((affineAlgebraEquiv (CommRingCat.of R)).functor.map f)).op ≫ g.op) =
          (affineActualProductFunctor (R := R) (A := A)).map f.unop ≫
            (affineProductSpecIso (R := R) (A := A)).hom.app T.unop ≫
              (specOverFunctor (CommRingCat.of R)).map g.op
      rw [Functor.map_comp]
      change
        (affineProductSpecIso (R := R) (A := A)).hom.app U.unop ≫
            (affineTensorSpecFunctor (R := R) (A := A)).map f.unop ≫
              (specOverFunctor (CommRingCat.of R)).map g.op =
          (affineActualProductFunctor (R := R) (A := A)).map f.unop ≫
            (affineProductSpecIso (R := R) (A := A)).hom.app T.unop ≫
              (specOverFunctor (CommRingCat.of R)).map g.op
      rw [← (affineProductSpecIso (R := R) (A := A)).hom.naturality_assoc])

/-- The affine internal Hom functor is represented by the affine scheme
associated to `CommAlgCat.affineWeilRestriction`. -/
def affineInternalHomRepresentable :
    (affineInternalHomFunctor (R := R) (A := A) (B := B)).RepresentableBy
      (affineInternalHomRepresenter (R := R) (A := A) (B := B)) :=
  (affineTransportedRepresentable (R := R) (A := A) (B := B)).ofIso
    (affineTransportedGeometricIso (R := R) (A := A) (B := B))

end Weil

end SchemeTheory.Affine

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Affine.WeilRestriction.Basic
public import Mathlib.RingTheory.Etale.Descent
public import Mathlib.RingTheory.Etale.Finite
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.TotallySplit

/-!
# Finite étale affine Weil restriction

This file proves that the affine corepresenter constructed in
`SchemeTheory.Affine.WeilRestriction.Basic` is compatible with arbitrary
base change and is finite étale when both input algebras are finite étale.

These are the affine algebra ingredients for Stacks Project, Tag `0BL7`.
-/


@[expose] public section

open scoped TensorProduct

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

universe u

namespace CommAlgCat

variable {R : Type u} [CommRing R]

private def tensorPower (B : CommAlgCat.{u} R) : ℕ → CommAlgCat.{u} R
  | 0 => of R R
  | n + 1 => B ⊗ tensorPower B n

private def binaryHomEquiv (X Y Z : CommAlgCat.{u} R) :
    (X ⊗ Y ⟶ Z) ≃ ((X ⟶ Z) × (Y ⟶ Z)) where
  toFun f := ((binaryCofan X Y).inl ≫ f, (binaryCofan X Y).inr ≫ f)
  invFun p := (binaryCofanIsColimit X Y).desc (BinaryCofan.mk p.1 p.2)
  left_inv f := by
    apply (binaryCofanIsColimit X Y).hom_ext
    intro j
    rw [(binaryCofanIsColimit X Y).fac
      (BinaryCofan.mk ((binaryCofan X Y).inl ≫ f) ((binaryCofan X Y).inr ≫ f)) j]
    rcases j with ⟨j⟩
    cases j <;> rfl
  right_inv p := by
    apply Prod.ext
    · exact (binaryCofanIsColimit X Y).fac (BinaryCofan.mk p.1 p.2) ⟨WalkingPair.left⟩
    · exact (binaryCofanIsColimit X Y).fac (BinaryCofan.mk p.1 p.2) ⟨WalkingPair.right⟩

private def tensorPowerHomEquiv (B C : CommAlgCat.{u} R) :
    (n : ℕ) → (tensorPower B n ⟶ C) ≃ (Fin n → (B ⟶ C))
  | 0 =>
      { toFun := fun _ i => Fin.elim0 i
        invFun := fun _ => isInitialSelf.to C
        left_inv := fun _ => isInitialSelf.hom_ext _ _
        right_inv := fun _ => funext fun i => Fin.elim0 i }
  | n + 1 =>
      (binaryHomEquiv B (tensorPower B n) C).trans <|
        ((Equiv.refl (B ⟶ C)).prodCongr (tensorPowerHomEquiv B C n)).trans <|
          Fin.consEquiv (fun _ : Fin (n + 1) => B ⟶ C)

private lemma tensorPowerHomEquiv_comp (B : CommAlgCat.{u} R) {C D : CommAlgCat.{u} R}
    (n : ℕ) (f : tensorPower B n ⟶ C) (g : C ⟶ D) :
    tensorPowerHomEquiv B D n (f ≫ g) =
      fun i => tensorPowerHomEquiv B C n f i ≫ g := by
  induction n with
  | zero =>
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · change ((binaryCofan B (tensorPower B n)).inl ≫ f) ≫ g =
          (binaryCofan B (tensorPower B n)).inl ≫ (f ≫ g)
        exact Category.assoc _ _ _
      · change tensorPowerHomEquiv B D n
            (((binaryCofan B (tensorPower B n)).inr ≫ f) ≫ g) j =
          tensorPowerHomEquiv B C n
              ((binaryCofan B (tensorPower B n)).inr ≫ f) j ≫ g
        exact congrFun (ih ((binaryCofan B (tensorPower B n)).inr ≫ f)) j

private def tensorPiAlgEquiv (C : CommAlgCat.{u} R) (n : ℕ) :
    C ⊗[R] (Fin n → R) ≃ₐ[R] (Fin n → C) :=
  (Algebra.TensorProduct.piRight R R C (fun _ : Fin n => R)).trans <|
    AlgEquiv.piCongrRight fun _ : Fin n => Algebra.TensorProduct.rid R R C

private lemma tensorPiAlgEquiv_map {C D : CommAlgCat.{u} R} (n : ℕ) (g : C ⟶ D)
    (z : C ⊗[R] (Fin n → R)) (i : Fin n) :
    tensorPiAlgEquiv D n
        (Algebra.TensorProduct.map g.hom (AlgHom.id R (Fin n → R)) z) i =
      g.hom (tensorPiAlgEquiv C n z i) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  | tmul c a => simp [tensorPiAlgEquiv]

private def homTensorPiEquiv (B C : CommAlgCat.{u} R) (n : ℕ) :
    (B ⟶ (MonoidalCategory.tensorRight (of R (Fin n → R))).obj C) ≃
      (Fin n → (B ⟶ C)) where
  toFun f i := ofHom <| (Pi.evalAlgHom R (fun _ : Fin n => C) i).comp <|
    (tensorPiAlgEquiv C n).toAlgHom.comp f.hom
  invFun f := ofHom <| (tensorPiAlgEquiv C n).symm.toAlgHom.comp <| AlgHom.pi fun i => (f i).hom
  left_inv f := by
    apply hom_ext
    ext x
    change (tensorPiAlgEquiv C n).symm (fun i => tensorPiAlgEquiv C n (f.hom x) i) = f.hom x
    rw [show (fun i => tensorPiAlgEquiv C n (f.hom x) i) =
      tensorPiAlgEquiv C n (f.hom x) by rfl]
    exact (tensorPiAlgEquiv C n).symm_apply_apply (f.hom x)
  right_inv f := by
    funext i
    apply hom_ext
    ext x
    change tensorPiAlgEquiv C n
      ((tensorPiAlgEquiv C n).symm (fun i => (f i).hom x)) i = (f i).hom x
    rw [(tensorPiAlgEquiv C n).apply_symm_apply]

private lemma homTensorPiEquiv_map (B : CommAlgCat.{u} R) {C D : CommAlgCat.{u} R}
    (n : ℕ) (f : B ⟶ (MonoidalCategory.tensorRight (of R (Fin n → R))).obj C)
    (g : C ⟶ D) :
    homTensorPiEquiv B D n
        (f ≫ (MonoidalCategory.tensorRight (of R (Fin n → R))).map g) =
      fun i => homTensorPiEquiv B C n f i ≫ g := by
  funext i
  apply hom_ext
  ext x
  exact tensorPiAlgEquiv_map n g (f.hom x) i

private def splitCorepresentableBy (B : CommAlgCat.{u} R) (n : ℕ) :
    ((MonoidalCategory.tensorRight (of R (Fin n → R))) ⋙
      coyoneda.obj (Opposite.op B)).CorepresentableBy (tensorPower B n) where
  homEquiv {Y} := (tensorPowerHomEquiv B Y n).trans (homTensorPiEquiv B Y n).symm
  homEquiv_comp {Y Y'} g f := by
    apply (homTensorPiEquiv B Y' n).injective
    change homTensorPiEquiv B Y' n
        ((homTensorPiEquiv B Y' n).symm (tensorPowerHomEquiv B Y' n (f ≫ g))) =
      homTensorPiEquiv B Y' n
        ((homTensorPiEquiv B Y n).symm (tensorPowerHomEquiv B Y n f) ≫
          (MonoidalCategory.tensorRight (of R (Fin n → R))).map g)
    rw [Equiv.apply_symm_apply, homTensorPiEquiv_map, Equiv.apply_symm_apply]
    exact tensorPowerHomEquiv_comp B n f g

private def tensorRightIsoOfIso {A A' : CommAlgCat.{u} R} (e : A ≅ A') :
    MonoidalCategory.tensorRight A ≅ MonoidalCategory.tensorRight A' :=
  NatIso.ofComponents (fun C => MonoidalCategory.whiskerLeftIso C e) fun f =>
    (MonoidalCategory.whisker_exchange f e.hom).symm

private def splitCorepresentableByOfAlgEquiv
    {A : Type u} [CommRing A] [Algebra R A] (B : CommAlgCat.{u} R)
    {n : ℕ} (e : A ≃ₐ[R] (Fin n → R)) :
    ((MonoidalCategory.tensorRight (of R A)) ⋙ coyoneda.obj (Opposite.op B)).CorepresentableBy
      (tensorPower B n) :=
  (splitCorepresentableBy B n).ofIso <|
    Functor.isoWhiskerRight
      (tensorRightIsoOfIso (isoMk e)).symm
      (coyoneda.obj (Opposite.op B))

private lemma tensorPower_finite (B : CommAlgCat.{u} R) [Module.Finite R B] (n : ℕ) :
    Module.Finite R (tensorPower B n) := by
  induction n with
  | zero => exact Module.Finite.self R
  | succ n ih =>
      change Module.Finite R (B ⊗[R] tensorPower B n)
      exact Module.Finite.tensorProduct R B (tensorPower B n)

private lemma tensorPower_etale (B : CommAlgCat.{u} R) [Algebra.Etale R B] (n : ℕ) :
    Algebra.Etale R (tensorPower B n) := by
  induction n with
  | zero =>
      change Algebra.Etale R R
      infer_instance
  | succ n ih =>
      let : Algebra.Etale R (tensorPower B n) := ih
      change Algebra.Etale R (B ⊗[R] tensorPower B n)
      let : Algebra.Etale B (B ⊗[R] tensorPower B n) :=
        Algebra.Etale.baseChange R (tensorPower B n) B
      exact Algebra.Etale.comp R B (B ⊗[R] tensorPower B n)

/-- The commutative R-algebra corepresenting homomorphisms from B to tensor products with the
finite free R-algebra A. -/
def affineWeilRestriction
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Module.Free R A] [Module.Finite R A] [Algebra.FinitePresentation R B] :
    CommAlgCat.{u} R :=
  (MonoidalCategory.tensorRight (of R A)).partialLeftAdjointObj
    ⟨of R B, tensorRight_leftAdjointObjIsDefined⟩

/-- The canonical affine Weil restriction corepresents
`C ↦ Hom_R(B, C ⊗_R A)`. -/
noncomputable def affineWeilRestrictionCorepresentableBy
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Module.Free R A] [Module.Finite R A] [Algebra.FinitePresentation R B] :
    ((MonoidalCategory.tensorRight (of R A)) ⋙
      coyoneda.obj (Opposite.op (of R B))).CorepresentableBy
      (affineWeilRestriction (R := R) (A := A) (B := B)) := by
  let F := (MonoidalCategory.tensorRight (of R A)) ⋙ coyoneda.obj (Opposite.op (of R B))
  let : F.IsCorepresentable := tensorRight_leftAdjointObjIsDefined
  exact F.corepresentableBy

private lemma affineWeilRestriction_finite_etale_of_isFiniteSplit
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Algebra.IsFiniteSplit R A]
    [Module.Finite R B] [Algebra.Etale R B] :
    Module.Finite R (affineWeilRestriction (R := R) (A := A) (B := B)) ∧
      Algebra.Etale R (affineWeilRestriction (R := R) (A := A) (B := B)) := by
  obtain ⟨n, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun R A
  let F := (MonoidalCategory.tensorRight (of R A)) ⋙ coyoneda.obj (Opposite.op (of R B))
  let : F.IsCorepresentable := tensorRight_leftAdjointObjIsDefined
  let h := splitCorepresentableByOfAlgEquiv (of R B) e
  let i : tensorPower (of R B) n ≅ affineWeilRestriction (R := R) (A := A) (B := B) :=
    h.isoCoreprX
  let ei : tensorPower (of R B) n ≃ₐ[R]
      affineWeilRestriction (R := R) (A := A) (B := B) := algEquivOfIso i
  let : Module.Finite R (tensorPower (of R B) n) := tensorPower_finite (of R B) n
  let : Algebra.Etale R (tensorPower (of R B) n) := tensorPower_etale (of R B) n
  exact ⟨Module.Finite.equiv ei.toLinearEquiv, Algebra.Etale.of_equiv ei⟩

section BaseChange

variable {S A B : Type u}
  [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B]
  [Module.Free R A] [Module.Finite R A]
  [Algebra.FinitePresentation R B]

private abbrev AS := S ⊗[R] A
private abbrev BS := S ⊗[R] B

local instance : Module.Finite S (S ⊗[R] A) :=
  Module.Finite.of_basis
    (Algebra.TensorProduct.basis S (Module.Free.chooseBasis R A))

private abbrev tensorRightR :=
  MonoidalCategory.tensorRight (of R A)

private def sourceR : tensorRightR (R := R) (A := A).PartialLeftAdjointSource :=
  ⟨of R B, tensorRight_leftAdjointObjIsDefined⟩

private abbrev HR :=
  (tensorRightR (R := R) (A := A)).partialLeftAdjointObj
    (sourceR (R := R) (A := A) (B := B))

private abbrev baseHR : CommAlgCat S :=
  of S (S ⊗[R] HR (R := R) (A := A) (B := B))

private abbrev restrictObj (C : CommAlgCat S) : CommAlgCat R :=
  letI : Algebra R C := Algebra.compHom C (algebraMap R S)
  of R C

private def restrictMap {C D : CommAlgCat S} (f : C ⟶ D) :
    restrictObj (R := R) C ⟶ restrictObj (R := R) D := by
  letI : Algebra R C := Algebra.compHom C (algebraMap R S)
  letI : Algebra R D := Algebra.compHom D (algebraMap R S)
  letI : IsScalarTower R S C := .of_algebraMap_eq' rfl
  letI : IsScalarTower R S D := .of_algebraMap_eq' rfl
  exact ofHom (f.hom.restrictScalars R)

private def baseChangeHomEquiv (C : CommAlgCat S) :
    (baseHR (R := R) (S := S) (A := A) (B := B) ⟶ C) ≃
      (HR (R := R) (A := A) (B := B) ⟶ restrictObj (R := R) C) where
  toFun f := by
    let : Algebra R C := Algebra.compHom C (algebraMap R S)
    let : IsScalarTower R S C := .of_algebraMap_eq' rfl
    exact ofHom
      ((Algebra.TensorProduct.liftEquivRight R S
        (HR (R := R) (A := A) (B := B)) C).symm f.hom)
  invFun f := by
    let : Algebra R C := Algebra.compHom C (algebraMap R S)
    let : IsScalarTower R S C := .of_algebraMap_eq' rfl
    exact ofHom
      (Algebra.TensorProduct.liftEquivRight R S
        (HR (R := R) (A := A) (B := B)) C f.hom)
  left_inv f := by
    apply hom_ext
    let : Algebra R C := Algebra.compHom C (algebraMap R S)
    let : IsScalarTower R S C := .of_algebraMap_eq' rfl
    exact Equiv.apply_symm_apply _ f.hom
  right_inv f := by
    apply hom_ext
    let : Algebra R C := Algebra.compHom C (algebraMap R S)
    let : IsScalarTower R S C := .of_algebraMap_eq' rfl
    exact Equiv.symm_apply_apply _ f.hom

private lemma baseChangeHomEquiv_comp {C D : CommAlgCat S}
    (f : baseHR (R := R) (S := S) (A := A) (B := B) ⟶ C) (g : C ⟶ D) :
    baseChangeHomEquiv (R := R) (S := S) (A := A) (B := B) D (f ≫ g) =
      baseChangeHomEquiv (R := R) (S := S) (A := A) (B := B) C f ≫
        restrictMap (R := R) g := by
  let : Algebra R C := Algebra.compHom C (algebraMap R S)
  let : Algebra R D := Algebra.compHom D (algebraMap R S)
  let : IsScalarTower R S C := .of_algebraMap_eq' rfl
  let : IsScalarTower R S D := .of_algebraMap_eq' rfl
  apply hom_ext
  apply AlgHom.ext
  intro x
  change g.hom (f.hom (1 ⊗ₜ[R] x)) = g.hom (f.hom (1 ⊗ₜ[R] x))
  rfl

private abbrev tensorRightS :=
  MonoidalCategory.tensorRight (of S (AS (R := R) (S := S) (A := A)))

private def postcompAlgEquiv {X Y : Type u}
    [CommRing X] [CommRing Y] [Algebra R X] [Algebra R Y]
    (e : X ≃ₐ[R] Y) : (B →ₐ[R] X) ≃ (B →ₐ[R] Y) where
  toFun f := e.toAlgHom.comp f
  invFun f := e.symm.toAlgHom.comp f
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp

private def targetAlgHomEquiv (C : CommAlgCat S) :
    (B →ₐ[R] (tensorRightR (R := R) (A := A)).obj (restrictObj (R := R) C)) ≃
      (BS (R := R) (S := S) (B := B) →ₐ[S]
        (tensorRightS (R := R) (S := S) (A := A)).obj C) := by
  letI : Algebra R C := Algebra.compHom C (algebraMap R S)
  letI : IsScalarTower R S C := .of_algebraMap_eq' rfl
  let D := C ⊗[S] AS (R := R) (S := S) (A := A)
  let e : D ≃ₐ[S] C ⊗[R] A :=
    Algebra.TensorProduct.cancelBaseChange R S S C A
  let eR : D ≃ₐ[R] C ⊗[R] A := e.restrictScalars R
  exact (postcompAlgEquiv (R := R) (B := B) eR.symm).trans
    (Algebra.TensorProduct.liftEquivRight R S B D)

omit [Module.Free R A] [Module.Finite R A] [Algebra.FinitePresentation R B] in
private lemma targetAlgHomEquiv_apply (C : CommAlgCat S)
    (f : B →ₐ[R]
      (tensorRightR (R := R) (A := A)).obj (restrictObj (R := R) C)) :
    letI : Algebra R C := Algebra.compHom C (algebraMap R S)
    letI : IsScalarTower R S C := .of_algebraMap_eq' rfl
    targetAlgHomEquiv (R := R) (S := S) (A := A) (B := B) C f =
        Algebra.TensorProduct.liftEquivRight R S B
          (C ⊗[S] AS (R := R) (S := S) (A := A))
            (((Algebra.TensorProduct.cancelBaseChange
              R S S C A).symm.restrictScalars R).toAlgHom.comp
              f) := by
  rfl

private def targetBaseChangeHomEquiv (C : CommAlgCat S) :
    (of R B ⟶ (tensorRightR (R := R) (A := A)).obj (restrictObj (R := R) C)) ≃
    (of S (BS (R := R) (S := S) (B := B)) ⟶
      (tensorRightS (R := R) (S := S) (A := A)).obj C) :=
  { toFun := fun f ↦ ofHom
      (targetAlgHomEquiv (R := R) (S := S) (A := A) (B := B) C f.hom)
    invFun := fun f ↦ ofHom
      ((targetAlgHomEquiv (R := R) (S := S) (A := A) (B := B) C).symm f.hom)
    left_inv := fun f ↦ hom_ext
      ((targetAlgHomEquiv (R := R) (S := S) (A := A) (B := B) C).symm_apply_apply f.hom)
    right_inv := fun f ↦ hom_ext
      ((targetAlgHomEquiv (R := R) (S := S) (A := A) (B := B) C).apply_symm_apply f.hom) }

omit [Module.Free R A] [Module.Finite R A] [Algebra.FinitePresentation R B] in
private lemma cancelBaseChange_symm_map {C D : CommAlgCat S}
    [Algebra R C] [Algebra R D]
    [IsScalarTower R S C] [IsScalarTower R S D]
    (g : C ⟶ D) (x : C ⊗[R] A) :
    (Algebra.TensorProduct.cancelBaseChange R S S D A).symm
        (Algebra.TensorProduct.map (g.hom.restrictScalars R) (AlgHom.id R A) x) =
      Algebra.TensorProduct.map g.hom (AlgHom.id S (S ⊗[R] A))
        ((Algebra.TensorProduct.cancelBaseChange R S S C A).symm x) := by
  induction x using TensorProduct.inductionOn with
  | tmul c a => simp
  | add x y hx hy => simp [hx, hy]

omit [Module.Free R A] [Module.Finite R A] [Algebra.FinitePresentation R B] in
private lemma targetBaseChangeHomEquiv_comp {C D : CommAlgCat S}
    (f : of R B ⟶
      (tensorRightR (R := R) (A := A)).obj (restrictObj (R := R) C))
    (g : C ⟶ D) :
    targetBaseChangeHomEquiv (R := R) (S := S) (A := A) (B := B) D
        (f ≫ (tensorRightR (R := R) (A := A)).map (restrictMap (R := R) g)) =
      targetBaseChangeHomEquiv (R := R) (S := S) (A := A) (B := B) C f ≫
        (tensorRightS (R := R) (S := S) (A := A)).map g := by
  let : Algebra R C := Algebra.compHom C (algebraMap R S)
  let : Algebra R D := Algebra.compHom D (algebraMap R S)
  let : IsScalarTower R S C := .of_algebraMap_eq' rfl
  let : IsScalarTower R S D := .of_algebraMap_eq' rfl
  let f' : B →ₐ[R] C ⊗[R] A := f.hom
  apply hom_ext
  change
    targetAlgHomEquiv (R := R) (S := S) (A := A) (B := B) D
        ((Algebra.TensorProduct.map (g.hom.restrictScalars R) (AlgHom.id R A)).comp f') =
      (Algebra.TensorProduct.map g.hom (AlgHom.id S (S ⊗[R] A))).comp
        (targetAlgHomEquiv (R := R) (S := S) (A := A) (B := B) C f')
  rw [targetAlgHomEquiv_apply, targetAlgHomEquiv_apply]
  apply Algebra.TensorProduct.ext_ring
  apply AlgHom.ext
  intro x
  simp only [Algebra.TensorProduct.liftEquivRight_apply,
    Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply,
    AlgHom.restrictScalars_apply, map_one, one_mul]
  change
    (Algebra.TensorProduct.cancelBaseChange R S S D A).symm
        (Algebra.TensorProduct.map (g.hom.restrictScalars R) (AlgHom.id R A) (f.hom x)) =
      Algebra.TensorProduct.map g.hom (AlgHom.id S (S ⊗[R] A))
        ((Algebra.TensorProduct.cancelBaseChange R S S C A).symm (f.hom x))
  exact cancelBaseChange_symm_map (R := R) (S := S) (A := A) g (f' x)

private def sourceS :
    tensorRightS (R := R) (S := S) (A := A).PartialLeftAdjointSource :=
  ⟨of S (BS (R := R) (S := S) (B := B)), tensorRight_leftAdjointObjIsDefined⟩

private abbrev HS :=
  affineWeilRestriction
    (R := S) (A := AS (R := R) (S := S) (A := A))
    (B := BS (R := R) (S := S) (B := B))

private def baseChangeCorepresentableBy :
    ((tensorRightS (R := R) (S := S) (A := A)) ⋙
      coyoneda.obj (Opposite.op (of S (BS (R := R) (S := S) (B := B))))).CorepresentableBy
        (baseHR (R := R) (S := S) (A := A) (B := B)) where
  homEquiv {Y} :=
    (baseChangeHomEquiv (R := R) (S := S) (A := A) (B := B) Y).trans <|
      ((tensorRightR (R := R) (A := A)).partialLeftAdjointHomEquiv
        (X := sourceR (R := R) (A := A) (B := B))).trans <|
          targetBaseChangeHomEquiv (R := R) (S := S) (A := A) (B := B) Y
  homEquiv_comp {Y Y'} g f := by
    change
      targetBaseChangeHomEquiv (R := R) (S := S) (A := A) (B := B) Y'
          ((tensorRightR (R := R) (A := A)).partialLeftAdjointHomEquiv
            (baseChangeHomEquiv (R := R) (S := S) (A := A) (B := B) Y' (f ≫ g))) =
        targetBaseChangeHomEquiv (R := R) (S := S) (A := A) (B := B) Y
            ((tensorRightR (R := R) (A := A)).partialLeftAdjointHomEquiv
              (baseChangeHomEquiv (R := R) (S := S) (A := A) (B := B) Y f)) ≫
          (tensorRightS (R := R) (S := S) (A := A)).map g
    rw [baseChangeHomEquiv_comp, Functor.partialLeftAdjointHomEquiv_comp]
    exact targetBaseChangeHomEquiv_comp (R := R) (S := S) (A := A) (B := B) _ _

/-- Affine Weil restriction commutes with arbitrary base change. -/
noncomputable opaque affineWeilRestrictionBaseChangeIso :
    of S (S ⊗[R] affineWeilRestriction (R := R) (A := A) (B := B)) ≅
      affineWeilRestriction
        (R := S) (A := S ⊗[R] A) (B := S ⊗[R] B) := by
  letI : ((tensorRightS (R := R) (S := S) (A := A)) ⋙
      coyoneda.obj (Opposite.op
        (of S (BS (R := R) (S := S) (B := B))))).IsCorepresentable :=
    (sourceS (R := R) (S := S) (A := A) (B := B)).property
  exact (baseChangeCorepresentableBy
    (R := R) (S := S) (A := A) (B := B)).isoCoreprX

end BaseChange

/-- If `A` and `B` are finite étale over `R`, then their affine Weil
restriction corepresenter is finite étale over `R`. -/
theorem affineWeilRestriction_finiteEtale
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Module.Free R A] [Module.Finite R A] [Algebra.Etale R A]
    [Module.Finite R B] [Algebra.Etale R B] :
    finiteEtale R (affineWeilRestriction (R := R) (A := A) (B := B)) := by
  obtain ⟨T, _, _, _, _, _, hsplitA⟩ :=
    Algebra.IsFiniteSplit.exists_tensorProduct_of_etale
      (R := R) (S := A) (n := Module.finrank R A)
      (Module.rankAtStalk_eq_finrank_of_free (R := R) (M := A))
  let : Algebra.IsFiniteSplit T (T ⊗[R] A) := hsplitA
  let : Module.Finite T (T ⊗[R] B) := Module.Finite.base_change R T B
  let : Algebra.Etale T (T ⊗[R] B) := Algebra.Etale.baseChange R B T
  have hT := affineWeilRestriction_finite_etale_of_isFiniteSplit
    (R := T) (A := T ⊗[R] A) (B := T ⊗[R] B)
  let : Module.Finite T
      (affineWeilRestriction (R := T) (A := T ⊗[R] A) (B := T ⊗[R] B)) := hT.1
  let : Algebra.Etale T
      (affineWeilRestriction (R := T) (A := T ⊗[R] A) (B := T ⊗[R] B)) := hT.2
  let e := algEquivOfIso
    (affineWeilRestrictionBaseChangeIso (R := R) (S := T) (A := A) (B := B))
  let : Module.Finite T
      (T ⊗[R] affineWeilRestriction (R := R) (A := A) (B := B)) :=
    Module.Finite.equiv e.symm.toLinearEquiv
  let : Algebra.Etale T
      (T ⊗[R] affineWeilRestriction (R := R) (A := A) (B := B)) :=
    Algebra.Etale.of_equiv e.symm
  exact
    ⟨Module.Finite.of_finite_tensorProduct_of_faithfullyFlat T,
      Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat T⟩

end CommAlgCat

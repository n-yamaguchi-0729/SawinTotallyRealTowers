/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_PresheafOfModules_InternalHom.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-!
# Internal Hom of module presheaves

The internal Hom is constructed from families of linear maps compatible with restriction.
Currying and uncurrying give the tensor-left adjunction, and hence the monoidal closed
structure on module presheaves over a presheaf of commutative rings.
-/

universe u v' u'

open CategoryTheory MonoidalCategory Limits Opposite

namespace PresheafOfModules

section general

variable {C : Type u'} [Category.{v'} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (F N : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

namespace InternalHom

lemma map_id_apply (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (X : Cᵒᵖ) (x : M.obj X) :
    M.map (𝟙 X) x = x := by
  change (M.presheaf.map (𝟙 X)) x = x
  rw [M.presheaf.map_id]; rfl

/-- Families of linear maps indexed by arrows from `X` in the opposite category. -/
abbrev PiFamily (X : Cᵒᵖ) : Type (max u u' v') :=
  ∀ ⦃Y : Cᵒᵖ⦄ (_ : X ⟶ Y), (F.obj Y →ₗ[R.obj Y] N.obj Y)

variable {F N} in
/-- Compatibility of a family of linear maps with restriction along subsequent arrows. -/
def IsNatural {X : Cᵒᵖ} (φ : PiFamily F N X) : Prop :=
  ∀ ⦃Y Z : Cᵒᵖ⦄ (f : X ⟶ Y) (g : Y ⟶ Z) (x : F.obj Y), N.map g (φ f x) = φ (f ≫ g) (F.map g x)

/-- The additive subgroup of families compatible with restriction. -/
def naturalFamilies (X : Cᵒᵖ) : AddSubgroup (PiFamily F N X) where
  carrier := {φ | IsNatural φ}
  zero_mem' := by
    intro Y Z f g x
    simp only [Pi.zero_apply, LinearMap.zero_apply]
    exact (N.map g).hom.map_zero
  add_mem' := by
    intro φ ψ hφ hψ Y Z f g x
    exact ((N.map g).hom.map_add (φ f x) (ψ f x)).trans
      (congrArg₂ (fun a b : N.obj Z => a + b) (hφ f g x) (hψ f g x))
  neg_mem' := by
    intro φ hφ Y Z f g x
    exact ((N.map g).hom.map_neg (φ f x)).trans
      (congrArg (fun a : N.obj Z => -a) (hφ f g x))

variable {F N}

@[ext] lemma naturalFamilies_ext {X : Cᵒᵖ} {φ ψ : naturalFamilies F N X}
    (h : ∀ ⦃Y : Cᵒᵖ⦄ (f : X ⟶ Y) (x : F.obj Y), φ.1 f x = ψ.1 f x) : φ = ψ :=
  Subtype.ext (funext fun _ => funext fun f => LinearMap.ext (h f))

lemma naturality {X : Cᵒᵖ} (φ : naturalFamilies F N X) ⦃Y Z : Cᵒᵖ⦄ (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : F.obj Y) : N.map g (φ.1 f x) = φ.1 (f ≫ g) (F.map g x) := φ.2 f g x

lemma congr_app {X : Cᵒᵖ} (φ : naturalFamilies F N X) {Y : Cᵒᵖ} {f g : X ⟶ Y} (h : f = g)
    (x : F.obj Y) : φ.1 f x = φ.1 g x := by subst h; rfl

instance (X : Cᵒᵖ) : SMul (R.obj X) (naturalFamilies F N X) where
  smul r φ := ⟨fun Y f => R.map f r • φ.1 f, by
    intro Y Z f g x
    simp only [LinearMap.smul_apply]
    rw [N.map_smul]
    erw [φ.2 f g x]
    congr 1
    rw [Functor.map_comp]
    rfl⟩

@[simp] lemma smul_app {X : Cᵒᵖ} (r : R.obj X) (φ : naturalFamilies F N X) {Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : F.obj Y) : (r • φ).1 f x = R.map f r • φ.1 f x := rfl
@[simp] lemma add_app {X : Cᵒᵖ} (φ ψ : naturalFamilies F N X) {Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : F.obj Y) : (φ + ψ).1 f x = φ.1 f x + ψ.1 f x := rfl
@[simp] lemma zero_app {X : Cᵒᵖ} {Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : F.obj Y) : (0 : naturalFamilies F N X).1 f x = 0 := rfl
@[simp] lemma neg_app {X : Cᵒᵖ} (φ : naturalFamilies F N X) {Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : F.obj Y) : (-φ).1 f x = - φ.1 f x := rfl
@[simp] lemma sub_app {X : Cᵒᵖ} (φ ψ : naturalFamilies F N X) {Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : F.obj Y) : (φ - ψ).1 f x = φ.1 f x - ψ.1 f x := rfl

instance (X : Cᵒᵖ) : Module (R.obj X) (naturalFamilies F N X) where
  one_smul φ := by ext Y f x; simp
  mul_smul r s φ := by ext Y f x; simp [mul_smul]
  smul_zero r := by ext Y f x; simp
  smul_add r φ ψ := by ext Y f x; simp
  add_smul r s φ := by ext Y f x; simp [add_smul]
  zero_smul φ := by ext Y f x; simp

variable (F N)

/-- Restriction of natural families by precomposing their indexing arrows. -/
def restrict {X X' : Cᵒᵖ} (h : X ⟶ X') : naturalFamilies F N X →+ naturalFamilies F N X' where
  toFun φ := ⟨fun Y f => φ.1 (h ≫ f), fun Y Z f g x => by
    rw [φ.2 (h ≫ f) g x, Category.assoc]⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] lemma restrict_app {X X' : Cᵒᵖ} (h : X ⟶ X') (φ : naturalFamilies F N X) {Y : Cᵒᵖ}
    (f : X' ⟶ Y) (x : F.obj Y) : (restrict F N h φ).1 f x = φ.1 (h ≫ f) x := rfl

/-- The presheaf of additive groups of natural families of linear maps. -/
@[simps obj] def presheaf : Cᵒᵖ ⥤ Ab.{max u u' v'} where
  obj X := AddCommGrpCat.of (naturalFamilies F N X)
  map h := AddCommGrpCat.ofHom (restrict F N h)
  map_id X := by
    ext φ Y f x
    change φ.1 (𝟙 X ≫ f) x = φ.1 f x
    rw [Category.id_comp]
  map_comp h h' := by
    ext φ Y f x
    change φ.1 ((h ≫ h') ≫ f) x = φ.1 (h ≫ (h' ≫ f)) x
    rw [Category.assoc]

@[simp] lemma presheaf_map_apply {X X' : Cᵒᵖ} (h : X ⟶ X') (φ : naturalFamilies F N X) {Y : Cᵒᵖ}
    (f : X' ⟶ Y) (x : F.obj Y) : ((presheaf F N).map h φ).1 f x = φ.1 (h ≫ f) x := rfl

instance (X : Cᵒᵖ) : Module ((R ⋙ forget₂ CommRingCat RingCat).obj X) ((presheaf F N).obj X) :=
  inferInstanceAs (Module (R.obj X) (naturalFamilies F N X))

variable {N} in
/-- Postcomposition of each linear map in a natural family by a module-presheaf morphism. -/
def postcomp {N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (ψ : N ⟶ N') (X : Cᵒᵖ) :
    naturalFamilies F N X →+ naturalFamilies F N' X where
  toFun φ := ⟨fun Y f =>
    { toFun := fun x => ψ.app Y (φ.1 f x)
      map_add' := fun x x' => by simp
      map_smul' := fun r x => by
        rw [(φ.1 f).map_smul]
        exact (ψ.app Y).hom.map_smul r _ }, by
    intro Y Z f g x
    change N'.map g (ψ.app Y (φ.1 f x)) = ψ.app Z (φ.1 (f ≫ g) (F.map g x))
    rw [← naturality_apply, φ.2 f g x]⟩
  map_zero' := by ext Y f x; exact (ψ.app Y).hom.map_zero
  map_add' φ φ' := by ext Y f x; exact (ψ.app Y).hom.map_add _ _

@[simp] lemma postcomp_app {N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (ψ : N ⟶ N') {X : Cᵒᵖ}
    (φ : naturalFamilies F N X) {Y : Cᵒᵖ} (f : X ⟶ Y) (x : F.obj Y) :
    (postcomp F ψ X φ).1 f x = ψ.app Y (φ.1 f x) := rfl

end InternalHom

open InternalHom

/-- The module presheaf of natural families of local linear maps from `F` to `N`. -/
@[simps! obj] noncomputable def ihomObj : PresheafOfModules.{max u u' v'} (R ⋙ forget₂ _ _) :=
  ofPresheaf (InternalHom.presheaf F N) (by
    intro X X' h r φ
    apply naturalFamilies_ext
    intro Y f x
    change (R.map (h ≫ f) r) • φ.1 (h ≫ f) x = R.map f (R.map h r) • φ.1 (h ≫ f) x
    rw [Functor.map_comp]
    rfl)

@[simp] lemma ihomObj_map_val {X X' : Cᵒᵖ} (h : X ⟶ X') (φ : (ihomObj F N).obj X) {Y : Cᵒᵖ}
    (f : X' ⟶ Y) (x : F.obj Y) :
    ((ihomObj F N).map h φ).1 f x = φ.1 (h ≫ f) x := rfl

variable {N} in
/-- The internal-Hom morphism induced by postcomposition in its second argument. -/
noncomputable def ihomMap {N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (ψ : N ⟶ N') :
    ihomObj F N ⟶ ihomObj F N' :=
  homMk { app := fun X => AddCommGrpCat.ofHom (postcomp F ψ X)
          naturality := fun {X X'} h => by ext φ; rfl } (by
    intro X r φ
    apply naturalFamilies_ext
    intro Y f x
    exact (ψ.app Y).hom.map_smul _ _)

@[simp] lemma ihomMap_app_val {N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (ψ : N ⟶ N')
    {X : Cᵒᵖ} (φ : (ihomObj F N).obj X) {Y : Cᵒᵖ} (f : X ⟶ Y) (x : F.obj Y) :
    ((ihomMap F ψ).app X φ).1 f x = ψ.app Y (φ.1 f x) := rfl

/-- The internal-Hom functor with fixed first argument `F`. -/
noncomputable def ihomFunctor :
    PresheafOfModules.{u} (R ⋙ forget₂ _ _) ⥤ PresheafOfModules.{max u u' v'} (R ⋙ forget₂ _ _)
      where
  obj N := ihomObj F N
  map ψ := ihomMap F ψ
  map_id N := by
    ext X φ
    apply naturalFamilies_ext
    intro Y f y; rfl
  map_comp ψ ψ' := by
    ext X φ
    apply naturalFamilies_ext
    intro Y f y; rfl

@[simp] lemma ihomFunctor_obj (N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) :
    (ihomFunctor F).obj N' = ihomObj F N' := rfl
@[simp] lemma ihomFunctor_map {N' N'' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (ψ : N' ⟶ N'') :
    (ihomFunctor F).map ψ = ihomMap F ψ := rfl

end general

section closed

-- Keep the bundled-ring comparison at the same transparency as Mathlib's
-- `PresheafOfModulesOfCommRing.Monoidal.tensorObjMap`.

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (F : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) {G N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)}

local instance commRingAt (X : Cᵒᵖ) : CommRing ((R ⋙ forget₂ CommRingCat RingCat).obj X) :=
  inferInstanceAs (CommRing (R.obj X))

namespace InternalHom

/-- The natural family obtained by currying a tensor morphism against the section `y`. -/
noncomputable def curryFamily (θ : F ⊗ G ⟶ N) {X : Cᵒᵖ} (y : G.obj X) : naturalFamilies F N X :=
  ⟨fun Y f =>
    { toFun := fun x => θ.app Y (x ⊗ₜ[R.obj Y] G.map f y)
      map_add' := fun x x' =>
        (congrArg (θ.app Y) (TensorProduct.add_tmul x x' (show G.obj Y from G.map f y))).trans
          ((θ.app Y).hom.map_add _ _)
      map_smul' := fun r x =>
        (congrArg (θ.app Y) (TensorProduct.smul_tmul' r x (show G.obj Y from G.map f y)).symm).trans
          ((θ.app Y).hom.map_smul r _) }, by
    intro Y Z f g x
    exact (naturality_apply θ g (x ⊗ₜ[R.obj Y] (show G.obj Y from G.map f y))).symm.trans
      ((congrArg (θ.app Z)
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul
          (M₁ := F) (M₂ := G) g x (show G.obj Y from G.map f y))).trans
        (congrArg (fun z : G.obj Z => θ.app Z (F.map g x ⊗ₜ[R.obj Z] z))
          (G.map_comp_apply f g y).symm))⟩

@[simp] lemma curryFamily_app (θ : F ⊗ G ⟶ N) {X : Cᵒᵖ} (y : G.obj X) {Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : F.obj Y) : (curryFamily F θ y).1 f x = θ.app Y (x ⊗ₜ[R.obj Y] G.map f y) := rfl

end InternalHom

open InternalHom

/-- The internal-Hom morphism obtained by currying a tensor morphism. -/
noncomputable def curry' (θ : F ⊗ G ⟶ N) : G ⟶ ihomObj F N :=
  homMk
    { app := fun X => AddCommGrpCat.ofHom
        { toFun := fun y => curryFamily F θ y
          map_zero' := by
            apply naturalFamilies_ext; intro Y f x
            have h0 : G.map f (0 : G.obj X) = 0 := (G.map f).hom.map_zero
            exact (congrArg (fun z : G.obj Y => θ.app Y (x ⊗ₜ[R.obj Y] z)) h0).trans
              ((congrArg (θ.app Y) (TensorProduct.tmul_zero (G.obj Y) x)).trans ((θ.app
                Y).hom.map_zero))
          map_add' := fun y y' => by
            apply naturalFamilies_ext; intro Y f x
            have h1 : G.map f (y + y') = G.map f y + G.map f y' := (G.map f).hom.map_add _ _
            exact (congrArg (fun z : G.obj Y => θ.app Y (x ⊗ₜ[R.obj Y] z)) h1).trans
              ((congrArg (θ.app Y) (TensorProduct.tmul_add x
                (show G.obj Y from G.map f y) (show G.obj Y from G.map f y'))).trans
                ((θ.app Y).hom.map_add _ _)) }
      naturality := fun {X X'} h => by
        ext y
        apply naturalFamilies_ext; intro Y f x
        exact congrArg (fun z : G.obj Y => θ.app Y (x ⊗ₜ[R.obj Y] z))
          (G.map_comp_apply h f y).symm }
    (by
      intro X r y
      apply naturalFamilies_ext; intro Y f x
      have hg : G.map f (r • y) = R.map f r • (show G.obj Y from G.map f y) := G.map_smul f r y
      exact (congrArg (fun z : G.obj Y => θ.app Y (x ⊗ₜ[R.obj Y] z)) hg).trans
        ((congrArg (θ.app Y) (TensorProduct.tmul_smul (R.map f r) x
          (show G.obj Y from G.map f y))).trans ((θ.app Y).hom.map_smul _ _)))

@[simp] lemma curry'_app_val (θ : F ⊗ G ⟶ N) {X : Cᵒᵖ} (y : G.obj X) {Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : F.obj Y) : ((curry' F θ).app X y).1 f x = θ.app Y (x ⊗ₜ[R.obj Y] G.map f y) := rfl

/-- The component of the uncurried tensor morphism, evaluated using the identity indexing arrow. -/
noncomputable def uncurryApp (κ : G ⟶ ihomObj F N) (X : Cᵒᵖ) : (F ⊗ G).obj X ⟶ N.obj X :=
  ModuleCat.MonoidalCategory.tensorLift (R := R.obj X) (fun (x : F.obj X) (y : G.obj X) => (κ.app X
    y).1 (𝟙 X) x)
    (fun x x' y => ((κ.app X y).1 (𝟙 X)).map_add x x')
    (fun r x y => ((κ.app X y).1 (𝟙 X)).map_smul r x)
    (fun x y y' => by
      have h1 : κ.app X (y + y') = κ.app X y + κ.app X y' := (κ.app X).hom.map_add _ _
      simp only [h1]; rfl)
    (fun r x y => by
      have h1 : κ.app X (r • y) = r • κ.app X y := (κ.app X).hom.map_smul _ _
      simp only [h1]
      change R.map (𝟙 X) r • (κ.app X y).1 (𝟙 X) x = _
      rw [R.map_id]
      rfl)

lemma tensorObj_map_tmul' {X Y : Cᵒᵖ} (g : X ⟶ Y) (x : F.obj X) (y : G.obj X) :
    DFunLike.coe (α := (F.obj X ⊗ G.obj X :))
      (β := fun _ => (ModuleCat.restrictScalars (R.map g).hom).obj (F.obj Y ⊗ G.obj Y))
      (ModuleCat.Hom.hom (R := ↑(R.obj X)) ((F ⊗ G).map g)) (x ⊗ₜ[R.obj X] y) =
    F.map g x ⊗ₜ[R.obj Y] G.map g y := rfl

lemma uncurryApp_tmul (κ : G ⟶ ihomObj F N) (X : Cᵒᵖ) (x : F.obj X) (y : G.obj X) :
    DFunLike.coe (α := (F.obj X ⊗ G.obj X :)) (β := fun _ => N.obj X)
      (uncurryApp F κ X).hom (x ⊗ₜ[R.obj X] y) = (κ.app X y).1 (𝟙 X) x := by
  erw [ModuleCat.MonoidalCategory.tensorLift_tmul (R := R.obj X)]

/-- The tensor morphism obtained by uncurrying an internal-Hom morphism. -/
noncomputable def uncurry' (κ : G ⟶ ihomObj F N) : F ⊗ G ⟶ N where
  app X := uncurryApp F κ X
  naturality {X Y} g := ModuleCat.MonoidalCategory.tensor_ext (fun x y => by
    have hκ := naturality_apply κ g y
    have hev := congrArg
      (fun φ : naturalFamilies F N Y => φ.1 (𝟙 Y) (F.map g x)) hκ
    exact (congrArg (uncurryApp F κ Y) (tensorObj_map_tmul' F (G := G) g x y)).trans
      ((uncurryApp_tmul F κ Y (F.map g x) (G.map g y)).trans
        (hev.trans
          ((ihomObj_map_val F N g (κ.app X y) (𝟙 Y) (F.map g x)).trans
            ((congr_app (κ.app X y)
              ((Category.comp_id g).trans (Category.id_comp g).symm) (F.map g x)).trans
              (((κ.app X y).2 (𝟙 X) g x).symm.trans
                (congrArg (N.map g) (uncurryApp_tmul F κ X x y).symm)))))))

lemma uncurry'_app_tmul (κ : G ⟶ ihomObj F N) {X : Cᵒᵖ} (x : F.obj X) (y : G.obj X) :
    DFunLike.coe (α := (F.obj X ⊗ G.obj X :)) (β := fun _ => N.obj X)
      ((uncurry' F κ).app X).hom (x ⊗ₜ[R.obj X] y) = (κ.app X y).1 (𝟙 X) x :=
  uncurryApp_tmul F κ X x y

lemma uncurry'_curry' (θ : F ⊗ G ⟶ N) : uncurry' F (curry' F θ) = θ := by
  ext X : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  erw [uncurry'_app_tmul]
  change θ.app X (x ⊗ₜ[R.obj X] G.map (𝟙 X) y) = θ.app X (x ⊗ₜ[R.obj X] y)
  rw [InternalHom.map_id_apply]

lemma curry'_uncurry' (κ : G ⟶ ihomObj F N) : curry' F (uncurry' F κ) = κ := by
  ext X y
  apply naturalFamilies_ext; intro Y f x
  rw [curry'_app_val]
  erw [uncurry'_app_tmul]
  rw [naturality_apply κ f y, ihomObj_map_val]
  exact congr_app _ (Category.comp_id f) _

/-- The tensor-left and internal-Hom adjunction given by currying and uncurrying. -/
noncomputable def tensorIhomAdj : tensorLeft F ⊣ ihomFunctor F :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun G N =>
        { toFun := curry' F
          invFun := uncurry' F
          left_inv := uncurry'_curry' F
          right_inv := curry'_uncurry' F }
      homEquiv_naturality_left_symm := fun {G G' N} γ κ => by
        ext X : 1
        apply ModuleCat.MonoidalCategory.tensor_ext
        intro x y
        change (uncurry' F (γ ≫ κ)).app X (x ⊗ₜ[R.obj X] y) =
          (uncurry' F κ).app X ((F ◁ γ).app X (x ⊗ₜ[R.obj X] y))
        erw [uncurry'_app_tmul, uncurry'_app_tmul]
      homEquiv_naturality_right := fun {G N N'} θ ν => by
        ext X y
        apply naturalFamilies_ext; intro Y f x
        rfl }

noncomputable instance instMonoidalClosed :
    MonoidalClosed (PresheafOfModules.{u} (R ⋙ forget₂ _ _)) where
  closed F := { rightAdj := ihomFunctor F, adj := tensorIhomAdj F }

end closed

end PresheafOfModules

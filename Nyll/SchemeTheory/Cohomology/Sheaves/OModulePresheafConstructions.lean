/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_OModulePresheafConstructions.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafHom
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties

/-!
Basic constructions on module presheaves, including kernels, cokernels, products and restrictions.
-/

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace

variable {R : Type u} [CommRing R] {V : Scheme.{u}}

namespace Scheme.OrderedAffineCover

/-- The ordered affine cover pulled back along a closed immersion. -/
def preimage {Z : Scheme.{u}} (i : Z ⟶ V) [IsClosedImmersion i] (K : V.OrderedAffineCover) :
    Z.OrderedAffineCover where
  ι := K.ι
  U j := i ⁻¹ᵁ K.U j
  isAffineOpen j := (K.isAffineOpen j).preimage i
  iSup_eq_top := Scheme.Hom.iSup_preimage_eq_top i K.iSup_eq_top

@[simp] theorem preimage_U {Z : Scheme.{u}} (i : Z ⟶ V) [IsClosedImmersion i] (K :
  V.OrderedAffineCover) (j : K.ι) :
    (K.preimage i).U j = i ⁻¹ᵁ K.U j := rfl

end Scheme.OrderedAffineCover

namespace OModulePresheaf

variable {π : V ⟶ Spec (.of R)}

/-- The pointwise product of two module presheaves. -/
def prod (F G : OModulePresheaf π) : OModulePresheaf π where
  obj U := F.obj U × G.obj U
  module U := inferInstance
  moduleSections U := Prod.instModule
  isScalarTower U := by
    let := Scheme.TwoAffineOpenCover.algebraOfHom π U
    exact ⟨fun r a x => Prod.ext (smul_assoc r a x.1) (smul_assoc r a x.2)⟩
  res h := (F.res h).prodMap (G.res h)
  res_smul h a x := Prod.ext (F.res_smul h a x.1) (G.res_smul h a x.2)
  res_refl U := LinearMap.ext fun x =>
    Prod.ext (LinearMap.congr_fun (F.res_refl U) x.1) (LinearMap.congr_fun (G.res_refl U) x.2)
  res_comp h h' := LinearMap.ext fun x =>
    Prod.ext (LinearMap.congr_fun (F.res_comp h h') x.1) (LinearMap.congr_fun (G.res_comp h h') x.2)

/-- The projection from the product module presheaf to its first factor. -/
def fstHom (F G : OModulePresheaf π) : Hom (F.prod G) F := ⟨fun _U => LinearMap.fst R _ _, fun _ _
    _ => rfl, fun _ => rfl⟩

/-- The projection from the product module presheaf to its second factor. -/
def sndHom (F G : OModulePresheaf π) : Hom (F.prod G) G := ⟨fun _U => LinearMap.snd R _ _, fun _ _
    _ => rfl, fun _ => rfl⟩

@[simp] theorem prod_obj (F G : OModulePresheaf π) (U : V.Opens) : (F.prod G).obj U = (F.obj U ×
  G.obj U) := rfl
@[simp] theorem fstHom_app (F G : OModulePresheaf π) (U : V.Opens) (x : (F.prod G).obj U) :
  (F.fstHom G).app U x = x.1 := rfl
@[simp] theorem sndHom_app (F G : OModulePresheaf π) (U : V.Opens) (x : (F.prod G).obj U) :
  (F.sndHom G).app U x = x.2 := rfl

/-- The pointwise finite power of a module presheaf indexed by Fin n. -/
def pow (F : OModulePresheaf π) (n : ℕ) : OModulePresheaf π where
  obj U := Fin n → F.obj U
  module U := inferInstance
  moduleSections U := Pi.module _ _ _
  isScalarTower U := by
    let := Scheme.TwoAffineOpenCover.algebraOfHom π U
    exact ⟨fun r a x => funext fun j => smul_assoc r a (x j)⟩
  res h := LinearMap.compLeft (F.res h) (Fin n)
  res_smul h a x := funext fun j => F.res_smul h a (x j)
  res_refl U := LinearMap.ext fun x => funext fun j => LinearMap.congr_fun (F.res_refl U) (x j)
  res_comp h h' := LinearMap.ext fun x => funext fun j => LinearMap.congr_fun (F.res_comp h h') (x
    j)

@[simp] theorem pow_obj (F : OModulePresheaf π) (n : ℕ) (U : V.Opens) : (F.pow n).obj U = (Fin n →
  F.obj U) := rfl
theorem pow_res_apply (F : OModulePresheaf π) (n : ℕ) {U U' : V.Opens} (h : U ≤ U') (x : (F.pow
    n).obj U') (j : Fin n) :
    (F.pow n).res h x j = F.res h (x j) := rfl

variable (π) in
/-- The zero module presheaf, with singleton sections on every open. -/
def zero : OModulePresheaf π where
  obj _ := PUnit.{u + 1}
  module _ := inferInstance
  moduleSections _ := inferInstance
  isScalarTower U := by
    let := Scheme.TwoAffineOpenCover.algebraOfHom π U
    exact ⟨fun _ _ _ => Subsingleton.elim _ _⟩
  res _ := 0
  res_smul _ _ _ := Subsingleton.elim _ _
  res_refl _ := Subsingleton.elim _ _
  res_comp _ _ := Subsingleton.elim _ _

instance (U : V.Opens) : Subsingleton ((zero π).obj U) := inferInstanceAs (Subsingleton PUnit.{u +
  1})

/-- Restrict the sections of F to intersections with the fixed open W₀. -/
def restrOpen (F : OModulePresheaf π) (W₀ : V.Opens) : OModulePresheaf π where
  obj U := F.obj (U ⊓ W₀)
  module U := inferInstance
  moduleSections U := Module.compHom _ (V.presheaf.map (homOfLE (inf_le_left : U ⊓ W₀ ≤ U)).op).hom
  isScalarTower U := by
    let := Scheme.TwoAffineOpenCover.algebraOfHom π U
    let := Scheme.TwoAffineOpenCover.algebraOfHom π (U ⊓ W₀)
    let : Module Γ(V, U) (F.obj (U ⊓ W₀)) :=
      Module.compHom _ (V.presheaf.map (homOfLE (inf_le_left : U ⊓ W₀ ≤ U)).op).hom
    refine ⟨fun r a x => ?_⟩
    change (V.presheaf.map (homOfLE (inf_le_left : U ⊓ W₀ ≤ U)).op).hom (r • a) • x
      = r • ((V.presheaf.map (homOfLE (inf_le_left : U ⊓ W₀ ≤ U)).op).hom a • x)
    rw [Algebra.smul_def, map_mul, mul_smul,
      show (V.presheaf.map (homOfLE (inf_le_left : U ⊓ W₀ ≤ U)).op).hom (algebraMap R Γ(V, U) r)
        = algebraMap R Γ(V, U ⊓ W₀) r from (Scheme.TwoAffineOpenCover.restrictAlgHom π
          inf_le_left).commutes r,
      algebraMap_smul]
  res h := F.res (inf_le_inf_right W₀ h)
  res_smul {U U'} h a x := by
    change F.res _ ((V.presheaf.map (homOfLE (inf_le_left : U' ⊓ W₀ ≤ U')).op).hom a • x)
      = (V.presheaf.map (homOfLE (inf_le_left : U ⊓ W₀ ≤ U)).op).hom
          ((V.presheaf.map (homOfLE h).op).hom a) • F.res (inf_le_inf_right W₀ h) x
    rw [F.res_smul, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply (g := V.presheaf.map _),
      ← V.presheaf.map_comp, ← V.presheaf.map_comp]
    rfl
  res_refl U := F.res_refl (U ⊓ W₀)
  res_comp h h' := F.res_comp (inf_le_inf_right W₀ h) (inf_le_inf_right W₀ h')

@[simp] theorem restrOpen_obj (F : OModulePresheaf π) (W₀ U : V.Opens) : (F.restrOpen W₀).obj U =
  F.obj (U ⊓ W₀) := rfl
theorem restrOpen_res (F : OModulePresheaf π) (W₀ : V.Opens) {U U' : V.Opens} (h : U ≤ U') :
    (F.restrOpen W₀).res h = F.res (inf_le_inf_right W₀ h) := rfl

section KerImCoker

variable {F G : OModulePresheaf π} (φ : Hom F G)

/-- The module structure on a submodule stable under multiplication by local sections. -/
@[reducible] def submoduleSections (U : V.Opens) {M : OModulePresheaf π} (p : Submodule R (M.obj U))
    (hp : ∀ (a : Γ(V, U)) (x : M.obj U), x ∈ p → a • x ∈ p) : Module Γ(V, U) p :=
  letI : SMul Γ(V, U) p := ⟨fun a x => ⟨a • x.1, hp a x.1 x.2⟩⟩
  Function.Injective.module Γ(V, U) ⟨⟨Subtype.val, rfl⟩, fun _ _ => rfl⟩ Subtype.val_injective
    (fun _ _ => rfl)

theorem range_smul_mem (U : V.Opens) (a : Γ(V, U)) (x : G.obj U) (hx : x ∈ LinearMap.range (φ.app
    U)) :
    a • x ∈ LinearMap.range (φ.app U) := by
  obtain ⟨s, rfl⟩ := hx; exact ⟨a • s, φ.app_smul U a s⟩

theorem ker_smul_mem (U : V.Opens) (a : Γ(V, U)) (x : F.obj U) (hx : x ∈ LinearMap.ker (φ.app U)) :
    a • x ∈ LinearMap.ker (φ.app U) :=
  LinearMap.mem_ker.mpr ((φ.app_smul U a x).trans (by rw [LinearMap.mem_ker.mp hx, smul_zero]))

/-- The pointwise kernel module presheaf of the morphism φ. -/
def ker : OModulePresheaf π where
  obj U := LinearMap.ker (φ.app U)
  module U := inferInstance
  moduleSections U := submoduleSections U _ (ker_smul_mem φ U)
  isScalarTower U := by
    let := Scheme.TwoAffineOpenCover.algebraOfHom π U
    let := submoduleSections U _ (ker_smul_mem φ U)
    exact ⟨fun r a x => Subtype.ext (smul_assoc r a x.1)⟩
  res h := (F.res h).restrict fun x hx => LinearMap.mem_ker.mpr <|
    (φ.naturality_apply h x).trans ((congrArg (G.res h) (LinearMap.mem_ker.mp hx)).trans (map_zero
      _))
  res_smul h a x := Subtype.ext (F.res_smul h a x.1)
  res_refl U := LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun (F.res_refl U) x.1)
  res_comp h h' := LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun (F.res_comp h h') x.1)

/-- The pointwise image module presheaf of the morphism φ. -/
def im : OModulePresheaf π where
  obj U := LinearMap.range (φ.app U)
  module U := inferInstance
  moduleSections U := submoduleSections U _ (range_smul_mem φ U)
  isScalarTower U := by
    let := Scheme.TwoAffineOpenCover.algebraOfHom π U
    let := submoduleSections U _ (range_smul_mem φ U)
    exact ⟨fun r a x => Subtype.ext (smul_assoc r a x.1)⟩
  res h := (G.res h).restrict fun x ⟨s, hs⟩ => ⟨F.res h s, hs ▸ φ.naturality_apply h s⟩
  res_smul h a x := Subtype.ext (G.res_smul h a x.1)
  res_refl U := LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun (G.res_refl U) x.1)
  res_comp h h' := LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun (G.res_comp h h') x.1)

/-- The local-sections module structure on the pointwise quotient by the image of φ. -/
@[reducible] def cokerModuleSections (U : V.Opens) : Module Γ(V, U) (G.obj U ⧸ LinearMap.range
  (φ.app U)) :=
  letI : SMul Γ(V, U) (G.obj U ⧸ LinearMap.range (φ.app U)) :=
    ⟨fun a => Quotient.map' (a • ·) fun x y hxy => (Submodule.quotientRel_def _).mpr <| by
      rw [← smul_sub]; exact range_smul_mem φ U a _ ((Submodule.quotientRel_def _).mp hxy)⟩
  Function.Surjective.module Γ(V, U) ⟨⟨Submodule.Quotient.mk, rfl⟩, fun _ _ => rfl⟩
    (Submodule.Quotient.mk_surjective _) (fun _ _ => rfl)

/-- The pointwise cokernel module presheaf of the morphism φ. -/
def coker : OModulePresheaf π where
  obj U := G.obj U ⧸ LinearMap.range (φ.app U)
  module U := inferInstance
  moduleSections U := cokerModuleSections φ U
  isScalarTower U := by
    let := Scheme.TwoAffineOpenCover.algebraOfHom π U
    let := cokerModuleSections φ U
    exact ⟨fun r a => Quotient.ind' fun x => congrArg Submodule.Quotient.mk (smul_assoc r a x)⟩
  res {U U'} h := Submodule.mapQ _ _ (G.res h) fun x ⟨s, hs⟩ => ⟨F.res h s, hs ▸
    φ.naturality_apply h s⟩
  res_smul {U U'} h a z := z.inductionOn' fun x => congrArg Submodule.Quotient.mk (G.res_smul h a x)
  res_refl U := LinearMap.ext fun z => z.inductionOn' fun x =>
    congrArg Submodule.Quotient.mk (LinearMap.congr_fun (G.res_refl U) x)
  res_comp {U U' U''} h h' := LinearMap.ext fun z => z.inductionOn' fun x =>
    congrArg Submodule.Quotient.mk (LinearMap.congr_fun (G.res_comp h h') x)

@[simp] theorem ker_obj (U : V.Opens) : (ker φ).obj U = LinearMap.ker (φ.app U) := rfl
@[simp] theorem im_obj (U : V.Opens) : (im φ).obj U = LinearMap.range (φ.app U) := rfl
@[simp] theorem coker_obj (U : V.Opens) : (coker φ).obj U = (G.obj U ⧸ LinearMap.range (φ.app U))
  := rfl
theorem ker_res_coe {U U' : V.Opens} (h : U ≤ U') (x : (ker φ).obj U') : ((ker φ).res h x).1 =
    F.res h x.1 := rfl
theorem im_res_coe {U U' : V.Opens} (h : U ≤ U') (x : (im φ).obj U') : ((im φ).res h x).1 = G.res
    h x.1 := rfl
theorem coker_res_mk {U U' : V.Opens} (h : U ≤ U') (x : G.obj U') :
    (coker φ).res h (Submodule.Quotient.mk x) = Submodule.Quotient.mk (G.res h x) := rfl
theorem ker_smul_coe (U : V.Opens) (a : Γ(V, U)) (x : (ker φ).obj U) : (a • x).1 = a • x.1 := rfl
theorem im_smul_coe (U : V.Opens) (a : Γ(V, U)) (x : (im φ).obj U) : (a • x).1 = a • x.1 := rfl
theorem coker_smul_mk (U : V.Opens) (a : Γ(V, U)) (x : G.obj U) :
    (a • (show (coker φ).obj U from Submodule.Quotient.mk x)) = (show (coker φ).obj U from
      Submodule.Quotient.mk (a • x)) := rfl

/-- The short exact sequence from the kernel of φ through F to the image of φ. -/
def kerImSES : SES (ker φ) F (im φ) where
  inc :=
    { app := fun U => (LinearMap.ker (φ.app U)).subtype,
      app_smul := fun _ _ _ => rfl,
      naturality := fun _ => rfl }
  proj := { app := fun U => (φ.app U).rangeRestrict
            app_smul := fun U a x => Subtype.ext (φ.app_smul U a x)
            naturality := fun h => LinearMap.ext fun x => Subtype.ext (φ.naturality_apply h x) }
  injective _ := Subtype.val_injective
  surjective U := LinearMap.surjective_rangeRestrict (φ.app U)
  exact U := (Submodule.range_subtype _).trans (LinearMap.ker_rangeRestrict (φ.app U)).symm

/-- The short exact sequence from the image of φ through G to the cokernel of φ. -/
def imCokerSES : SES (im φ) G (coker φ) where
  inc :=
    { app := fun U => (LinearMap.range (φ.app U)).subtype,
      app_smul := fun _ _ _ => rfl,
      naturality := fun _ => rfl }
  proj :=
    { app := fun U => (LinearMap.range (φ.app U)).mkQ,
      app_smul := fun _ _ _ => rfl,
      naturality := fun _ => rfl }
  injective _ := Subtype.val_injective
  surjective _ := Submodule.Quotient.mk_surjective _
  exact _ := (Submodule.range_subtype _).trans (Submodule.ker_mkQ _).symm

theorem kerImSES_inc_app (U : V.Opens) (x : (ker φ).obj U) : (kerImSES φ).inc.app U x = x.1 := rfl
theorem kerImSES_proj_app (U : V.Opens) (x : F.obj U) : ((kerImSES φ).proj.app U x).1 = φ.app U x
    := rfl
theorem imCokerSES_inc_app (U : V.Opens) (x : (im φ).obj U) : (imCokerSES φ).inc.app U x = x.1 :=
    rfl
theorem imCokerSES_proj_app (U : V.Opens) (x : G.obj U) : (imCokerSES φ).proj.app U x = (show
    (coker φ).obj U from Submodule.Quotient.mk x) := rfl

end KerImCoker

section Pushforward

variable {Z : Scheme.{u}} (i : Z ⟶ V)

theorem appLE_algebraMap (U : V.Opens) (r : R) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (i ≫ π) (i ⁻¹ᵁ U)
    (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom (algebraMap R Γ(V, U) r) = algebraMap R Γ(Z, i ⁻¹ᵁ U) r := by
  change (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom ((π.appLE ⊤ U le_top).hom _) = ((i ≫ π).appLE ⊤ (i ⁻¹ᵁ
    U) le_top).hom _
  rw [← CommRingCat.comp_apply]
  erw [Scheme.Hom.appLE_comp_appLE]

variable (π) in
/-- Push a module presheaf forward by evaluating its sections on inverse images of opens. -/
def pushforward (H : OModulePresheaf (i ≫ π)) : OModulePresheaf π where
  obj U := H.obj (i ⁻¹ᵁ U)
  module U := inferInstance
  moduleSections U := Module.compHom _ (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom
  isScalarTower U := by
    let := Scheme.TwoAffineOpenCover.algebraOfHom π U
    let := Scheme.TwoAffineOpenCover.algebraOfHom (i ≫ π) (i ⁻¹ᵁ U)
    let : Module Γ(V, U) (H.obj (i ⁻¹ᵁ U)) := Module.compHom _ (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom
    refine ⟨fun r a x => ?_⟩
    change (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom (r • a) • x = r • ((i.appLE U (i ⁻¹ᵁ U) le_rfl).hom a
      • x)
    rw [Algebra.smul_def, map_mul, mul_smul, appLE_algebraMap, algebraMap_smul]
  res h := H.res ((Opens.map i.base).monotone h)
  res_smul {U U'} h a x := by
    change H.res _ ((i.appLE U' (i ⁻¹ᵁ U') le_rfl).hom a • x)
      = (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom ((V.presheaf.map (homOfLE h).op).hom a) • H.res
        ((Opens.map i.base).monotone h) x
    rw [H.res_smul, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply (f := V.presheaf.map _),
      Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  res_refl U := H.res_refl (i ⁻¹ᵁ U)
  res_comp h h' := H.res_comp ((Opens.map i.base).monotone h) ((Opens.map i.base).monotone h')

@[simp] theorem pushforward_obj (H : OModulePresheaf (i ≫ π)) (U : V.Opens) : (pushforward π i
  H).obj U = H.obj (i ⁻¹ᵁ U) := rfl
theorem pushforward_res (H : OModulePresheaf (i ≫ π)) {U U' : V.Opens} (h : U ≤ U') :
    (pushforward π i H).res h = H.res ((Opens.map i.base).monotone h) := rfl
theorem pushforward_smul (H : OModulePresheaf (i ≫ π)) (U : V.Opens) (a : Γ(V, U)) (x : H.obj (i
    ⁻¹ᵁ U)) :
    (a • (show (pushforward π i H).obj U from x)) = (show (pushforward π i H).obj U from (i.appLE
      U (i ⁻¹ᵁ U) le_rfl).hom a • x) := rfl

variable (π) in
/-- The pushforward of the unit module presheaf along i. -/
abbrev pushforwardUnit : OModulePresheaf π := pushforward π i (unit (i ≫ π))

end Pushforward

section AffHoms

variable (F : OModulePresheaf π)

/-- The affine morphism from the zero presheaf to F. -/
def AffHom.zeroFrom : AffHom (zero π) F where
  app _ := 0
  app_smul _ _ _ := by simp
  naturality _ := by ext; simp

/-- The affine morphism from F to the zero presheaf. -/
def AffHom.zeroTo : AffHom F (zero π) where
  app _ := 0
  app_smul _ _ _ := Subsingleton.elim _ _
  naturality _ := LinearMap.ext fun _ => Subsingleton.elim _ _

/-- The affine short exact sequence with zero kernel and identity projection on F. -/
def AffSES.zeroLeft : AffSES (zero π) F F where
  inc := AffHom.zeroFrom F
  proj := AffHom.id F
  injective _ := fun _ _ _ => Subsingleton.elim _ _
  surjective _ := Function.surjective_id
  exact _ := by
    change LinearMap.range (0 : _ →ₗ[R] _) = LinearMap.ker LinearMap.id
    rw [LinearMap.range_zero, LinearMap.ker_id]

/-- Evaluation at the unique coordinate of the first power of F. -/
def AffHom.powOne : AffHom (F.pow 1) F where
  app U := LinearMap.proj (R := R) (φ := fun _ : Fin 1 => F.obj U.1) 0
  app_smul _ _ _ := rfl
  naturality _ := rfl

/-- The affine short exact sequence identifying the first power of F with F. -/
def AffSES.powOne : AffSES (F.pow 1) F (zero π) where
  inc := AffHom.powOne F
  proj := AffHom.zeroTo F
  injective _ := fun f g h => funext fun j => Fin.fin_one_eq_zero j ▸ h
  surjective _ := fun x => ⟨0, Subsingleton.elim _ _⟩
  exact U := by
    apply le_antisymm
    · exact fun x _ => LinearMap.mem_ker.mpr (Subsingleton.elim _ _)
    · exact fun x _ => ⟨fun _ => x, rfl⟩

end AffHoms

/--
An integral support piece, its pushed-forward module presheaf, and an exact sequence with smaller
supported quotient.
-/
structure DevissageStep (F : OModulePresheaf π) (Y : Closeds V) where
  /-- The closed integral support piece selected inside Y. -/
  Z₀ : Closeds V
  /-- The subscheme defined by the vanishing ideal of Z₀ is integral. -/
  isIntegral : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme
  /-- The selected support piece is contained in Y. -/
  Z₀_le : Z₀ ≤ Y
  /-- The selected support piece is nonempty. -/
  Z₀_nonempty : (Z₀ : Set V).Nonempty
  /-- The module presheaf on the selected integral subscheme. -/
  H : OModulePresheaf ((Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι ≫ π)
  /-- The pushforward of H is coherent. -/
  isCoherent_pushforward : (pushforward π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι
    H).IsCoherent
  /-- The pushforward of H is quasicoherent. -/
  isQuasicoherent_pushforward : (pushforward π (Scheme.IdealSheafData.vanishingIdeal
    Z₀).subschemeι H).IsQuasicoherent
  /-- The pushforward of H is supported inside Z₀. -/
  supportedIn_pushforward : (pushforward π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι
    H).SupportedIn Z₀
  /-- The quotient module presheaf in the dévissage sequence. -/
  G₃ : OModulePresheaf π
  /-- The affine short exact sequence from the pushforward of H through F to G₃. -/
  ses : AffSES (pushforward π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι H) F G₃
  /-- A strictly smaller closed set supporting the quotient. -/
  Z₁ : Closeds V
  /-- The closed support of the quotient is strictly smaller than Y. -/
  Z₁_lt : Z₁ < Y
  /-- The quotient module presheaf is coherent. -/
  isCoherent_G₃ : G₃.IsCoherent
  /-- The quotient module presheaf is quasicoherent. -/
  isQuasicoherent_G₃ : G₃.IsQuasicoherent
  /-- The quotient module presheaf is supported inside Z₁. -/
  supportedIn_G₃ : G₃.SupportedIn Z₁

/--
The existence of a dévissage step for each coherent quasicoherent presheaf annihilated by its
nonempty support ideal.
-/
def HasDevissageStep : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))
    [IsSeparated π]
    [IsNoetherian V] (F : OModulePresheaf π) (_ : F.IsCoherent) (_ : F.IsQuasicoherent) (Y :
      Closeds V)
    (_ : (Y : Set V).Nonempty) (_ : F.SupportedIn Y)
    (_ : ∀ U : V.affineOpens, ∀ a ∈ (Scheme.IdealSheafData.vanishingIdeal Y).ideal U, ∀ x : F.obj
      U.1, a • x = 0),
    Nonempty (F.DevissageStep Y)

end OModulePresheaf

end AlgebraicGeometry

end

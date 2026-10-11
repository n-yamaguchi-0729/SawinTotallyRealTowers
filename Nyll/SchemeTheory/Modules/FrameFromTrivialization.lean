/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Modules.Invertible
import Nyll.SchemeTheory.Modules.Frames

/-!
# Frames obtained from a pullback trivialization

A trivialization on an open subscheme gives compatible local generators and a section
that is a frame on that open.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.Limits

noncomputable section

namespace PresheafOfModules
open _root_.PresheafOfModules
open _root_.PresheafOfModules

namespace FrameBridge

open Opposite

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (F : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))

/-- Compatible generators trivializing the presheaf on objects reached from `X₀`. -/
structure TrivializationBelow (X₀ : Cᵒᵖ) where
  /-- The generator associated to an arrow from `X₀`. -/
  gen : ∀ {Y : Cᵒᵖ} (_ : X₀ ⟶ Y), F.obj Y
  /-- The generators are preserved by the presheaf restriction maps. -/
  compat : ∀ {Y Z : Cᵒᵖ} (f : X₀ ⟶ Y) (g : Y ⟶ Z), F.map g (gen f) = gen (f ≫ g)
  /-- Scalar multiplication by each generator is bijective. -/
  bij : ∀ {Y : Cᵒᵖ} (f : X₀ ⟶ Y), Function.Bijective (fun a : R.obj Y => a • gen f)

end FrameBridge

end PresheafOfModules

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

namespace FrameBridge

open TopologicalSpace Opposite PresheafOfModules.FrameBridge

variable {X : Scheme.{u}}

variable (U : X.Opens)

/-- The ring-sheaf morphism used to restrict module sheaves to the open subscheme. -/
noncomputable def restrictRingCatSheafHom : (U : Scheme.{u}).ringCatSheaf ⟶
    (U.ι.opensFunctor.sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology (U : Scheme.{u})) (Opens.grothendieckTopology X)).obj
        X.ringCatSheaf :=
  ⟨𝟙 _⟩

/-- Restriction expressed as pushforward along the inclusion of the open indexing categories. -/
noncomputable def restrictFunctor' : X.Modules ⥤ (U : Scheme.{u}).Modules :=
  SheafOfModules.pushforward (restrictRingCatSheafHom U)

lemma restrictFunctor'_eq : restrictFunctor' U = Modules.restrictFunctor U.ι := by
  dsimp only [restrictFunctor', Modules.restrictFunctor, restrictRingCatSheafHom]
  congr 2
  ext V : 2
  change 𝟙 _ = (forget₂ CommRingCat RingCat).map (U.ι.appIso V.unop).inv
  rw [Scheme.Opens.ι_appIso]
  rfl

/-- The canonical comparison between the restriction functor and pullback to the open. -/
noncomputable def restrictFunctor'IsoPullback : restrictFunctor' U ≅ Modules.pullback U.ι :=
  eqToIso (restrictFunctor'_eq U) ≪≫ restrictFunctorIsoPullback U.ι

variable {U} (L : X.Modules)

lemma image_preimage_of_le {V : X.Opens} (h : V ≤ U) : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr h

section

variable (e : (restrictFunctor' U).obj L ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)

/-- The generator obtained by transporting one through the inverse trivialization. -/
noncomputable def gen₀ (W : (U : Scheme.{u}).Opens) : L.val.obj (op (U.ι ''ᵁ W)) :=
  (e.inv.val.app (op W)).hom (1 : Γ(U, W))

lemma gen₀_spec (W : (U : Scheme.{u}).Opens) (b : Γ(X, U.ι ''ᵁ W)) :
    (e.inv.val.app (op W)).hom b = b • (show Γ(L, U.ι ''ᵁ W) from gen₀ L e W) := by
  have h := (e.inv.val.app (op W)).hom.map_smul b (1 : Γ(U, W))
  have hunit : (show Γ(U, W) from b) • (1 : Γ(U, W)) = b :=
    (smul_eq_mul (show Γ(U, W) from b) (1 : Γ(U, W))).trans (mul_one _)
  exact (congrArg (e.inv.val.app (op W)).hom hunit).symm.trans h

lemma gen₀_bijective (W : (U : Scheme.{u}).Opens) :
    Function.Bijective (fun b : Γ(X, U.ι ''ᵁ W) => b • (show Γ(L, U.ι ''ᵁ W) from gen₀ L e W)) := by
  have h : Function.Bijective ((e.inv.val.app (op W)).hom) := by
    refine Function.bijective_iff_has_inverse.2 ⟨(e.hom.val.app (op W)).hom, fun b => ?_, fun m =>
        ?_⟩
    · exact congr($(e.inv_hom_id).val.app (op W) |>.hom b)
    · exact congr($(e.hom_inv_id).val.app (op W) |>.hom m)
  exact (funext (gen₀_spec L e W) ▸ h :)

lemma gen₀_map {W W' : (U : Scheme.{u}).Opens} (i : W' ⟶ W) :
    L.val.map (U.ι.opensFunctor.map i).op (gen₀ L e W) = gen₀ L e W' := by
  have := PresheafOfModules.naturality_apply e.inv.val i.op (1 : Γ(U, W))
  rw [show ((SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf).val.map i.op) (1 : Γ(U, W)) =
    (1 : Γ(U, W')) from ((U : Scheme.{u}).presheaf.map i.op).hom.map_one] at this
  exact this.symm

omit e in
lemma bijective_smul_map_eqToHom {A B : X.Opens} (q : A = B) (t : L.val.obj (op A))
    (h : Function.Bijective (fun b : Γ(X, A) => b • (show Γ(L, A) from t))) :
    Function.Bijective (fun a : Γ(X, B) =>
      a • (show Γ(L, B) from L.val.map (eqToHom q.symm : B ⟶ A).op t)) := by
  subst q
  have e1 : L.val.map (eqToHom (rfl : A = A) : A ⟶ A).op t = t := by
    rw [eqToHom_refl, op_id]
    change (L.val.presheaf.map (𝟙 (op A))) t = t
    rw [L.val.presheaf.map_id]
    rfl
  simpa only [e1] using h

/-- The compatible generators on opens contained in the trivializing open `U`. -/
noncomputable def trivializationBelow : TrivializationBelow L.val (op U) where
  gen {Y} f := L.val.map (eqToHom (image_preimage_of_le (U := U) f.unop.le).symm :
      Y.unop ⟶ U.ι ''ᵁ (U.ι ⁻¹ᵁ Y.unop)).op (gen₀ L e (U.ι ⁻¹ᵁ Y.unop))
  compat {Y Z} f g := by
    have hle : U.ι ⁻¹ᵁ Z.unop ≤ U.ι ⁻¹ᵁ Y.unop := fun x hx => g.unop.le hx
    dsimp only
    rw [← gen₀_map L e (homOfLE hle)]
    erw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
    exact congrFun (congrArg
      (fun φ : (op (U.ι ''ᵁ (U.ι ⁻¹ᵁ Y.unop)) ⟶ Z) =>
        ((L.val.map φ).hom : L.val.obj (op (U.ι ''ᵁ (U.ι ⁻¹ᵁ Y.unop))) → L.val.obj Z))
      (Subsingleton.elim _ _)) _
  bij {Y} f := bijective_smul_map_eqToHom L (image_preimage_of_le (U := U) f.unop.le) _
    (gen₀_bijective L e _)

end

end FrameBridge

open FrameBridge in
theorem exists_isFrameOn_of_pullback_iso_unit {X : Scheme.{u}} {M : X.Modules} (U : X.Opens)
    (eU : (Modules.pullback U.ι).obj M ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) :
    ∃ s : Γ(M, U), IsFrameOn s U := by
  let e : (restrictFunctor' U).obj M ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf :=
    (restrictFunctor'IsoPullback U).app M ≪≫ eU
  let D := trivializationBelow M e
  refine ⟨D.gen (𝟙 (Opposite.op U)), ?_⟩
  intro W hWU _
  have hc : M.presheaf.map (homOfLE hWU).op (D.gen (𝟙 (Opposite.op U))) = D.gen (homOfLE hWU).op :=
      by
    have h := D.compat (𝟙 (Opposite.op U)) (homOfLE hWU).op
    rw [Category.id_comp] at h
    exact h
  simp only [hc]
  exact D.bij (homOfLE hWU).op

end AlgebraicGeometry.Scheme.Modules

end

open _root_.AlgebraicGeometry in
open Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit.AlgebraicGeometry.Scheme in
theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit
    {X : Scheme.{u}} {M : X.Modules} (U : X.Opens)
    (eU : (Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) :
    ∃ s : Γ(M, U), Scheme.Modules.IsFrameOn s U :=
  Modules.exists_isFrameOn_of_pullback_iso_unit U eU
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit
end ProofImplementation

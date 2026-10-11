/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted proof at pinned revision
aa2d8b34692b16c70f699536de0d8e75b9a3e9ef:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_associator_hom_app_tensorSections_monoidalV2.lean
Upstream NOTICE and per-file ATTRIBUTION (including earlier FLT and Mathlib notices):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
See SchemeTheory/ANTHROPIC_FLT_SOURCE.md for retained notices.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Modules.TensorSectionMaps
import Nyll.SchemeTheory.Modules.TensorSectionSheafification
import Nyll.SchemeTheory.Modules.TensorSections
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.SchemeTheory.Modules.SheafificationMonoidal

/-!
# The associator on tensor sections

The formula is proved through the monoidal sheafification adjunction and naturality.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules
namespace TensorSectionAssociator

open Opposite TensorProduct

variable {X : Scheme.{u}}

private abbrev ι (X : Scheme.{u}) : X.Modules ⥤ X.PresheafOfModules :=
  SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property

private abbrev adj (X : Scheme.{u}) : Modules.sheafify X ⊣ ι X :=
  SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property

private abbrev eta (P : X.PresheafOfModules) (U : X.Opens) (x : P.obj (op U)) :
    Γ((Modules.sheafify X).obj P, U) :=
  ((adj X).unit.app P).app (op U) x

private lemma comp_app_apply {A B C : X.Modules} (f : A ⟶ B) (g : B ⟶ C)
    (U : X.Opens) (a : Γ(A, U)) :
    (f ≫ g).app U a = g.app U (f.app U a) := rfl

private lemma id_app_apply {A : X.Modules} (U : X.Opens) (a : Γ(A, U)) :
    (𝟙 A : A ⟶ A).app U a = a := rfl

private lemma iso_app_injective {A B : X.Modules} (e : A ≅ B) (U : X.Opens) :
    Function.Injective (e.hom.app U) := by
  intro a b h
  have h2 := congrArg (e.inv.app U) h
  rw [← comp_app_apply, ← comp_app_apply, e.hom_inv_id, id_app_apply, id_app_apply] at h2
  exact h2

private lemma whiskerLeft_app_tensorSections {L M M' : X.Modules} (f : M ⟶ M')
    {U : X.Opens} (s : Γ(L, U)) (t : Γ(M, U)) :
    (L ◁ f).app U (tensorSections s t) = tensorSections s (f.app U t) := by
  rw [← id_tensorHom, tensorHom_app_tensorSections]
  rfl

private lemma whiskerRight_app_tensorSections {L L' M : X.Modules} (f : L ⟶ L')
    {U : X.Opens} (s : Γ(L, U)) (t : Γ(M, U)) :
    (f ▷ M).app U (tensorSections s t) = tensorSections (f.app U s) t := by
  rw [← tensorHom_id, tensorHom_app_tensorSections]
  rfl

private lemma sheafify_map_app_eta {P P' : X.PresheafOfModules} (g : P ⟶ P')
    (U : X.Opens) (z : P.obj (op U)) :
    ((Modules.sheafify X).map g).app U (eta P U z) = eta P' U (g.app (op U) z) := by
  have h := (adj X).unit.naturality g
  exact (congr($(h.symm).app (op U) z) :)

private lemma counit_app_eta (N : X.Modules) (U : X.Opens) (y : Γ(N, U)) :
    Scheme.Modules.Hom.app (M := (Modules.sheafify X).obj ((ι X).obj N)) (N := N)
      ((adj X).counit.app N) U (eta ((ι X).obj N) U y) = y := by
  have h := (adj X).right_triangle_components N
  exact (congr($(h).app (op U) y) :)

private theorem associator_sheafify (P Q R : X.PresheafOfModules) (U : X.Opens)
    (x : P.obj (op U)) (y : Q.obj (op U)) (z : R.obj (op U)) :
    (α_ ((Modules.sheafify X).obj P) ((Modules.sheafify X).obj Q)
        ((Modules.sheafify X).obj R)).hom.app U
        (tensorSections (tensorSections (eta P U x) (eta Q U y)) (eta R U z)) =
      tensorSections (eta P U x) (tensorSections (eta Q U y) (eta R U z)) := by
  let : Module Γ(X, U) (P.obj (op U)) := (P.obj (op U)).isModule
  let : Module Γ(X, U) (Q.obj (op U)) := (Q.obj (op U)).isModule
  let : Module Γ(X, U) (R.obj (op U)) := (R.obj (op U)).isModule
  let F : X.PresheafOfModules ⥤ X.Modules := Modules.sheafify X
  apply iso_app_injective
    (whiskerLeftIso (F.obj P) (Functor.Monoidal.μIso F Q R) ≪≫
      Functor.Monoidal.μIso F P (Q ⊗ R)) U
  have hassoc := Functor.LaxMonoidal.associativity F P Q R
  have hPQ := sheafify_mu_app_tensorSections (X := X) P Q (U := U) x y
  have hQR := sheafify_mu_app_tensorSections (X := X) Q R (U := U) y z
  have hPQR := sheafify_mu_app_tensorSections (X := X) (P ⊗ Q) R (U := U)
    (x ⊗ₜ[Γ(X, U)] y) z
  have hPQR' := sheafify_mu_app_tensorSections (X := X) P (Q ⊗ R) (U := U)
    x (y ⊗ₜ[Γ(X, U)] z)
  rw [Iso.trans_hom, whiskerLeftIso_hom, Functor.Monoidal.μIso_hom, Functor.Monoidal.μIso_hom]
  rw [← comp_app_apply, ← hassoc, comp_app_apply, comp_app_apply, whiskerRight_app_tensorSections]
  erw [hPQ, hPQR, sheafify_map_app_eta]
  rw [comp_app_apply, whiskerLeft_app_tensorSections]
  erw [hQR, hPQR']
  rfl
end TensorSectionAssociator

variable {X : Scheme.{u}}

open TensorSectionAssociator in
/-- The associator sends a tensor of three local sections to the other parenthesization. -/
theorem associator_hom_app_tensorSections {L M N : X.Modules} {U : X.Opens}
    (l : Γ(L, U)) (m : Γ(M, U)) (n : Γ(N, U)) :
    (α_ L M N).hom.app U (tensorSections (L := L ⊗ M) (M := N) (tensorSections l m) n) =
      tensorSections (L := L) (M := M ⊗ N) l (tensorSections m n) := by
  let εL : (Modules.sheafify X).obj ((ι X).obj L) ⟶ L := (adj X).counit.app L
  let εM : (Modules.sheafify X).obj ((ι X).obj M) ⟶ M := (adj X).counit.app M
  let εN : (Modules.sheafify X).obj ((ι X).obj N) ⟶ N := (adj X).counit.app N
  have hnat := MonoidalCategory.associator_naturality εL εM εN
  have hl : εL.app U (eta ((ι X).obj L) U l) = l := counit_app_eta L U l
  have hm : εM.app U (eta ((ι X).obj M) U m) = m := counit_app_eta M U m
  have hn : εN.app U (eta ((ι X).obj N) U n) = n := counit_app_eta N U n
  have h1 : ((εL ⊗ₘ εM) ⊗ₘ εN).app U
      (tensorSections (tensorSections (eta ((ι X).obj L) U l) (eta ((ι X).obj M) U m))
        (eta ((ι X).obj N) U n)) =
      tensorSections (tensorSections l m) n := by
    rw [tensorHom_app_tensorSections, tensorHom_app_tensorSections, hl, hm, hn]
  have h2 : (εL ⊗ₘ (εM ⊗ₘ εN)).app U
      (tensorSections (eta ((ι X).obj L) U l)
        (tensorSections (eta ((ι X).obj M) U m) (eta ((ι X).obj N) U n))) =
      tensorSections l (tensorSections m n) := by
    rw [tensorHom_app_tensorSections, tensorHom_app_tensorSections, hl, hm, hn]
  have hα := associator_sheafify ((ι X).obj L) ((ι X).obj M) ((ι X).obj N) U l m n
  rw [← h1, ← comp_app_apply, hnat, comp_app_apply, hα, h2]

end AlgebraicGeometry.Scheme.Modules

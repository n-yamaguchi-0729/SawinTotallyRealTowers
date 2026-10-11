/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Sites.Pretopology
import Nyll.SchemeTheory.Modules.Frames
import Nyll.SchemeTheory.Modules.PresheafInternalHom
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.SchemeTheory.Modules.TensorSections
import Nyll.SchemeTheory.Modules.SheafificationMonoidal

/-!
# Tensor products of local frames

The presheaf tensor comparison carries tensor products of generators to frames.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsFrameOn_tensorSections_monoidalV2

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.Opposite
open _root_.TensorProduct
open _root_.TopologicalSpace


noncomputable section

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (Scheme.Hom Scheme.Hom.image_preimage_eq_opensRange_inf Scheme
  Scheme.Modules Scheme.Opens Scheme.Opens.ι_image_top Scheme.Modules.map_smul
  Scheme.Opens.opensRange_ι Scheme.Modules.tensorSections Scheme.Modules.IsFrameOn)

namespace Scheme

export _root_.AlgebraicGeometry.Scheme (forget ringCatSheaf Hom Γ
  Hom.image_preimage_eq_opensRange_inf Modules Opens Opens.ι_image_top grothendieckTopology
  Modules.map_smul Opens.opensRange_ι restrict PresheafOfModules Modules.tensorSections
  Modules.map_homOfLE_tensorSections Modules.IsFrameOn)

namespace Modules

export _root_.AlgebraicGeometry.Scheme.Modules (hom_ext toPresheaf pushforward presheaf Hom
  restrict map_smul tensor tensorSectionsHom tensorSections map_homOfLE_tensorSections IsFrameOn)


open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry


namespace FrameTensor

variable {X : Scheme.{u}}

private local instance frameTensorPresheafModule (P : X.PresheafOfModules) (W : X.Opens) :
    Module Γ(X, W) (P.obj (op W)) := (P.obj (op W)).isModule

lemma bijective_smul_tmul {R : Type*} [CommRing R] {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B] (a : A) (b : B)
    (ha : Function.Bijective fun r : R => r • a) (hb : Function.Bijective fun r : R => r • b) :
    Function.Bijective fun r : R => r • (a ⊗ₜ[R] b) := by
  let eA : R ≃ₗ[R] A := LinearEquiv.ofBijective (LinearMap.toSpanSingleton R A a) ha
  let eB : R ≃ₗ[R] B := LinearEquiv.ofBijective (LinearMap.toSpanSingleton R B b) hb
  let e : R ≃ₗ[R] A ⊗[R] B := (TensorProduct.lid R R).symm ≪≫ₗ TensorProduct.congr eA eB
  have he : (fun r : R => r • (a ⊗ₜ[R] b)) = e := by
    funext r
    change r • (a ⊗ₜ[R] b) = TensorProduct.congr eA eB ((TensorProduct.lid R R).symm r)
    rw [TensorProduct.lid_symm_apply, TensorProduct.congr_tmul]
    change r • (a ⊗ₜ[R] b) = ((1 : R) • a) ⊗ₜ[R] (r • b)
    rw [one_smul, TensorProduct.tmul_smul]
  rw [he]
  exact e.bijective

section locbij

variable (L M : X.Modules)

/-- Applies the canonical tensor comparison to a local presheaf tensor. -/
def tsApp (W : X.Opens) (z : (L.val ⊗ M.val).obj (op W)) : Γ(L ⊗ M, W) :=
  DFunLike.coe (α := ((L.val ⊗ M.val).obj (op W) :)) (β := fun _ => Γ(L ⊗ M, W))
    ((tensorSectionsHom L M).app (op W)).hom z

variable {L M}

lemma tensorSections_eq_tsApp {W : X.Opens} (s : Γ(L, W)) (t : Γ(M, W)) :
    Modules.tensorSections s t = tsApp L M W ((s : L.val.obj (op W)) ⊗ₜ[Γ(X, W)] (t : M.val.obj (op
      W))) :=
  rfl

lemma tsApp_smul {W : X.Opens} (g : Γ(X, W)) (z : (L.val ⊗ M.val).obj (op W)) :
    tsApp L M W (g • z) = g • tsApp L M W z := by
  exact ((tensorSectionsHom L M).app (op W)).hom.map_smul g z

lemma tsApp_add {W : X.Opens} (z z' : (L.val ⊗ M.val).obj (op W)) :
    tsApp L M W (z + z') = tsApp L M W z + tsApp L M W z' := by
  exact ((tensorSectionsHom L M).app (op W)).hom.map_add z z'

lemma map_tsApp {W W' : X.Opens} (i : W' ⟶ W) (z : (L.val ⊗ M.val).obj (op W)) :
    (L ⊗ M).presheaf.map i.op (tsApp L M W z) = tsApp L M W' ((L.val ⊗ M.val).map i.op z) :=
  (PresheafOfModules.naturality_apply (tensorSectionsHom L M) i.op z).symm

lemma map_smul_tmul {W W' : X.Opens} (i : W' ⟶ W) (g : Γ(X, W)) (s : Γ(L, W)) (t : Γ(M, W)) :
    (L.val ⊗ M.val).map i.op (g • ((s : L.val.obj (op W)) ⊗ₜ[Γ(X, W)] (t : M.val.obj (op W)))) =
      X.presheaf.map i.op g • ((L.presheaf.map i.op s : L.val.obj (op W')) ⊗ₜ[Γ(X, W')]
        (M.presheaf.map i.op t : M.val.obj (op W'))) := by
  erw [PresheafOfModules.map_smul, PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul]
  rfl

variable (L M) in
lemma W_tensorSectionsHom :
    (Opens.grothendieckTopology X).W ((PresheafOfModules.toPresheaf _).map (tensorSectionsHom L
        M)) := by
  dsimp only [tensorSectionsHom]
  erw [Functor.map_comp]
  apply MorphismProperty.comp_mem
  · erw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact GrothendieckTopology.W_toSheafify _ _
  · let e := (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).mapIso
      ((SheafOfModules.toPMod (J := Opens.grothendieckTopology X)
        X.sheaf.obj X.ringCatSheaf.property : X.Modules ⥤ X.PresheafOfModules).mapIso
          (tensorIsoSheafify L M))
    exact ((Opens.grothendieckTopology X).W_iff e.hom).2
      (((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapIso e).isIso_hom)

scoped instance isLocallySurjective_tensorSectionsHom : Presheaf.IsLocallySurjective
  (Opens.grothendieckTopology X)
    ((PresheafOfModules.toPresheaf _).map (tensorSectionsHom L M)) :=
  (((Opens.grothendieckTopology X).W_iff_isLocallyBijective _).1 (W_tensorSectionsHom L M)).2

scoped instance isLocallyInjective_tensorSectionsHom : Presheaf.IsLocallyInjective
  (Opens.grothendieckTopology X)
    ((PresheafOfModules.toPresheaf _).map (tensorSectionsHom L M)) :=
  (((Opens.grothendieckTopology X).W_iff_isLocallyBijective _).1 (W_tensorSectionsHom L M)).1

lemma exists_local_preimage {W : X.Opens} (y : Γ(L ⊗ M, W)) {x : X} (hx : x ∈ W) :
    ∃ (W' : X.Opens) (i : W' ⟶ W), x ∈ W' ∧ ∃ z : (L.val ⊗ M.val).obj (op W'),
      tsApp L M W' z = (L ⊗ M).presheaf.map i.op y := by
  have h := Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
    ((PresheafOfModules.toPresheaf _).map (tensorSectionsHom L M)) y
  obtain ⟨W', i, ⟨z, hz⟩, hxW'⟩ := h x hx
  exact ⟨W', i, hxW', z, hz⟩

lemma exists_local_eq {W : X.Opens} (z₁ z₂ : (L.val ⊗ M.val).obj (op W))
    (h : tsApp L M W z₁ = tsApp L M W z₂) {x : X} (hx : x ∈ W) :
    ∃ (W' : X.Opens) (i : W' ⟶ W), x ∈ W' ∧ (L.val ⊗ M.val).map i.op z₁ = (L.val ⊗ M.val).map i.op
      z₂ := by
  have hm := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X)
    ((PresheafOfModules.toPresheaf _).map (tensorSectionsHom L M)) z₁ z₂ h
  obtain ⟨W', i, hi, hxW'⟩ := hm x hx
  exact ⟨W', i, hxW', hi⟩

end locbij

section restrict

variable (W : X.Opens)

/-- The identity ring-sheaf map used to restrict to an open subset. -/
def restrictRingCatSheafHom : (W : Scheme.{u}).ringCatSheaf ⟶
    (W.ι.opensFunctor.sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology (W : Scheme.{u})) (Opens.grothendieckTopology X)).obj
        X.ringCatSheaf :=
  ⟨𝟙 _⟩

/-- Restricts a module sheaf to an open subset by pushforward along the open inclusion. -/
def restrictFunctor' : X.Modules ⥤ (W : Scheme.{u}).Modules :=
  SheafOfModules.pushforward (restrictRingCatSheafHom W)

lemma image_le (W' : (W : Scheme.{u}).Opens) : W.ι ''ᵁ W' ≤ W :=
  (W.ι.image_le_opensRange W').trans_eq W.opensRange_ι

variable {W} in
lemma image_preimage_of_le {W₂ : X.Opens} (h : W₂ ≤ W) : W.ι ''ᵁ (W.ι ⁻¹ᵁ W₂) = W₂ := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr h

/-- Views a function on an open subscheme as a function on its image. -/
abbrev secX (W' : (W : Scheme.{u}).Opens) (a : Γ(W, W')) : Γ(X, W.ι ''ᵁ W') := a

end restrict

section smulHom

variable (N : X.Modules) (W : X.Opens) (τ : Γ(N, W))

/-- The map from the unit module sending functions to multiples of a section. -/
def smulSectionHom : SheafOfModules.unit ((W : X.Opens) : Scheme.{u}).ringCatSheaf ⟶
    (restrictFunctor' W).obj N :=
  ⟨{ app := fun W' => (show
        (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf).val.obj W' ⟶
          ((restrictFunctor' W).obj N).val.obj W' from
      ConcreteCategory.ofHom
        (C := ModuleCat ((W : Scheme.{u}).ringCatSheaf.obj.obj W'))
        (X := (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf).val.obj W')
        (Y := ((restrictFunctor' W).obj N).val.obj W')
        { toFun := fun a =>
            (secX W W'.unop a • N.presheaf.map (homOfLE (image_le W W'.unop)).op τ : Γ(N, W.ι
                ''ᵁ W'.unop))
          map_add' := fun a b => add_smul (secX W W'.unop a) (secX W W'.unop b)
            (N.presheaf.map (homOfLE (image_le W W'.unop)).op τ : Γ(N, W.ι ''ᵁ W'.unop))
          map_smul' := fun r a => mul_smul (secX W W'.unop r) (secX W W'.unop a)
            (N.presheaf.map (homOfLE (image_le W W'.unop)).op τ : Γ(N, W.ι ''ᵁ W'.unop)) })
     naturality := fun {W' W''} i => by
       apply ModuleCat.hom_ext
       apply LinearMap.ext
       intro a
       change secX W W''.unop (X.presheaf.map (W.ι.opensFunctor.map i.unop).op (secX W W'.unop a)) •
           N.presheaf.map (homOfLE (image_le W W''.unop)).op τ =
         N.presheaf.map (W.ι.opensFunctor.map i.unop).op
           (secX W W'.unop a • N.presheaf.map (homOfLE (image_le W W'.unop)).op τ)
       rw [Scheme.Modules.map_smul]
       congr 1
       change _ = (N.presheaf.map _ ≫ N.presheaf.map _) τ
       rw [← N.presheaf.map_comp]
       rfl }⟩

lemma smulSectionHom_app_apply (W' : (((W : X.Opens) : Scheme.{u}).Opens)ᵒᵖ) (a : Γ(W, W'.unop)) :
    (smulSectionHom N W τ).val.app W' a =
      secX W W'.unop a • N.presheaf.map (homOfLE (image_le W W'.unop)).op τ := rfl

variable {N W τ}

lemma bijective_smul_map_iff_of_eq {A B : X.Opens} (q : A = B) (τ : Γ(N, B)) :
    (Function.Bijective fun a : Γ(X, A) => a • N.presheaf.map (homOfLE q.le).op τ) ↔
      Function.Bijective fun g : Γ(X, B) => g • τ := by
  subst q
  have e : N.presheaf.map (homOfLE (le_refl A)).op τ = τ := by
    rw [show (homOfLE (le_refl A) : A ⟶ A) = 𝟙 A from rfl, op_id, N.presheaf.map_id]
    rfl
  simp only [e]

lemma bijective_smul_of_isIso (h : IsIso (smulSectionHom N W τ)) :
    Function.Bijective fun g : Γ(X, W) => g • τ := by
  let e := asIso (smulSectionHom N W τ)
  have hb : Function.Bijective (e.hom.val.app (op ⊤)).hom := by
    refine Function.bijective_iff_has_inverse.2 ⟨(e.inv.val.app (op ⊤)).hom, fun a => ?_, fun m =>
      ?_⟩
    · exact congr($(e.hom_inv_id).val.app (op ⊤) |>.hom a)
    · exact congr($(e.inv_hom_id).val.app (op ⊤) |>.hom m)
  have hb' : Function.Bijective fun a : Γ(X, W.ι ''ᵁ ⊤) =>
      a • N.presheaf.map (homOfLE (Scheme.Opens.ι_image_top W).le).op τ := hb
  exact (bijective_smul_map_iff_of_eq (Scheme.Opens.ι_image_top W) τ).1 hb'

end smulHom

section main

variable {L M : X.Modules} {U V : X.Opens} {s : Γ(L, U)} {t : Γ(M, U)}

lemma bijective_smul_tmul_res (hs : IsFrameOn s V) (ht : IsFrameOn t V) {W : X.Opens}
    (hWU : W ≤ U) (hWV : W ≤ V) :
    Function.Bijective fun g : Γ(X, W) =>
      g • ((L.presheaf.map (homOfLE hWU).op s : L.val.obj (op W)) ⊗ₜ[Γ(X, W)]
        (M.presheaf.map (homOfLE hWU).op t : M.val.obj (op W))) :=
  bijective_smul_tmul (R := Γ(X, W)) _ _ (hs hWU hWV) (ht hWU hWV)

variable (W : X.Opens) (hWU : W ≤ U)

/-- Restricts the first frame to a smaller open subset. -/
abbrev resL (W' : X.Opens) (h : W' ≤ W) : Γ(L, W') := L.presheaf.map (homOfLE (h.trans hWU)).op s

/-- Restricts the second frame to a smaller open subset. -/
abbrev resM (W' : X.Opens) (h : W' ≤ W) : Γ(M, W') := M.presheaf.map (homOfLE (h.trans hWU)).op t

/-- The tensor product section restricted to an open subset. -/
abbrev τW : Γ(L ⊗ M, W) :=
  Modules.tensorSections (L.presheaf.map (homOfLE hWU).op s) (M.presheaf.map (homOfLE hWU).op t)

lemma map_τW (W' : X.Opens) (h : W' ≤ W) :
    (L ⊗ M).presheaf.map (homOfLE h).op (τW (s := s) (t := t) W hWU) =
      tsApp L M W' ((resL (s := s) W hWU W' h : L.val.obj (op W')) ⊗ₜ[Γ(X, W')]
        (resM (t := t) W hWU W' h : M.val.obj (op W'))) := by
  dsimp only [τW]
  rw [map_homOfLE_tensorSections, tensorSections_eq_tsApp]
  congr 2
  · change (L.presheaf.map _ ≫ L.presheaf.map _) s = _
    rw [← L.presheaf.map_comp]
    rfl
  · change (M.presheaf.map _ ≫ M.presheaf.map _) t = _
    rw [← M.presheaf.map_comp]
    rfl

theorem isIso_smulSectionHom (hs : IsFrameOn s V) (ht : IsFrameOn t V) (hWV : W ≤ V) :
    IsIso (smulSectionHom (L ⊗ M) W (τW (s := s) (t := t) W hWU)) := by
  set ψ := smulSectionHom (L ⊗ M) W (τW (s := s) (t := t) W hWU)
  let J := Opens.grothendieckTopology ((W : X.Opens) : Scheme.{u})
  have pre_le : ∀ (W' : (W : Scheme.{u}).Opens) (W₂ : X.Opens), W₂ ≤ W.ι ''ᵁ W' → W.ι ⁻¹ᵁ W₂ ≤
      W' := by
    intro W' W₂ h₂ w hw
    obtain ⟨w', hw', hww'⟩ := h₂ hw
    rwa [← W.ι.isOpenEmbedding.injective hww']
  have hsurj : Presheaf.IsLocallySurjective J ((SheafOfModules.toSheaf _).map ψ).hom := by
    constructor
    rintro W' y
    refine fun x hx => ?_
    have hx' : W.ι.base x ∈ W.ι ''ᵁ W' := ⟨x, hx, rfl⟩
    obtain ⟨W₂, i₂, hxW₂, z, hz⟩ := exists_local_preimage (L := L) (M := M) y hx'
    have h₂W : W₂ ≤ W := i₂.le.trans (image_le W W')
    obtain ⟨g, hg⟩ := (bijective_smul_tmul_res hs ht (h₂W.trans hWU) (h₂W.trans hWV)).2 z
    dsimp only at hg
    have e₃ : W.ι ''ᵁ (W.ι ⁻¹ᵁ W₂) ≤ W₂ := (image_preimage_of_le h₂W).le
    refine ⟨W.ι ⁻¹ᵁ W₂, homOfLE (pre_le W' W₂ i₂.le), ⟨X.presheaf.map (homOfLE e₃).op g, ?_⟩, hxW₂⟩
    have key : g • (L ⊗ M).presheaf.map (homOfLE h₂W).op (τW (s := s) (t := t) W hWU) =
        (L ⊗ M).presheaf.map i₂.op y := by
      rw [map_τW]
      exact (tsApp_smul (L := L) (M := M) g _).symm.trans
        ((congrArg (tsApp L M W₂) hg).trans hz)
    have key' := congrArg ((L ⊗ M).presheaf.map (homOfLE e₃).op) key
    rw [Scheme.Modules.map_smul] at key'
    change secX W _ (X.presheaf.map (homOfLE e₃).op g) •
        (L ⊗ M).presheaf.map (homOfLE (image_le W _)).op (τW (s := s) (t := t) W hWU) =
      (L ⊗ M).presheaf.map (W.ι.opensFunctor.map (homOfLE (pre_le W' W₂ i₂.le))).op y
    convert key' using 2
    · change _ = ((L ⊗ M).presheaf.map _ ≫ (L ⊗ M).presheaf.map _) _
      rw [← (L ⊗ M).presheaf.map_comp]
      rfl
    · change _ = ((L ⊗ M).presheaf.map _ ≫ (L ⊗ M).presheaf.map _) _
      rw [← (L ⊗ M).presheaf.map_comp]
      rfl
  have hinj : Presheaf.IsLocallyInjective J ((SheafOfModules.toSheaf _).map ψ).hom := by
    constructor
    intro W' a b hab
    refine fun x hx => ?_
    have hab' : secX W W'.unop a • (L ⊗ M).presheaf.map (homOfLE (image_le W W'.unop)).op
          (τW (s := s) (t := t) W hWU) =
        secX W W'.unop b • (L ⊗ M).presheaf.map (homOfLE (image_le W W'.unop)).op
          (τW (s := s) (t := t) W hWU) := hab
    rw [map_τW] at hab'
    have hab'' := (tsApp_smul (L := L) (M := M) (secX W W'.unop a) _).trans
      (hab'.trans (tsApp_smul (L := L) (M := M) (secX W W'.unop b) _).symm)
    have hx' : W.ι.base x ∈ W.ι ''ᵁ W'.unop := ⟨x, hx, rfl⟩
    obtain ⟨W₂, i₂, hxW₂, h₂⟩ := exists_local_eq _ _ hab'' hx'
    have h₂W : W₂ ≤ W := i₂.le.trans (image_le W W'.unop)
    erw [map_smul_tmul, map_smul_tmul] at h₂
    have h₃ : X.presheaf.map i₂.op (secX W W'.unop a) = X.presheaf.map i₂.op (secX W W'.unop b)
        := by
      apply (bijective_smul_tmul_res hs ht (h₂W.trans hWU) (h₂W.trans hWV)).1
      have hL : L.presheaf.map i₂.op (resL (s := s) W hWU (W.ι ''ᵁ W'.unop)
          (image_le W W'.unop)) = L.presheaf.map (homOfLE (h₂W.trans hWU)).op s := by
        change (L.presheaf.map (homOfLE ((image_le W W'.unop).trans hWU)).op ≫
          L.presheaf.map i₂.op) s = _
        erw [← L.presheaf.map_comp]
        rfl
      have hM : M.presheaf.map i₂.op (resM (t := t) W hWU (W.ι ''ᵁ W'.unop)
          (image_le W W'.unop)) = M.presheaf.map (homOfLE (h₂W.trans hWU)).op t := by
        change (M.presheaf.map (homOfLE ((image_le W W'.unop).trans hWU)).op ≫
          M.presheaf.map i₂.op) t = _
        erw [← M.presheaf.map_comp]
        rfl
      erw [hL, hM] at h₂
      exact h₂
    have e₃ : W.ι ''ᵁ (W.ι ⁻¹ᵁ W₂) ≤ W₂ := (image_preimage_of_le h₂W).le
    refine ⟨W.ι ⁻¹ᵁ W₂, homOfLE (pre_le W'.unop W₂ i₂.le), ?_, hxW₂⟩
    have h₄ := congrArg (X.presheaf.map (homOfLE e₃).op) h₃
    change (X.presheaf.map _ ≫ X.presheaf.map _) a = (X.presheaf.map _ ≫ X.presheaf.map _) b at h₄
    erw [← X.presheaf.map_comp] at h₄
    exact h₄
  have h₁ : IsIso ((SheafOfModules.toSheaf _).map ψ) :=
    (Sheaf.isLocallyBijective_iff_isIso _).1 ⟨hinj, hsurj⟩
  have h₂ : IsIso ((PresheafOfModules.toPresheaf _).map ((SheafOfModules.forget _).map ψ)) := by
    change IsIso ((sheafToPresheaf _ _).map ((SheafOfModules.toSheaf _).map ψ))
    infer_instance
  have := (SheafOfModules.fullyFaithfulForget
    (((W : X.Opens) : Scheme.{u}).ringCatSheaf)).reflectsIsomorphisms
  have h₃ := isIso_of_reflects_iso ((SheafOfModules.forget _).map ψ)
    (PresheafOfModules.toPresheaf _)
  exact isIso_of_reflects_iso ψ (SheafOfModules.forget _)

end main

theorem isFrameOn_tensorSections {L M : X.Modules} {U V : X.Opens} {s : Γ(L, U)} {t : Γ(M, U)}
    (hs : IsFrameOn s V) (ht : IsFrameOn t V) : IsFrameOn (Modules.tensorSections s t) V := by
  intro W hWU hWV
  have h := bijective_smul_of_isIso (isIso_smulSectionHom W hWU hs ht hWV)
  simp only [Modules.map_homOfLE_tensorSections]
  exact h

end FrameTensor



end AlgebraicGeometry.Scheme.Modules







end



open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules in
theorem _root_.AlgebraicGeometry.Scheme.Modules.IsFrameOn.tensorSections_monoidalV2 {X :
  AlgebraicGeometry.Scheme.{u}} {L M : X.Modules} {U V : X.Opens}
    {s : Γ(L, U)} {t : Γ(M, U)}
    (hs : AlgebraicGeometry.Scheme.Modules.IsFrameOn s V)
    (ht : AlgebraicGeometry.Scheme.Modules.IsFrameOn t V) :
    AlgebraicGeometry.Scheme.Modules.IsFrameOn (AlgebraicGeometry.Scheme.Modules.tensorSections s
      t) V :=
  AlgebraicGeometry.Scheme.Modules.FrameTensor.isFrameOn_tensorSections hs ht
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsFrameOn_tensorSections_monoidalV2
end ProofImplementation

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_OModulePresheafHom.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
Morphisms of module presheaves, their affine sections and short exact sequences.
-/

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite Limits

variable {R : Type u} [CommRing R] {V : Scheme.{u}}

namespace Scheme.OrderedAffineCover

variable (π : V ⟶ Spec (.of R)) (K : V.OrderedAffineCover)

theorem isAffineOpen_inf_of_isSeparated [IsSeparated π] {U W : V.Opens} (hU : IsAffineOpen U)
    (hW : IsAffineOpen W) : IsAffineOpen (U ⊓ W) := by
  have : IsAffineHom (pullback.diagonal π) := inferInstance
  exact isAffineHom_diagonal_iff.mp this ⊤ (isAffineOpen_top _) U (by simp) W (by simp) hU hW

theorem isAffineOpen_inter [IsSeparated π] {i : ℕ} (s : K.Idx i) : IsAffineOpen (K.inter s) := by
  suffices h : ∀ (n : ℕ) (t : Fin (n + 1) → K.ι), IsAffineOpen (⨅ j, K.U (t j)) from h i s.1
  intro n
  induction n with
  | zero =>
    intro t
    have h1 : (⨅ j : Fin 1, K.U (t j)) = K.U (t 0) :=
      le_antisymm (iInf_le _ 0) (le_iInf fun j => by fin_cases j; exact le_rfl)
    rw [h1]; exact K.isAffineOpen (t 0)
  | succ m ih =>
    intro t
    have hsplit : (⨅ j : Fin (m + 2), K.U (t j)) = K.U (t 0) ⊓ (⨅ j : Fin (m + 1), K.U (t j.succ))
      :=
      le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun j => iInf_le _ j.succ))
        (le_iInf fun j => Fin.cases inf_le_left (fun k => inf_le_right.trans (iInf_le _ k)) j)
    rw [hsplit]
    exact isAffineOpen_inf_of_isSeparated π (K.isAffineOpen (t 0)) (ih (t ∘ Fin.succ))

/-- The affine open given by an intersection indexed by the ordered affine cover. -/
abbrev affineInter [IsSeparated π] {i : ℕ} (s : K.Idx i) : V.affineOpens :=
  ⟨K.inter s, K.isAffineOpen_inter π s⟩

end Scheme.OrderedAffineCover

namespace OModulePresheaf

variable {π : V ⟶ Spec (.of R)}

/--
A morphism of O-module presheaves, linear over local section rings and compatible with
restriction.
-/
structure Hom (F G : OModulePresheaf π) where
  /-- The base-ring linear map on sections of each open subset. -/
  app : ∀ U : V.Opens, F.obj U →ₗ[R] G.obj U
  /-- Each section map respects scalar multiplication by local regular functions. -/
  app_smul : ∀ (U : V.Opens) (a : Γ(V, U)) (x : F.obj U), app U (a • x) = a • app U x
  /-- The section maps commute with restriction to smaller open subsets. -/
  naturality : ∀ {U U' : V.Opens} (h : U ≤ U'), app U ∘ₗ F.res h = G.res h ∘ₗ app U'

/-- A sequence of O-module presheaves that is short exact on every open subset. -/
structure SES (F₁ F₂ F₃ : OModulePresheaf π) where
  /-- The inclusion morphism of the short exact sequence. -/
  inc : Hom F₁ F₂
  /-- The projection morphism of the short exact sequence. -/
  proj : Hom F₂ F₃
  /-- The inclusion is injective on sections of every open subset. -/
  injective : ∀ U : V.Opens, Function.Injective (inc.app U)
  /-- The projection is surjective on sections of every open subset. -/
  surjective : ∀ U : V.Opens, Function.Surjective (proj.app U)
  /-- The image of the inclusion equals the kernel of the projection on each open subset. -/
  exact : ∀ U : V.Opens, LinearMap.range (inc.app U) = LinearMap.ker (proj.app U)

/--
A morphism on affine-open sections, linear over local section rings and compatible with
restriction.
-/
structure AffHom (F G : OModulePresheaf π) where
  /-- The base-ring linear map on sections of each affine open subset. -/
  app : ∀ U : V.affineOpens, F.obj U.1 →ₗ[R] G.obj U.1
  /-- Each affine-open section map respects scalar multiplication by local regular functions. -/
  app_smul : ∀ (U : V.affineOpens) (a : Γ(V, U.1)) (x : F.obj U.1), app U (a • x) = a • app U x
  /-- The section maps commute with restriction between affine open subsets. -/
  naturality : ∀ {U U' : V.affineOpens} (h : U.1 ≤ U'.1), app U ∘ₗ F.res h = G.res h ∘ₗ app U'

/-- A sequence of O-module presheaves that is short exact on every affine open subset. -/
structure AffSES (F₁ F₂ F₃ : OModulePresheaf π) where
  /-- The inclusion morphism on affine-open sections. -/
  inc : AffHom F₁ F₂
  /-- The projection morphism on affine-open sections. -/
  proj : AffHom F₂ F₃
  /-- The inclusion is injective on sections of every affine open subset. -/
  injective : ∀ U : V.affineOpens, Function.Injective (inc.app U)
  /-- The projection is surjective on sections of every affine open subset. -/
  surjective : ∀ U : V.affineOpens, Function.Surjective (proj.app U)
  /-- The image of the inclusion equals the kernel of the projection on each affine open subset. -/
  exact : ∀ U : V.affineOpens, LinearMap.range (inc.app U) = LinearMap.ker (proj.app U)

namespace Hom

variable {F G H : OModulePresheaf π}

/-- The section map viewed as a linear map over the ring of regular functions on the open subset. -/
def appSections (φ : Hom F G) (U : V.Opens) : F.obj U →ₗ[Γ(V, U)] G.obj U :=
  { toFun := φ.app U, map_add' := (φ.app U).map_add, map_smul' := φ.app_smul U }

@[simp] theorem appSections_apply (φ : Hom F G) (U : V.Opens) (x : F.obj U) :
    φ.appSections U x = φ.app U x := rfl

theorem naturality_apply (φ : Hom F G) {U U' : V.Opens} (h : U ≤ U') (x : F.obj U') :
    φ.app U (F.res h x) = G.res h (φ.app U' x) :=
  congrFun (congrArg DFunLike.coe (φ.naturality h)) x

variable (F) in
/-- The identity morphism of an O-module presheaf. -/
protected def id : Hom F F where
  app _ := LinearMap.id
  app_smul _ _ _ := rfl
  naturality _ := rfl

/-- The composite morphism obtained by composing the section maps. -/
def comp (ψ : Hom G H) (φ : Hom F G) : Hom F H where
  app U := ψ.app U ∘ₗ φ.app U
  app_smul U a x := by
    change ψ.app U (φ.app U (a • x)) = a • ψ.app U (φ.app U x)
    rw [φ.app_smul, ψ.app_smul]
  naturality h := by
    rw [LinearMap.comp_assoc, φ.naturality, ← LinearMap.comp_assoc, ψ.naturality,
      LinearMap.comp_assoc]

@[simp] theorem id_app (U : V.Opens) (x : F.obj U) : (Hom.id F).app U x = x := rfl
@[simp] theorem comp_app (ψ : Hom G H) (φ : Hom F G) (U : V.Opens) (x : F.obj U) :
    (ψ.comp φ).app U x = ψ.app U (φ.app U x) := rfl

/-- The restriction of a presheaf morphism to affine-open sections. -/
def toAffHom (φ : Hom F G) : AffHom F G where
  app U := φ.app U.1
  app_smul U := φ.app_smul U.1
  naturality h := φ.naturality h

@[simp] theorem toAffHom_app (φ : Hom F G) (U : V.affineOpens) : φ.toAffHom.app U = φ.app U.1 := rfl

end Hom

namespace AffHom

variable {F G H : OModulePresheaf π}

/-- The affine-open section map viewed as linear over its ring of regular functions. -/
def appSections (φ : AffHom F G) (U : V.affineOpens) : F.obj U.1 →ₗ[Γ(V, U.1)] G.obj U.1 :=
  { toFun := φ.app U, map_add' := (φ.app U).map_add, map_smul' := φ.app_smul U }

@[simp] theorem appSections_apply (φ : AffHom F G) (U : V.affineOpens) (x : F.obj U.1) :
    φ.appSections U x = φ.app U x := rfl

theorem naturality_apply (φ : AffHom F G) {U U' : V.affineOpens} (h : U.1 ≤ U'.1) (x : F.obj U'.1) :
    φ.app U (F.res h x) = G.res h (φ.app U' x) :=
  congrFun (congrArg DFunLike.coe (φ.naturality h)) x

variable (F) in
/-- The identity morphism on affine-open sections. -/
protected def id : AffHom F F where
  app _ := LinearMap.id
  app_smul _ _ _ := rfl
  naturality _ := rfl

/-- The composite morphism on affine-open sections. -/
def comp (ψ : AffHom G H) (φ : AffHom F G) : AffHom F H where
  app U := ψ.app U ∘ₗ φ.app U
  app_smul U a x := by
    change ψ.app U (φ.app U (a • x)) = a • ψ.app U (φ.app U x)
    rw [φ.app_smul, ψ.app_smul]
  naturality h := by
    rw [LinearMap.comp_assoc, φ.naturality, ← LinearMap.comp_assoc, ψ.naturality,
      LinearMap.comp_assoc]

@[simp] theorem id_app (U : V.affineOpens) (x : F.obj U.1) : (AffHom.id F).app U x = x := rfl
@[simp] theorem comp_app (ψ : AffHom G H) (φ : AffHom F G) (U : V.affineOpens) (x : F.obj U.1) :
    (ψ.comp φ).app U x = ψ.app U (φ.app U x) := rfl

end AffHom

/--
The short exact sequence on affine-open sections obtained from a sectionwise short exact sequence.
-/
def SES.toAffSES {F₁ F₂ F₃ : OModulePresheaf π} (S : SES F₁ F₂ F₃) : AffSES F₁ F₂ F₃ where
  inc := S.inc.toAffHom
  proj := S.proj.toAffHom
  injective U := S.injective U.1
  surjective U := S.surjective U.1
  exact U := S.exact U.1

section Cochains

variable [IsSeparated π] (K : V.OrderedAffineCover) {F G : OModulePresheaf π}

/-- The map of Cech cochains induced by the affine-open section maps. -/
def AffHom.cochainMap (φ : AffHom F G) (i : ℕ) : F.cochain K i →ₗ[R] G.cochain K i :=
  LinearMap.pi fun s => (φ.app (K.affineInter π s)).comp (LinearMap.proj s)

theorem AffHom.cochainMap_apply (φ : AffHom F G) (i : ℕ) (f : F.cochain K i) (s : K.Idx i) :
    φ.cochainMap K i f s = φ.app (K.affineInter π s) (f s) := rfl

theorem AffHom.cochainMap_comp_d (φ : AffHom F G) (i : ℕ) :
    φ.cochainMap K (i + 1) ∘ₗ F.d K i = G.d K i ∘ₗ φ.cochainMap K i := by
  refine LinearMap.ext fun f => funext fun s => ?_
  simp only [LinearMap.comp_apply, AffHom.cochainMap_apply, OModulePresheaf.d_apply, map_sum,
    map_zsmul]
  exact Finset.sum_congr rfl fun j _ => congrArg _
    (φ.naturality_apply (U := K.affineInter π s) (U' := K.affineInter π (K.face s j))
      (K.inter_le_inter_face s j) _)

/-- The induced map on the kernels of the Cech differentials. -/
def AffHom.kerMap (φ : AffHom F G) (i : ℕ) :
    LinearMap.ker (F.d K i) →ₗ[R] LinearMap.ker (G.d K i) :=
  (φ.cochainMap K i).restrict fun f hf => LinearMap.mem_ker.mpr <| by
    rw [← LinearMap.comp_apply, ← AffHom.cochainMap_comp_d, LinearMap.comp_apply,
      LinearMap.mem_ker.mp hf, map_zero]

@[simp] theorem AffHom.kerMap_coe (φ : AffHom F G) (i : ℕ) (x : LinearMap.ker (F.d K i)) :
    (φ.kerMap K i x : G.cochain K i) = φ.cochainMap K i x := rfl

/-- The induced map on zeroth Cech cohomology. -/
abbrev AffHom.H0Map (φ : AffHom F G) : F.H0 K →ₗ[R] G.H0 K := φ.kerMap K 0

/-- The induced map on Cech cohomology in degree `i + 1`. -/
def AffHom.HSuccMap (φ : AffHom F G) (i : ℕ) : F.HSucc K i →ₗ[R] G.HSucc K i :=
  Submodule.mapQ _ _ (φ.kerMap K (i + 1)) fun x hx => by
    obtain ⟨g, hg⟩ := (Submodule.mem_comap.mp hx)
    refine Submodule.mem_comap.mpr ⟨φ.cochainMap K i g, ?_⟩
    change G.d K i _ = φ.cochainMap K (i + 1) x.1
    rw [← LinearMap.comp_apply, ← AffHom.cochainMap_comp_d, LinearMap.comp_apply, hg]
    rfl

theorem AffHom.HSuccMap_mk (φ : AffHom F G) (i : ℕ) (x : LinearMap.ker (F.d K (i + 1))) :
    φ.HSuccMap K i (Submodule.Quotient.mk x) = Submodule.Quotient.mk (φ.kerMap K (i + 1) x) := rfl

end Cochains

end OModulePresheaf

end AlgebraicGeometry

end

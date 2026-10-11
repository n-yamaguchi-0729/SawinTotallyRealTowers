/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.Modules.ProjectivePresentation
import Nyll.SchemeTheory.ProjectiveSpace.BaseChange
import Nyll.SchemeTheory.ProjectiveSpace.StandardChartsBaseChange
import Nyll.SchemeTheory.Modules.PullbackFrame

/-!
Base change of a projective presentation by pulling back its presenting sections and morphism.
The chart ratios and pullback square give the compatibility of the resulting presentation.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

open Opposite TopologicalSpace HomogeneousLocalization

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

namespace PresBC

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {X X' : Scheme.{u}}
    {f : X ⟶ Spec (.of R)} {f' : X' ⟶ Spec (.of A)} {p : X' ⟶ X}
    (sq : IsPullback p f' f (Spec.map (CommRingCat.ofHom (algebraMap R A))))
    {M : X.Modules} {N : ℕ} (𝔓 : M.ProjPresentation f N)

local notation "𝒜R" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R
local notation "𝒜A" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A

/-- The projective presentation morphism obtained from the pullback square. -/
noncomputable def toProj' : X' ⟶ Proj 𝒜A :=
  (ProjSpace.isPullback_map R A N).lift (p ≫ 𝔓.toProj) f'
    (by rw [Category.assoc, 𝔓.toProj_π]; exact sq.w)

lemma toProj'_map : toProj' sq 𝔓 ≫ ProjSpace.map R A N = p ≫ 𝔓.toProj :=
  IsPullback.lift_fst _ _ _ _

lemma toProj'_π : toProj' sq 𝔓 ≫ ProjSpace.π A N = f' :=
  IsPullback.lift_snd _ _ _ _

lemma isPullback_toProj' : IsPullback p (toProj' sq 𝔓) 𝔓.toProj (ProjSpace.map R A N) := by
  have s : IsPullback p (toProj' sq 𝔓 ≫ ProjSpace.π A N) (𝔓.toProj ≫ ProjSpace.π R N)
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
    rw [toProj'_π, 𝔓.toProj_π]; exact sq
  exact IsPullback.of_bot s (toProj'_map sq 𝔓).symm (ProjSpace.isPullback_map R A N)

lemma preimage_chart (i : Fin (N + 1)) :
    toProj' sq 𝔓 ⁻¹ᵁ Proj.basicOpen 𝒜A (MvPolynomial.X i) =
      p ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜R (MvPolynomial.X i)) := by
  rw [← ProjSpace.map_preimage_basicOpen_X R A N i, ← Scheme.Hom.comp_preimage, toProj'_map,
    Scheme.Hom.comp_preimage]

/-- The presenting sections pulled back through the adjunction unit. -/
noncomputable abbrev σ' (i : Fin (N + 1)) : Γ((Modules.pullback p).obj M, ⊤) :=
  ((pullbackPushforwardAdjunction p).unit.app M).app ⊤ (𝔓.σ i)
omit sq 𝔓 in
lemma presheaf_map_congr {Z : Scheme.{u}} (G : TopCat.Presheaf Ab Z) {U V : Z.Opens}
    (k₁ k₂ : op U ⟶ op V) (z : G.obj (op U)) : G.map k₁ z = G.map k₂ z := by
  rw [show k₁ = k₂ from Quiver.Hom.unop_inj (Subsingleton.elim _ _)]

/-- The pullback of a module section through the adjunction unit. -/
noncomputable def eta (U : X.Opens) (m : Γ(M, U)) : Γ((Modules.pullback p).obj M, p ⁻¹ᵁ U) :=
  ((pullbackPushforwardAdjunction p).unit.app M).app U m
omit sq 𝔓 f in
lemma eta_smul (U : X.Opens) (r : Γ(X, U)) (m : Γ(M, U)) :
    eta (p := p) U (r • m) = p.app U r • eta (p := p) U m :=
  Modules.Hom.app_smul _ r m
omit sq 𝔓 f in
lemma eta_resTop (U : X.Opens) (m : Γ(M, ⊤)) :
    eta (p := p) U (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op m) =
      ((Modules.pullback p).obj M).presheaf.map (homOfLE (le_top : p ⁻¹ᵁ U ≤ ⊤)).op
        (eta (p := p) ⊤ m) := by
  have hnat := ((pullbackPushforwardAdjunction p).unit.app M).mapPresheaf.naturality
    (homOfLE (le_top : U ≤ ⊤)).op
  have hx := ConcreteCategory.congr_hom hnat m
  simp only [ConcreteCategory.comp_apply, mapPresheaf_app] at hx
  refine hx.trans ?_
  exact presheaf_map_congr ((Modules.pullback p).obj M).presheaf _ _ _

lemma ratio_pulled (i j : Fin (N + 1)) :
    (p.app (𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜R (MvPolynomial.X i))
        (𝔓.toProj.app (Proj.basicOpen 𝒜R (MvPolynomial.X i))
          (Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio R N i j)))) •
      ((Modules.pullback p).obj M).presheaf.map
        (homOfLE (le_top : p ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜R (MvPolynomial.X i)) ≤ ⊤)).op
          (σ' 𝔓 (p := p) i) =
      ((Modules.pullback p).obj M).presheaf.map
        (homOfLE (le_top : p ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜R (MvPolynomial.X i)) ≤ ⊤)).op
          (σ' 𝔓 (p := p) j) := by
  have h := congrArg (eta (p := p) (M := M) (𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜R (MvPolynomial.X i)))
    (𝔓.app_ratio_smul i j)
  have h2 := (eta_smul (p := p) _ _ _).symm.trans h
  rw [eta_resTop, eta_resTop] at h2
  exact h2

end PresBC

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

namespace PresBC

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {X X' : Scheme.{u}}
    {f : X ⟶ Spec (.of R)} {f' : X' ⟶ Spec (.of A)} {p : X' ⟶ X}
    (sq : IsPullback p f' f (Spec.map (CommRingCat.ofHom (algebraMap R A))))
    {M : X.Modules} {N : ℕ} (𝔓 : M.ProjPresentation f N)

local notation "𝒜R" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R
local notation "𝒜A" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A

omit sq 𝔓 in
lemma awayToSection_mk_congr (s t : MvPolynomial (Fin (N + 1)) A) (hst : s = t)
    (hs : s ∈ 𝒜A 1) (ht : t ∈ 𝒜A 1) (a b : MvPolynomial (Fin (N + 1)) A) (hab : a = b)
    (ha : a ∈ 𝒜A (1 • 1)) (hb : b ∈ 𝒜A (1 • 1)) (E : Proj.basicOpen 𝒜A s = Proj.basicOpen 𝒜A t) :
    (Proj 𝒜A).presheaf.map (eqToHom E).op (Proj.awayToSection 𝒜A t (Away.mk 𝒜A ht 1 b hb)) =
      Proj.awayToSection 𝒜A s (Away.mk 𝒜A hs 1 a ha) := by
  subst hst hab
  exact congrArg
    (fun φ : Γ(Proj 𝒜A, Proj.basicOpen 𝒜A s) ⟶ Γ(Proj 𝒜A, Proj.basicOpen 𝒜A s) =>
      φ.hom (Proj.awayToSection 𝒜A s (Away.mk 𝒜A hs 1 a ha)))
    ((Proj 𝒜A).presheaf.map_id (op (Proj.basicOpen 𝒜A s)))
omit sq 𝔓 in
lemma presheaf_map_congr' {Z : Scheme.{u}} (G : TopCat.Presheaf CommRingCat Z) {U V : Z.Opens}
    (k₁ k₂ : op U ⟶ op V) (z : G.obj (op U)) : G.map k₁ z = G.map k₂ z := by
  rw [show k₁ = k₂ from Quiver.Hom.unop_inj (Subsingleton.elim _ _)]
omit sq 𝔓 in
lemma presheaf_map_map_eq {Z : Scheme.{u}} {U V W : Z.Opens}
    (k₁ : op U ⟶ op V) (k₂ : op V ⟶ op W) (k : op U ⟶ op W) (z : Γ(Z, U)) :
    Z.presheaf.map k₂ (Z.presheaf.map k₁ z) = Z.presheaf.map k z := by
  rw [show k = k₁ ≫ k₂ from Quiver.Hom.unop_inj (Subsingleton.elim _ _), Z.presheaf.map_comp]
  rfl
omit sq 𝔓 f f' p in
lemma map_app_ratio (i j : Fin (N + 1)) :
    (ProjSpace.map R A N).app (Proj.basicOpen 𝒜R (MvPolynomial.X i))
        (Proj.awayToSection 𝒜R (MvPolynomial.X i) (ProjSpace.ratio R N i j)) =
      (Proj 𝒜A).presheaf.map (eqToHom (ProjSpace.map_preimage_basicOpen_X R A N i)).op
        (Proj.awayToSection 𝒜A (MvPolynomial.X i) (ProjSpace.ratio A N i j)) := by
  have key := Proj.awayToSection_comp_appLE (𝒜 := 𝒜R) (ℬ := 𝒜A) (f := ProjSpace.mvMapGraded R A N)
    (hf := ProjSpace.irrelevant_le_map_mvMapGraded R A N) (s := MvPolynomial.X i)
    (ProjSpace.X_mem_one R N i)
  have hk := ConcreteCategory.congr_hom key (ProjSpace.ratio R N i j)
  simp only [ConcreteCategory.comp_apply] at hk
  rw [Scheme.Hom.appLE] at hk
  simp only [ConcreteCategory.comp_apply] at hk
  have hk' : (ProjSpace.map R A N).app (Proj.basicOpen 𝒜R (MvPolynomial.X i))
      (Proj.awayToSection 𝒜R (MvPolynomial.X i) (ProjSpace.ratio R N i j)) =
        Proj.awayToSection 𝒜A ((ProjSpace.mvMapGraded R A N) (MvPolynomial.X i))
          (HomogeneousLocalization.Away.map (ProjSpace.mvMapGraded R A N) (MvPolynomial.X i)
            (ProjSpace.ratio R N i j)) := by
    refine Eq.trans ?_ hk
    change _ = (Proj 𝒜A).presheaf.map ((homOfLE _).op :
      op (Proj.basicOpen 𝒜A ((ProjSpace.mvMapGraded R A N) (MvPolynomial.X i))) ⟶
        op (Proj.basicOpen 𝒜A ((ProjSpace.mvMapGraded R A N) (MvPolynomial.X i)))) _
    erw [presheaf_map_congr' (Proj 𝒜A).presheaf _ (𝟙 _), CategoryTheory.Functor.map_id,
      CategoryTheory.id_apply]
    rfl
  rw [hk']
  rw [ProjSpace.ratio, ProjSpace.ratio, HomogeneousLocalization.Away.map_mk]
  symm
  exact awayToSection_mk_congr _ _ (ProjSpace.mvMapGraded_X R A N i) _ _ _ _
    (ProjSpace.mvMapGraded_X R A N j) _ _ _

lemma toProj'_app_ratio (i j : Fin (N + 1)) :
    (toProj' sq 𝔓).app (Proj.basicOpen 𝒜A (MvPolynomial.X i))
        (Proj.awayToSection 𝒜A (MvPolynomial.X i) (ProjSpace.ratio A N i j)) =
      X'.presheaf.map (eqToHom (preimage_chart sq 𝔓 i)).op
        (p.app (𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜R (MvPolynomial.X i))
          (𝔓.toProj.app (Proj.basicOpen 𝒜R (MvPolynomial.X i))
            (Proj.awayToSection 𝒜R (MvPolynomial.X i) (ProjSpace.ratio R N i j)))) := by
  have h1 : Proj.awayToSection 𝒜A (MvPolynomial.X i) (ProjSpace.ratio A N i j) =
      (Proj 𝒜A).presheaf.map (eqToHom (ProjSpace.map_preimage_basicOpen_X R A N i).symm).op
        ((ProjSpace.map R A N).app (Proj.basicOpen 𝒜R (MvPolynomial.X i))
          (Proj.awayToSection 𝒜R (MvPolynomial.X i) (ProjSpace.ratio R N i j))) := by
    rw [map_app_ratio, ← CategoryTheory.comp_apply, ← CategoryTheory.Functor.map_comp,
      ← op_comp, eqToHom_trans,
      eqToHom_refl, op_id, CategoryTheory.Functor.map_id, CategoryTheory.id_apply]
  rw [h1]
  have h2 := ConcreteCategory.congr_hom ((toProj' sq 𝔓).naturality
    (eqToHom (ProjSpace.map_preimage_basicOpen_X R A N i).symm).op)
    ((ProjSpace.map R A N).app (Proj.basicOpen 𝒜R (MvPolynomial.X i))
      (Proj.awayToSection 𝒜R (MvPolynomial.X i) (ProjSpace.ratio R N i j)))
  simp only [ConcreteCategory.comp_apply] at h2
  rw [h2]
  have h3 := ConcreteCategory.congr_hom
    (Scheme.Hom.congr_app (toProj'_map sq 𝔓) (Proj.basicOpen 𝒜R (MvPolynomial.X i)))
    (Proj.awayToSection 𝒜R (MvPolynomial.X i) (ProjSpace.ratio R N i j))
  simp only [Scheme.Hom.comp_app] at h3
  have h3' : (toProj' sq 𝔓).app (ProjSpace.map R A N ⁻¹ᵁ Proj.basicOpen 𝒜R (MvPolynomial.X i))
      ((ProjSpace.map R A N).app (Proj.basicOpen 𝒜R (MvPolynomial.X i))
        (Proj.awayToSection 𝒜R (MvPolynomial.X i) (ProjSpace.ratio R N i j))) =
      X'.presheaf.map (eqToHom (by
        rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, toProj'_map])).op
        (p.app (𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜R (MvPolynomial.X i))
          (𝔓.toProj.app (Proj.basicOpen 𝒜R (MvPolynomial.X i))
            (Proj.awayToSection 𝒜R (MvPolynomial.X i) (ProjSpace.ratio R N i j)))) := h3
  rw [h3']
  exact presheaf_map_map_eq _ _ _ _
omit sq in
lemma resTop_eq {O O' : X'.Opens} (h : O = O') (m : Γ((Modules.pullback p).obj M, ⊤)) :
    ((Modules.pullback p).obj M).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op m =
      ((Modules.pullback p).obj M).presheaf.map (eqToHom h).op
        (((Modules.pullback p).obj M).presheaf.map (homOfLE (le_top : O' ≤ ⊤)).op m) := by
  subst h
  exact (congrArg
    (fun φ : Γ((Modules.pullback p).obj M, O) ⟶ Γ((Modules.pullback p).obj M, O) =>
      φ.hom (((Modules.pullback p).obj M).presheaf.map
        (homOfLE (le_top : O ≤ ⊤)).op m))
    (((Modules.pullback p).obj M).presheaf.map_id (op O))).symm

/-- The projective presentation obtained by pulling back its sections and morphism. -/
noncomputable def baseChange : ((Modules.pullback p).obj M).ProjPresentation f' N where
  σ := σ' 𝔓
  toProj := toProj' sq 𝔓
  toProj_π := toProj'_π sq 𝔓
  frame := fun i V hV =>
    bijective_smul_unit_app_of_bijective_smul p M (𝔓.σ i)
      (V := 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜R (MvPolynomial.X i)) (𝔓.frame i) V
      (hV.trans (preimage_chart sq 𝔓 i).le)
  app_ratio_smul := fun i j => by
    rw [toProj'_app_ratio, resTop_eq (preimage_chart sq 𝔓 i), resTop_eq (preimage_chart sq 𝔓 i),
      ← Modules.map_smul, ratio_pulled]

end PresBC

end AlgebraicGeometry.Scheme.Modules

theorem _root_.AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {X X' : Scheme.{u}}
    {f : X ⟶ Spec (.of R)} {f' : X' ⟶ Spec (.of A)} {p : X' ⟶ X}
    (sq : IsPullback p f' f (Spec.map (CommRingCat.ofHom (algebraMap R A))))
    {M : X.Modules} {N : ℕ} (𝔓 : M.ProjPresentation f N) :
    ∃ 𝔓' : ((Scheme.Modules.pullback p).obj M).ProjPresentation f' N,
      (∀ i, 𝔓'.σ i =
        (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤) (𝔓.σ i)) ∧
      𝔓'.toProj ≫ ProjSpace.map R A N = p ≫ 𝔓.toProj ∧
      IsPullback p 𝔓'.toProj 𝔓.toProj (ProjSpace.map R A N) :=
  ⟨AlgebraicGeometry.Scheme.Modules.PresBC.baseChange sq 𝔓, fun _ => rfl,
    AlgebraicGeometry.Scheme.Modules.PresBC.toProj'_map sq 𝔓,
    AlgebraicGeometry.Scheme.Modules.PresBC.isPullback_toProj' sq 𝔓⟩
end Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_mem_map_maximalIdeal_of_stalkMap_mem_map_maximalIdeal_of_iso_pullback.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Ext

/-!
# mem map maximal Ideal of stalk Map mem map maximal Ideal of iso pullback
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace mem_map_maximalIdeal_of_stalkMap_mem_map_maximalIdeal_of_iso_pullback

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace IsLocalRing

namespace CFStalk

section algebra

variable {A A₁ : Type u} [CommRing A] [IsLocalRing A] [CommRing A₁] [IsLocalRing A₁]
  (ι₁ : A₁ →+* A) [IsLocalHom ι₁]

lemma residueFieldMap_bijective (hres₁ : Function.Surjective ((residue A).comp ι₁)) :
  Function.Bijective (ResidueField.map ι₁) := by
  refine ⟨(ResidueField.map ι₁).injective, fun v => ?_⟩
  obtain ⟨a₁, ha₁⟩ := hres₁ v
  exact ⟨residue A₁ a₁, by rw [ResidueField.map_residue]; exact ha₁⟩

/-- The residue field equivalence induced by the surjective residue map. -/
noncomputable def resEquiv (hres₁ : Function.Surjective ((residue A).comp ι₁)) :
    ResidueField A₁ ≃+* ResidueField A :=
  RingEquiv.ofBijective (ResidueField.map ι₁) (residueFieldMap_bijective ι₁ hres₁)

lemma resEquiv_symm_residue (hres₁ : Function.Surjective ((residue A).comp ι₁)) (a₁ : A₁) :
    (resEquiv ι₁ hres₁).symm (residue A (ι₁ a₁)) = residue A₁ a₁ := by
  apply (resEquiv ι₁ hres₁).injective
  rw [RingEquiv.apply_symm_apply]
  exact (ResidueField.map_residue ι₁ a₁).symm

variable (hres₁ : Function.Surjective ((residue A).comp ι₁)) {R : Type u} [CommRing R] (b : A₁ →+*
  R)

/-- The residue field map into the quotient by the image of the maximal ideal. -/
noncomputable def lift₁ : ResidueField A₁ →+* R ⧸ Ideal.map b (maximalIdeal A₁) :=
  Ideal.Quotient.lift (maximalIdeal A₁) ((Ideal.Quotient.mk (Ideal.map b (maximalIdeal A₁))).comp b)
    (fun a ha => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ ha)

lemma lift₁_residue (a₁ : A₁) :
    lift₁ b (residue A₁ a₁) = Ideal.Quotient.mk (Ideal.map b (maximalIdeal A₁)) (b a₁) := rfl

/-- The map from the larger local ring into the quotient, using the residue field equivalence. -/
noncomputable def aR : A →+* R ⧸ Ideal.map b (maximalIdeal A₁) :=
  (lift₁ b).comp ((resEquiv ι₁ hres₁).symm.toRingHom.comp (residue A))

lemma aR_apply (t : A) : aR ι₁ hres₁ b t = lift₁ b ((resEquiv ι₁ hres₁).symm (residue A t)) := rfl

lemma aR_ι₁ (a₁ : A₁) :
    aR ι₁ hres₁ b (ι₁ a₁) = Ideal.Quotient.mk (Ideal.map b (maximalIdeal A₁)) (b a₁) := by
  rw [aR_apply, resEquiv_symm_residue, lift₁_residue]

lemma aR_comp_ι₁ : (aR ι₁ hres₁ b).comp ι₁ = (Ideal.Quotient.mk (Ideal.map b (maximalIdeal
  A₁))).comp b :=
  RingHom.ext fun a₁ => aR_ι₁ ι₁ hres₁ b a₁

lemma aR_eq_zero_of_mem {t : A} (ht : t ∈ maximalIdeal A) : aR ι₁ hres₁ b t = 0 := by
  rw [aR_apply, (residue_eq_zero_iff t).mpr ht, map_zero, map_zero]
include hres₁ in
omit [IsLocalRing A₁] [IsLocalHom ι₁] in
lemma ringHom_ext_of_ι₁ {T : Type*} [CommRing T] (φ ψ : A →+* T)
    (hφ : ∀ t ∈ maximalIdeal A, φ t = 0) (hψ : ∀ t ∈ maximalIdeal A, ψ t = 0)
    (h : ∀ a₁, φ (ι₁ a₁) = ψ (ι₁ a₁)) : φ = ψ := by
  ext a
  obtain ⟨a₁, ha₁⟩ := hres₁ (residue A a)
  have : a - ι₁ a₁ ∈ maximalIdeal A := by
    rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]; exact ha₁.symm
  have e1 := hφ _ this
  have e2 := hψ _ this
  rw [map_sub, sub_eq_zero] at e1 e2
  rw [e1, e2, h]

end algebra

section thin
variable {Z : Scheme.{u}}
lemma map_op_congr {A B : Z.Opens} (i j : B ⟶ A) (s : Γ(Z, A)) :
    Z.presheaf.map i.op s = Z.presheaf.map j.op s := by
  rw [Subsingleton.elim i j]
lemma app_map_top {Z' : Scheme.{u}} (q : Z' ⟶ Z) (W : Z.Opens) (x : Γ(Z, ⊤)) :
    q.app W (Z.presheaf.map (homOfLE le_top).op x) =
      Z'.presheaf.map (homOfLE le_top).op (q.appTop x) := by
  have := congrArg (fun φ => φ.hom x) (q.naturality (homOfLE (le_top : W ≤ ⊤)).op)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at this
  rw [this]
  exact map_op_congr _ _ _
lemma comp_app_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) (x : Γ(Z, U)) :
    (f ≫ g).app U x = f.app (g ⁻¹ᵁ U) (g.app U x) := rfl
lemma map_id_apply' {A : Z.Opens} (i : A ⟶ A) (s : Γ(Z, A)) : Z.presheaf.map i.op s = s := by
  rw [Subsingleton.elim i (𝟙 _), op_id, Z.presheaf.map_id]; rfl
lemma map_congr' {A B : Z.Opens} (i j : op A ⟶ op B) (s : Γ(Z, A)) :
    Z.presheaf.map i s = Z.presheaf.map j s := by
  rw [← i.op_unop, ← j.op_unop, Subsingleton.elim i.unop j.unop]
lemma map_map_eq {A B C : Z.Opens} (i : op A ⟶ op B) (j : op B ⟶ op C) (s : Γ(Z, A)) :
    Z.presheaf.map j (Z.presheaf.map i s) = Z.presheaf.map (i ≫ j) s := by
  rw [Z.presheaf.map_comp]; rfl
lemma map_top_endo (i : op (⊤ : Z.Opens) ⟶ op ⊤) (s : Γ(Z, ⊤)) : Z.presheaf.map i s = s := by
  rw [map_congr' i (𝟙 _), Z.presheaf.map_id]; rfl
end thin

section scheme

variable {A A₁ : Type u} [CommRing A] [IsLocalRing A] [CommRing A₁] [IsLocalRing A₁]

/-- The base ring homomorphism into the stalk at a scheme point. -/
noncomputable def baseAt {B : Type u} [CommRing B] {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of
  B))
    (y : Y) : B →+* Y.presheaf.stalk y :=
  (Y.presheaf.germ ⊤ y trivial).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of
    B)).inv.hom)

lemma baseAt_apply {B : Type u} [CommRing B] {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of B)) (y
  : Y)
    (t : B) : baseAt f y t = Y.presheaf.germ ⊤ y trivial (f.appTop ((Scheme.ΓSpecIso
      (CommRingCat.of B)).inv t)) :=
  rfl

private lemma fromSpecStalk_comp_baseAt {B : Type u} [CommRing B] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of B)) (y : Y) :
    Y.fromSpecStalk y ≫ f = Spec.map (CommRingCat.ofHom (baseAt f y)) := by
  have hbase : CommRingCat.ofHom (baseAt f y) =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ f.appTop ≫ Y.presheaf.germ ⊤ y trivial := rfl
  rw [hbase, Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ]
  simp only [Category.assoc]
  rw [← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

lemma baseAt_mem_maximalIdeal {B : Type u} [CommRing B] [IsLocalRing B] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of B)) (y : Y) (hy : f.base y = closedPoint B) {t : B} (ht : t ∈
      maximalIdeal B) :
    baseAt f y t ∈ maximalIdeal (Y.presheaf.stalk y) := by
  rw [mem_maximalIdeal, mem_nonunits_iff, baseAt_apply]
  intro hu
  have hmem : y ∈ Y.basicOpen (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of B)).inv t)) :=
    (Y.mem_basicOpen_top _ y).mpr hu
  rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine] at hmem
  have hmem' : f.base y ∈ PrimeSpectrum.basicOpen t := hmem
  rw [hy] at hmem'
  exact (PrimeSpectrum.mem_basicOpen (R := B) t (closedPoint B)).mp hmem' ht
omit [IsLocalRing A] [IsLocalRing A₁] in
lemma stalkMap_baseAt (ι₁ : A₁ →+* A) {X₁ P : Scheme.{u}} (f₁ : X₁ ⟶ Spec (CommRingCat.of A₁))
    (π : P ⟶ X₁) (β : P ⟶ Spec (CommRingCat.of A))
    (hw : π ≫ f₁ = β ≫ Spec.map (CommRingCat.ofHom ι₁)) (p : P) (a₁ : A₁) :
    (π.stalkMap p).hom (baseAt f₁ (π.base p) a₁) = baseAt β p (ι₁ a₁) := by
  have h2 := congrArg (fun φ => φ.appTop ((Scheme.ΓSpecIso (CommRingCat.of A₁)).inv a₁)) hw
  have h3 := congrArg (fun φ => φ.hom a₁)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ι₁))
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom] at h2 h3
  rw [baseAt_apply, baseAt_apply]
  erw [Scheme.Hom.germ_stalkMap_apply, h2, ← h3]
  rfl


private lemma germ_stalkMap_stalkClosedPointTo
    {R : CommRingCat.{u}} [IsLocalRing R] {X Y : Scheme.{u}}
    (σ : Spec R ⟶ X) (p : X) (hp : σ (closedPoint R) = p) (g : X ⟶ Y)
    (U : Y.Opens) (hU : g p ∈ U) (hU' : (σ ≫ g) (closedPoint R) ∈ U) :
    Y.presheaf.germ U (g p) hU ≫ g.stalkMap p ≫
        (X.presheaf.stalkCongr (Inseparable.of_eq hp)).inv ≫ Scheme.stalkClosedPointTo σ =
      Y.presheaf.germ U ((σ ≫ g) (closedPoint R)) hU' ≫
        Scheme.stalkClosedPointTo (σ ≫ g) := by
  subst p
  simp only [TopCat.Presheaf.stalkCongr_inv, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp, Scheme.stalkClosedPointTo_comp]
  rfl

theorem core (ι₁ : A₁ →+* A) [IsLocalHom ι₁] (hres₁ : Function.Surjective ((residue A).comp ι₁))
    {X₁ P : Scheme.{u}} (f₁ : X₁ ⟶ Spec (CommRingCat.of A₁))
    (π : P ⟶ X₁) (β : P ⟶ Spec (CommRingCat.of A))
    (hP : IsPullback π β f₁ (Spec.map (CommRingCat.ofHom ι₁)))
    (p : P) (hp : β.base p = closedPoint A)
    (r : X₁.presheaf.stalk (π.base p))
    (hr : (π.stalkMap p).hom r ∈ Ideal.map (baseAt β p) (maximalIdeal A)) :
    r ∈ Ideal.map (baseAt f₁ (π.base p)) (maximalIdeal A₁) := by
  set I : Ideal (X₁.presheaf.stalk (π.base p)) := Ideal.map (baseAt f₁ (π.base p)) (maximalIdeal
    A₁) with hI
  have hbase : ∀ a₁ : A₁, (π.stalkMap p).hom (baseAt f₁ (π.base p) a₁) = baseAt β p (ι₁ a₁) :=
    stalkMap_baseAt ι₁ f₁ π β hP.w p
  have hβmem : ∀ {t : A}, t ∈ maximalIdeal A → baseAt β p t ∈ maximalIdeal (P.presheaf.stalk p) :=
    fun ht => baseAt_mem_maximalIdeal β p hp ht
  have hIle : I ≤ maximalIdeal (X₁.presheaf.stalk (π.base p)) := by
    rw [hI, Ideal.map_le_iff_le_comap]
    intro a₁ ha₁
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff, ← isUnit_map_iff (π.stalkMap p).hom,
      hbase]
    exact (mem_maximalIdeal _).mp (hβmem (map_nonunit ι₁ a₁ ha₁))
  have hItop : I ≠ ⊤ := fun h => (maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (h ▸ hIle))
  have : Nontrivial (X₁.presheaf.stalk (π.base p) ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
  have : IsLocalRing (X₁.presheaf.stalk (π.base p) ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let q : X₁.presheaf.stalk (π.base p) ⟶ CommRingCat.of (X₁.presheaf.stalk (π.base p) ⧸ I) :=
    CommRingCat.ofHom (Ideal.Quotient.mk I)
  have hqloc : IsLocalHom q.hom := by
    refine ⟨fun x hx => ?_⟩
    by_contra hxu
    obtain ⟨wbar, hw⟩ := hx.exists_right_inv
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective wbar
    have h0 : Ideal.Quotient.mk I (x * w - 1) = 0 := by
      rw [map_sub, map_one, map_mul, sub_eq_zero]; exact hw
    rw [Ideal.Quotient.eq_zero_iff_mem] at h0
    have h1 : x * w - 1 ∈ maximalIdeal _ := hIle h0
    have h2 : x * w ∈ maximalIdeal _ := Ideal.mul_mem_right _ _ ((mem_maximalIdeal _).mpr hxu)
    have h3 := (maximalIdeal (X₁.presheaf.stalk (π.base p))).sub_mem h2 h1
    rw [sub_sub_cancel] at h3
    exact (maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).mpr h3)
  let a : A →+* X₁.presheaf.stalk (π.base p) ⧸ I := aR ι₁ hres₁ (baseAt f₁ (π.base p))
  have ha₁ : ∀ a₁, a (ι₁ a₁) = Ideal.Quotient.mk I (baseAt f₁ (π.base p) a₁) := aR_ι₁ ι₁ hres₁
    (baseAt f₁ (π.base p))
  have ha0 : ∀ t ∈ maximalIdeal A, a t = 0 := fun t ht => aR_eq_zero_of_mem ι₁ hres₁ (baseAt f₁
    (π.base p)) ht
  have hw : (Spec.map q ≫ X₁.fromSpecStalk (π.base p)) ≫ f₁ =
      Spec.map (CommRingCat.ofHom a) ≫ Spec.map (CommRingCat.ofHom ι₁) := by
    rw [Category.assoc, fromSpecStalk_comp_baseAt, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext fun t => (ha₁ t).symm
  let σ := hP.lift (Spec.map q ≫ X₁.fromSpecStalk (π.base p)) (Spec.map (CommRingCat.ofHom a)) hw
  have hσ₁ : σ ≫ π = Spec.map q ≫ X₁.fromSpecStalk (π.base p) := hP.lift_fst _ _ _
  have hσ₂ : σ ≫ β = Spec.map (CommRingCat.ofHom a) := hP.lift_snd _ _ _
  have hts : ∀ t : A, (β.stalkMap p).hom (StructureSheaf.toStalk A (β.base p) t) = baseAt β p t :=
    by
    intro t
    rw [baseAt_apply]
    erw [Scheme.Hom.germ_stalkMap_apply β ⊤ p trivial]
    rfl
  let χ : X₁.presheaf.stalk (π.base p) →+* P.residueField p := (P.residue p).hom.comp (π.stalkMap
    p).hom
  have hχ0 : ∀ z ∈ maximalIdeal (X₁.presheaf.stalk (π.base p)), χ z = 0 := by
    intro z hz
    change IsLocalRing.residue _ ((π.stalkMap p).hom z) = 0
    exact (residue_eq_zero_iff _).mpr (map_nonunit _ z hz)
  let ρ : X₁.presheaf.stalk (π.base p) ⧸ I →+* P.residueField p :=
    Ideal.Quotient.lift I χ (fun z hz => hχ0 z (hIle hz))
  have hρq : ∀ z, ρ (Ideal.Quotient.mk I z) = χ z := fun z => rfl
  have hρloc : IsLocalHom ρ := by
    refine ⟨fun x hx => ?_⟩
    by_contra hxu
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hz : ¬ IsUnit z := fun h => hxu (h.map _)
    rw [hρq, hχ0 z ((mem_maximalIdeal _).mpr hz)] at hx
    exact not_isUnit_zero hx
  have : IsLocalHom (CommRingCat.ofHom ρ).hom := hρloc
  let γ : Spec (P.residueField p) ⟶ Spec (CommRingCat.of (X₁.presheaf.stalk (π.base p) ⧸ I)) :=
    Spec.map (CommRingCat.ofHom ρ)
  have hγσ : γ ≫ σ = P.fromSpecResidueField p := by
    apply hP.hom_ext
    · rw [Category.assoc, hσ₁, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
        Scheme.fromSpecResidueField, ← Category.assoc, ← Category.assoc]
      change (Spec.map (CommRingCat.ofHom ρ) ≫ Spec.map q) ≫ X₁.fromSpecStalk (π.base p) = _
      rw [← Spec.map_comp, ← Spec.map_comp, Scheme.residue_residueFieldMap]
      rfl
    · have hs : (Spec (CommRingCat.of A)).fromSpecStalk (β.base p) =
          Spec.map (show CommRingCat.of A ⟶ (Spec (CommRingCat.of A)).presheaf.stalk (β.base p) from
            StructureSheaf.toStalk A (β.base p)) := Spec.fromSpecStalk_eq' _ _
      rw [Category.assoc, hσ₂, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
        Scheme.fromSpecResidueField, hs, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
      change Spec.map (CommRingCat.ofHom ρ) ≫ Spec.map (CommRingCat.ofHom a) = _
      rw [← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      have eres := congrArg (fun φ => φ.hom) (Scheme.residue_residueFieldMap β p)
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at eres ⊢
      apply ringHom_ext_of_ι₁ ι₁ hres₁
      · intro t ht
        change ρ (a t) = 0
        rw [ha0 t ht, map_zero]
      · intro t ht
        have e1 := congrArg (fun φ => φ ((StructureSheaf.toStalk A (β.base p)).hom t)) eres
        erw [e1]
        have hz : (P.residue p).hom (baseAt β p t) = 0 :=
          (residue_eq_zero_iff _).mpr (hβmem ht)
        exact (congrArg (P.residue p).hom (hts t)).trans hz
      · intro a₁
        have e1 := congrArg (fun φ => φ ((StructureSheaf.toStalk A (β.base p)).hom (ι₁ a₁))) eres
        erw [e1]
        change ρ (a (ι₁ a₁)) = (P.residue p).hom
          ((β.stalkMap p).hom ((StructureSheaf.toStalk A (β.base p)).hom (ι₁ a₁)))
        rw [ha₁, hρq]
        exact congrArg (P.residue p).hom ((hbase a₁).trans (hts (ι₁ a₁)).symm)
  have hσp : σ.base (closedPoint (X₁.presheaf.stalk (π.base p) ⧸ I)) = p := by
    have h1 : γ.base (closedPoint (P.residueField p)) = closedPoint (X₁.presheaf.stalk (π.base p) ⧸
      I) :=
      Spec_closedPoint (f := CommRingCat.ofHom ρ)
    rw [← h1]
    change (γ ≫ σ).base (closedPoint _) = p
    rw [hγσ]
    exact Scheme.fromSpecResidueField_apply p _
  let e := P.presheaf.stalkCongr (Inseparable.of_eq hσp)
  let τ : P.presheaf.stalk p ⟶ CommRingCat.of (X₁.presheaf.stalk (π.base p) ⧸ I) := e.inv ≫
    Scheme.stalkClosedPointTo σ
  have hD1cat : π.stalkMap p ≫ τ = q := by
    refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
    have hU' : (σ ≫ π) (closedPoint (X₁.presheaf.stalk (π.base p) ⧸ I)) ∈ U := by
      change π.base (σ.base (closedPoint (X₁.presheaf.stalk (π.base p) ⧸ I))) ∈ U
      rw [hσp]
      exact hU
    change X₁.presheaf.germ U (π.base p) hU ≫ π.stalkMap p ≫ e.inv ≫
        Scheme.stalkClosedPointTo σ = X₁.presheaf.germ U (π.base p) hU ≫ q
    rw [germ_stalkMap_stalkClosedPointTo σ p hσp π U hU hU']
    revert hU'
    rw [hσ₁]
    intro hU'
    exact Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk q U hU'
  have hD1 : ∀ z : X₁.presheaf.stalk (π.base p),
      τ ((π.stalkMap p).hom z) = Ideal.Quotient.mk I z :=
    fun z => congrArg (fun φ => φ.hom z) hD1cat
  have hD2cat :
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (Spec (CommRingCat.of A)).presheaf.germ ⊤ (β.base p) trivial ≫
        β.stalkMap p ≫ τ = CommRingCat.ofHom a := by
    change (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (Spec (CommRingCat.of A)).presheaf.germ ⊤ (β.base p) trivial ≫
        β.stalkMap p ≫ e.inv ≫ Scheme.stalkClosedPointTo σ = CommRingCat.ofHom a
    rw [germ_stalkMap_stalkClosedPointTo σ p hσp β ⊤ trivial trivial, hσ₂,
      Scheme.germ_stalkClosedPointTo_Spec, Iso.inv_hom_id_assoc]
  have hD2 : ∀ t : A, τ (baseAt β p t) = a t := by
    intro t
    have h := congrArg (fun φ => φ.hom t) hD2cat
    change τ ((β.stalkMap p).hom (StructureSheaf.toStalk A (β.base p) t)) = a t at h
    rw [hts] at h
    exact h
  have hmem : τ.hom ((π.stalkMap p).hom r) ∈ Ideal.map (τ.hom.comp (baseAt β p)) (maximalIdeal A)
    := by
    rw [← Ideal.map_map]; exact Ideal.mem_map_of_mem _ hr
  have hcomp : τ.hom.comp (baseAt β p) = a := RingHom.ext hD2
  have hbot : Ideal.map a (maximalIdeal A) = ⊥ := by
    rw [Ideal.map_eq_bot_iff_le_ker]; intro t ht; exact ha0 t ht
  rw [hcomp, hbot, Ideal.mem_bot] at hmem
  have : Ideal.Quotient.mk I r = 0 := (hD1 r).symm.trans hmem
  exact Ideal.Quotient.eq_zero_iff_mem.mp this

end scheme

end CFStalk

open CFStalk in
theorem
  _root_.AlgebraicGeometry.mem_map_maximalIdeal_of_stalkMap_mem_map_maximalIdeal_of_iso_pullback
    {A A₁ : Type u} [CommRing A] [IsLocalRing A] [CommRing A₁] [IsLocalRing A₁]
    (ι₁ : A₁ →+* A) [IsLocalHom ι₁] (hres₁ : Function.Surjective ((IsLocalRing.residue A).comp ι₁))
    {X X₁ : Scheme.{u}} (toBase : X ⟶ Spec (CommRingCat.of A)) (f₁ : X₁ ⟶ Spec (CommRingCat.of A₁))
    (e₁ : X ≅ pullback f₁ (Spec.map (CommRingCat.ofHom ι₁)))
    (he₁ : e₁.hom ≫ pullback.snd f₁ (Spec.map (CommRingCat.ofHom ι₁)) = toBase)
    (x : X) (hx : toBase.base x = IsLocalRing.closedPoint A)
    (r : X₁.presheaf.stalk ((e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x))
    (hr : ((e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).stalkMap x).hom r ∈
      Ideal.map ((X.presheaf.germ ⊤ x trivial).hom.comp
        (toBase.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
        (IsLocalRing.maximalIdeal A)) :
    r ∈ Ideal.map ((X₁.presheaf.germ ⊤ ((e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom
      ι₁))).base x)
        trivial).hom.comp (f₁.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom))
      (IsLocalRing.maximalIdeal A₁) := by
  have hP : IsPullback (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))) toBase f₁
      (Spec.map (CommRingCat.ofHom ι₁)) :=
    IsPullback.of_iso_pullback
      ⟨by rw [Category.assoc, pullback.condition, ← Category.assoc, he₁]⟩ e₁ rfl he₁
  exact core ι₁ hres₁ f₁ _ toBase hP x hx r hr
end mem_map_maximalIdeal_of_stalkMap_mem_map_maximalIdeal_of_iso_pullback
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation

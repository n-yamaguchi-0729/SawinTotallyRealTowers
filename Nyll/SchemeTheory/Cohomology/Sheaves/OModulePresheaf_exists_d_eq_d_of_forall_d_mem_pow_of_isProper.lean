/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_of_isProper.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafConstructions
import Nyll.SchemeTheory.Cohomology.Cech.OModulePresheaf_cechFinite_of_isProper
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheaf_d_comp_d

/-!
# Ideal-power control of proper Čech coboundaries

The Rees algebra and proper Čech finiteness give a uniform loss of ideal power when
replacing a zero-cochain by one with the same coboundary.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs.ReesCechApproximation
attribute [-instance]
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul
  AlgebraicGeometry.OModulePresheaf.Leray.biC_module
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
  DoubleComplex.instModuleE₂I
  DoubleComplex.Bounded.modR
  DoubleComplex.instModuleE₂II
  DoubleComplex.instAddCommGroupE₂II
  DoubleComplex.Bounded.abGrp
  DoubleComplex.instAddCommGroupE₂I
  AlgebraicGeometry.ChowDatum.hι_closed
  AlgebraicGeometry.ChowDatumProj.hιN_closed
  AlgebraicGeometry.ChowDatumProj.hp_proper
  AlgebraicGeometry.ChowDatum.hp_isoU
  AlgebraicGeometry.ChowDatum.hp_proper
  AlgebraicGeometry.ProjSpace.algebraAway
  AlgebraicGeometry.ProjSpace.instIsProperProdOverπ
  AlgebraicGeometry.ChowDatumProj.hp_isoU
  AlgebraicGeometry.ProjSpace.isProper_π
  AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
  ProjSpaceCech.GradedModule.H.module
  ProjSpaceCech.GradedModule.H.addCommGroup
  ProjSpaceCech.GradedModule.sec.instAdd
  ProjSpaceCech.GradedModule.sec.instNeg
  ProjSpaceCech.GradedModule.acg
  ProjSpaceCech.GradedModule.Frac.setoid
  ProjSpaceCech.GradedModule.modR
  ProjSpaceCech.GradedModule.sec.instModule
  ProjSpaceCech.GradedModule.sec.instAddCommGroup
  ProjSpaceCech.GradedModule.sec.instZero
  ProjSpaceCech.GradedModule.Presentation.fJ
attribute [-instance]
  ProjSpaceCech.GradedModule.sec.instSMul
  ProjSpaceCech.Twist.H.module
  ProjSpaceCech.Idx.instFintype
  ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq
  ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup
  ProjSpaceCech.Twist.cochain.instModule
attribute [-simp]
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
  DoubleComplex.Bounded.mk.injEq
  DoubleComplex.Bounded.mk.sizeOf_spec
  DoubleComplex.Convergence.mk.injEq
  DoubleComplex.Convergence.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.injEq
  AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatumProj.mk.injEq
  AlgebraicGeometry.ChowDatum.mk.injEq
  ProjSpaceCech.GradedModule.mk.injEq
  ProjSpaceCech.GradedModule.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Presentation.mk.injEq
  ProjSpaceCech.GradedModule.Frac.mk.injEq
  ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap
  ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite
open _root_.TopologicalSpace
open _root_.AlgebraicGeometry
open _root_.Polynomial

universe u

noncomputable section

namespace SolKS

private lemma le_preimage_top {Y Z : Scheme.{u}} (f : Y ⟶ Z) (W : Y.Opens) :
    W ≤ f ⁻¹ᵁ ⊤ := by
  rw [Scheme.Hom.preimage_top]
  exact le_top

lemma preimage_iInf {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type*} [Finite ι] (U : ι → Y.Opens) :
    f ⁻¹ᵁ (⨅ j, U j) = ⨅ j, f ⁻¹ᵁ (U j) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  rw [← Finset.inf_univ_eq_iInf, ← Finset.inf_univ_eq_iInf]
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.inf_insert, Finset.inf_insert, Scheme.Hom.preimage_inf, ih]

lemma appLE_congr_hom {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (h : f = g) (U : Z.Opens) (V : Y.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

section Setup

variable {A : Type u} [CommRing A] (I : Ideal A) {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A))

/-- The Rees algebra of the ideal, retained as a named coefficient ring. -/
def Rr : Type u := ↥(reesAlgebra I)

scoped instance : CommRing (Rr I) := inferInstanceAs (CommRing ↥(reesAlgebra I))
scoped instance : Algebra A (Rr I) := inferInstanceAs (Algebra A ↥(reesAlgebra I))
scoped instance [IsNoetherianRing A] : IsNoetherianRing (Rr I) :=
  inferInstanceAs (IsNoetherianRing ↥(reesAlgebra I))

/-- The polynomial represented by an element of the Rees algebra. -/
abbrev Rr.val (r : Rr I) : A[X] := (show ↥(reesAlgebra I) from r).1

lemma Rr.coeff_mem (r : Rr I) (i : ℕ) : (Rr.val I r).coeff i ∈ I ^ i :=
  (mem_reesAlgebra_iff _ _).mp (show ↥(reesAlgebra I) from r).2 i

/-- View a polynomial satisfying the Rees coefficient conditions as an element of `Rr`. -/
abbrev Rr.mk (p : A[X]) (hp : p ∈ reesAlgebra I) : Rr I := (show ↥(reesAlgebra I) from ⟨p, hp⟩)

/-- The canonical inclusion of the Rees algebra into the polynomial ring. -/
abbrev Rr.incl : Rr I →+* A[X] := (reesAlgebra I).val.toRingHom

/-- The structure morphism from the spectrum of the Rees algebra to the base. -/
abbrev sA : Spec (CommRingCat.of (Rr I)) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (Rr I)))

/-- The spectrum morphism induced by the inclusion of the Rees algebra. -/
abbrev sX : Spec (CommRingCat.of A[X]) ⟶ Spec (CommRingCat.of (Rr I)) :=
  Spec.map (CommRingCat.ofHom (Rr.incl I))

/-- The base change of the proper scheme to the Rees algebra. -/
abbrev P' : Scheme.{u} := pullback q (sA I)

/-- The projection from the Rees base change to the original scheme. -/
abbrev fst' : P' I q ⟶ P := pullback.fst q (sA I)

/-- The structure morphism of the Rees base change. -/
abbrev π' : P' I q ⟶ Spec (CommRingCat.of (Rr I)) := pullback.snd q (sA I)

/-- The further base change from the Rees algebra to the polynomial ring. -/
abbrev P₁ : Scheme.{u} := pullback (π' I q) (sX I)

/-- The projection from the polynomial base change to the Rees base change. -/
abbrev g : P₁ I q ⟶ P' I q := pullback.fst (π' I q) (sX I)

/-- The structure morphism of the polynomial base change. -/
abbrev snd₁ : P₁ I q ⟶ Spec (CommRingCat.of A[X]) := pullback.snd (π' I q) (sX I)

/-- The composite projection from the polynomial base change to the original scheme. -/
abbrev p₁ : P₁ I q ⟶ P := g I q ≫ fst' I q

lemma sX_sA : sX I ≫ sA I = Spec.map (CommRingCat.ofHom (algebraMap A A[X])) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

lemma isPullback_P' : IsPullback (fst' I q) (π' I q) q (sA I) := IsPullback.of_hasPullback _ _

lemma isPullback_P₁ :
    IsPullback (p₁ I q) (snd₁ I q) q (Spec.map (CommRingCat.ofHom (algebraMap A A[X]))) := by
  rw [← sX_sA]
  exact IsPullback.paste_horiz (IsPullback.of_hasPullback (π' I q) (sX I)) (isPullback_P' I q)

scoped instance : IsAffineHom (g I q) := by
  have hBase : MorphismProperty.IsStableUnderBaseChange (@IsAffineHom.{u}) :=
    isAffineHom_isStableUnderBaseChange
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom.{u})
    (self := hBase) (IsPullback.of_hasPullback (π' I q) (sX I)).flip
    (isAffineHom_of_isAffine (sX I))
scoped instance : IsAffineHom (fst' I q) := by
  have hBase : MorphismProperty.IsStableUnderBaseChange (@IsAffineHom.{u}) :=
    isAffineHom_isStableUnderBaseChange
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom.{u})
    (self := hBase) (isPullback_P' I q).flip (isAffineHom_of_isAffine (sA I))

/-- The base-ring action on sections over an open of the original scheme. -/
def alg (U : P.Opens) : A →+* Γ(P, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ U (le_preimage_top q U)).hom

lemma alg_res {U V : P.Opens} (h : V ≤ U) (a : A) :
    P.presheaf.map (homOfLE h).op (alg q U a) = alg q V a := by
  simp only [alg, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

/-- The section obtained by pulling back the polynomial variable. -/
def T (W : (P₁ I q).Opens) : Γ(P₁ I q, W) :=
  ((snd₁ I q).appLE ⊤ W (le_preimage_top (snd₁ I q) W)).hom
    ((Scheme.ΓSpecIso (CommRingCat.of A[X])).inv.hom X)

/-- Evaluate a polynomial in sections at the pulled-back polynomial variable. -/
def θ (U : P.Opens) (W : (P₁ I q).Opens) (e : W ≤ p₁ I q ⁻¹ᵁ U) : Γ(P, U)[X] →+* Γ(P₁ I q, W) :=
  eval₂RingHom ((p₁ I q).appLE U W e).hom (T I q W)

lemma θ_C (U : P.Opens) (W : (P₁ I q).Opens) (e : W ≤ p₁ I q ⁻¹ᵁ U) (c : Γ(P, U)) :
    θ I q U W e (C c) = ((p₁ I q).appLE U W e).hom c := by
  exact Polynomial.eval₂_C _ _

lemma θ_X (U : P.Opens) (W : (P₁ I q).Opens) (e : W ≤ p₁ I q ⁻¹ᵁ U) :
    θ I q U W e X = T I q W := by
  exact Polynomial.eval₂_X _ _

lemma appLE_top_top {Y Z : Scheme.{u}} (f : Y ⟶ Z) : f.appLE ⊤ ⊤ (le_preimage_top f ⊤) = f.appTop :=
  f.appLE_eq_app

lemma ΓSpecIso_inv_C (a : A) :
    (Scheme.ΓSpecIso (CommRingCat.of A[X])).inv.hom (C a) =
      ((Spec.map (CommRingCat.ofHom (algebraMap A A[X]))).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) := by
  have hn := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A A[X]))
  have := congrArg (fun ψ : CommRingCat.of A ⟶ _ => ψ.hom a) hn
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom,
    Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at this
  exact this

lemma θ_map (U : P.Opens) (W : (P₁ I q).Opens) (e : W ≤ p₁ I q ⁻¹ᵁ U) (r : A[X]) :
    θ I q U W e (Polynomial.map (alg q U) r) =
      ((snd₁ I q).appLE ⊤ W (le_preimage_top (snd₁ I q) W)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A[X])).inv.hom r) := by
  have key : ((θ I q U W e).comp (mapRingHom (alg q U))) =
      ((snd₁ I q).appLE ⊤ W (le_preimage_top (snd₁ I q) W)).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of A[X])).inv.hom := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, map_C, θ_C]
      have lhs : ((p₁ I q).appLE U W e).hom (alg q U a) =
          ((p₁ I q ≫ q).appLE ⊤ W (le_preimage_top (p₁ I q ≫ q) W)).hom
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) := by
        simp only [alg, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
        rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
      have rhs : ((snd₁ I q).appLE ⊤ W (le_preimage_top (snd₁ I q) W)).hom
            ((Scheme.ΓSpecIso (CommRingCat.of A[X])).inv.hom (C a)) =
          ((snd₁ I q ≫ Spec.map (CommRingCat.ofHom (algebraMap A A[X]))).appLE ⊤ W
            (le_preimage_top (snd₁ I q ≫ Spec.map (CommRingCat.ofHom (algebraMap A A[X]))) W)).hom
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) := by
        rw [ΓSpecIso_inv_C, ← appLE_top_top, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
      rw [lhs, rhs]
      exact congrArg (fun φ => (CommRingCat.Hom.hom φ)
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))
        (appLE_congr_hom (isPullback_P₁ I q).w ⊤ W _ _)
    · simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, map_X, θ_X, T]
  exact congrArg (fun φ : A[X] →+* Γ(P₁ I q, W) => φ r) key

lemma θ_res {U U' : P.Opens} {W W' : (P₁ I q).Opens} (e : W ≤ p₁ I q ⁻¹ᵁ U)
    (e' : W' ≤ p₁ I q ⁻¹ᵁ U') (hU : U' ≤ U) (hW : W' ≤ W) (p : Γ(P, U)[X]) :
    (P₁ I q).presheaf.map (homOfLE hW).op (θ I q U W e p) =
      θ I q U' W' e' (Polynomial.map (P.presheaf.map (homOfLE hU).op).hom p) := by
  have key : ((P₁ I q).presheaf.map (homOfLE hW).op).hom.comp (θ I q U W e) =
      (θ I q U' W' e').comp (mapRingHom (P.presheaf.map (homOfLE hU).op).hom) := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, map_C, θ_C]
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map,
        Scheme.Hom.map_appLE]
    · simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, map_X, θ_X, T]
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  exact congrArg (fun φ : Γ(P, U)[X] →+* Γ(P₁ I q, W') => φ p) key

lemma θ_bijective {U : P.Opens} (hU : IsAffineOpen U) {W : (P₁ I q).Opens}
    (hW : W = p₁ I q ⁻¹ᵁ U ⊓ snd₁ I q ⁻¹ᵁ ⊤) :
    Function.Bijective (θ I q U W (hW.le.trans inf_le_left)) := by
  have H := isPullback_P₁ I q
  have h1 := isIso_pushoutSection_of_isAffineOpen H (US := ⊤) (UT := ⊤) (UX := U)
    (le_preimage_top (Spec.map (CommRingCat.ofHom (algebraMap A A[X]))) ⊤)
    (le_preimage_top q U) hW (isAffineOpen_top _) (isAffineOpen_top _) hU
  have hP := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U)
    (le_preimage_top (Spec.map (CommRingCat.ofHom (algebraMap A A[X]))) ⊤)
    (le_preimage_top q U) hW).mp h1
  let ΦC : Γ(P, U) ⟶ CommRingCat.of Γ(P, U)[X] := CommRingCat.ofHom C
  let ΦX : Γ(Spec (CommRingCat.of A[X]), ⊤) ⟶ CommRingCat.of Γ(P, U)[X] :=
    (Scheme.ΓSpecIso (CommRingCat.of A[X])).hom ≫ CommRingCat.ofHom (mapRingHom (alg q U))
  have w : q.appLE ⊤ U (le_preimage_top q U) ≫ ΦC =
      (Spec.map (CommRingCat.ofHom (algebraMap A A[X]))).appLE ⊤ ⊤
        (le_preimage_top (Spec.map (CommRingCat.ofHom (algebraMap A A[X]))) ⊤) ≫ ΦX := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, ΦC, ΦX,
      CommRingCat.hom_ofHom, coe_mapRingHom]
    rw [appLE_top_top]
    change C ((q.appLE ⊤ U (le_preimage_top q U)).hom x) = Polynomial.map (alg q U)
      (((Spec.map (CommRingCat.ofHom (algebraMap A A[X]))).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of A[X])).hom).hom x)
    rw [Scheme.ΓSpecIso_naturality]
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom,
      Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, map_C]
    congr 1
    simp only [alg, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Iso.hom_inv_id_assoc]
  let Φ : Γ(P₁ I q, W) ⟶ CommRingCat.of Γ(P, U)[X] := hP.desc ΦC ΦX w
  have hΦl : (p₁ I q).appLE U W _ ≫ Φ = ΦC := hP.inl_desc _ _ _
  have hΦr : (snd₁ I q).appLE ⊤ W _ ≫ Φ = ΦX := hP.inr_desc _ _ _
  set θ' := θ I q U W (hW.le.trans inf_le_left)
  have h1 : Φ.hom.comp θ' = RingHom.id _ := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · simp only [RingHom.coe_comp, Function.comp_apply, θ', θ_C, RingHom.id_apply]
      change (((p₁ I q).appLE U W _) ≫ Φ).hom c = C c
      rw [hΦl]; rfl
    · simp only [RingHom.coe_comp, Function.comp_apply, θ', θ_X, T, RingHom.id_apply]
      change ((snd₁ I q).appLE ⊤ W _ ≫ Φ).hom _ = X
      rw [hΦr]
      change Polynomial.map (alg q U) (((Scheme.ΓSpecIso (CommRingCat.of A[X])).inv ≫
        (Scheme.ΓSpecIso (CommRingCat.of A[X])).hom).hom X) = X
      rw [Iso.inv_hom_id]
      change Polynomial.map (alg q U) X = X
      exact Polynomial.map_X (alg q U)
  have h2 : Φ ≫ CommRingCat.ofHom θ' = 𝟙 _ := by
    refine hP.hom_ext ?_ ?_
    · rw [← Category.assoc, hΦl, Category.comp_id]
      ext c
      exact θ_C I q U W _ c
    · rw [← Category.assoc, hΦr, Category.comp_id]
      ext r
      change θ' (Polynomial.map (alg q U) ((Scheme.ΓSpecIso (CommRingCat.of A[X])).hom.hom r)) = _
      rw [θ_map]
      congr 1
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
  constructor
  · intro x y hxy
    have := congrArg Φ.hom hxy
    rwa [← RingHom.comp_apply, ← RingHom.comp_apply, h1] at this
  · intro z
    refine ⟨Φ.hom z, ?_⟩
    change (Φ ≫ CommRingCat.ofHom θ').hom z = z
    rw [h2]; rfl

lemma closure_eq_top {U : P.Opens} (hU : IsAffineOpen U) {W' : (P' I q).Opens}
    (hW' : W' = fst' I q ⁻¹ᵁ U ⊓ π' I q ⁻¹ᵁ ⊤) :
    Subring.closure (Set.range ((fst' I q).appLE U W' (hW'.le.trans inf_le_left)).hom ∪
      Set.range ((π' I q).appLE ⊤ W' (le_preimage_top (π' I q) W')).hom) = ⊤ := by
  have H := isPullback_P' I q
  have h1 := isIso_pushoutSection_of_isAffineOpen H (US := ⊤) (UT := ⊤) (UX := U)
      (le_preimage_top (sA I) ⊤) (le_preimage_top q U) hW'
        (isAffineOpen_top _) (isAffineOpen_top _) hU
  have hP := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U)
    (le_preimage_top (sA I) ⊤) (le_preimage_top q U) hW').mp h1
  exact CommRingCat.closure_range_union_range_eq_top_of_isPushout hP

/-- The Rees-algebra action on sections of the Rees base change. -/
def algR (W' : (P' I q).Opens) : Rr I →+* Γ(P' I q, W') :=
  ((Scheme.ΓSpecIso (CommRingCat.of (Rr I))).inv ≫ (π' I q).appLE ⊤ W'
    (le_preimage_top (π' I q) W')).hom

/-- The Rees-algebra action on sections of the polynomial base change. -/
def algR₁ (W : (P₁ I q).Opens) : Rr I →+* Γ(P₁ I q, W) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (Rr I))).inv ≫ (g I q ≫ π' I q).appLE ⊤ W
    (le_preimage_top (g I q ≫ π' I q) W)).hom

lemma algR₁_eq_θ (U : P.Opens) (W : (P₁ I q).Opens) (e : W ≤ p₁ I q ⁻¹ᵁ U) (r : Rr I) :
    algR₁ I q W r = θ I q U W e (Polynomial.map (alg q U) (Rr.val I r)) := by
  rw [θ_map]
  simp only [algR₁, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [appLE_congr_hom (pullback.condition (f := π' I q) (g := sX I)) ⊤ W _
    (le_preimage_top (snd₁ I q ≫ sX I) W),
    ← Scheme.Hom.appLE_comp_appLE (snd₁ I q) (sX I) ⊤ ⊤ W
        (le_preimage_top (sX I) ⊤) (le_preimage_top (snd₁ I q) W),
          CommRingCat.comp_apply, appLE_top_top]
  congr 1
  have hn := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Rr.incl I))
  have := congrArg (fun ψ : CommRingCat.of (Rr I) ⟶ _ => ψ.hom r) hn
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom] at this
  exact this.symm

lemma g_appLE_algR (W' : (P' I q).Opens) (r : Rr I) :
    ((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom (algR I q W' r) = algR₁ I q (g I q ⁻¹ᵁ W') r := by
  simp only [algR, algR₁, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

lemma algR_res {W W' : (P' I q).Opens} (h : W ≤ W') (r : Rr I) :
    (P' I q).presheaf.map (homOfLE h).op (algR I q W' r) = algR I q W r := by
  simp only [algR, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

lemma g_appLE_res {W W' : (P' I q).Opens} (h : W ≤ W') (x : Γ(P' I q, W')) :
    (P₁ I q).presheaf.map (homOfLE ((g I q).preimage_mono h)).op
        (((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom x) =
      ((g I q).appLE W (g I q ⁻¹ᵁ W) le_rfl).hom ((P' I q).presheaf.map (homOfLE h).op x) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map,
    Scheme.Hom.map_appLE]

/-- Pullback of structure sections along the polynomial base-change projection. -/
def φg : OModulePresheaf.Hom (OModulePresheaf.unit (π' I q))
    (OModulePresheaf.pushforwardUnit (π' I q) (g I q)) where
  app W' :=
    { toFun := fun x => ((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x => by
        change ((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom
            (algR I q W' r * (show Γ(P' I q, W') from x)) =
          algR₁ I q (g I q ⁻¹ᵁ W') r * ((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom x
        rw [map_mul, g_appLE_algR] }
  app_smul W' a x := by
    change ((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom (a * (show Γ(P' I q, W') from x)) =
      ((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom a *
        ((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom x
    exact map_mul _ a x
  naturality {W W'} h := by
    refine LinearMap.ext fun x => ?_
    exact (g_appLE_res I q h x).symm

lemma φg_app (W' : (P' I q).Opens) (x : Γ(P' I q, W')) :
    (φg I q).app W' x = ((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom x := rfl

/-- The image presheaf of sections pulled back from the Rees base change. -/
abbrev F' : OModulePresheaf (π' I q) := OModulePresheaf.im (φg I q)

/-- The section of the polynomial base change underlying an image-presheaf section. -/
abbrev F'val {W' : (P' I q).Opens} (y : (F' I q).obj W') : Γ(P₁ I q, g I q ⁻¹ᵁ W') := y.1

lemma F'_exists {W' : (P' I q).Opens} (y : (F' I q).obj W') :
    ∃ x, ((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom x = F'val I q y :=
  LinearMap.mem_range.mp y.2

lemma mem_F'_iff (W' : (P' I q).Opens)
    (y : (OModulePresheaf.pushforwardUnit (π' I q) (g I q)).obj W') :
    y ∈ LinearMap.range ((φg I q).app W') ↔
      ∃ x, ((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom x = (show Γ(P₁ I q, g I q ⁻¹ᵁ W') from y) :=
  LinearMap.mem_range

lemma F'_res_val {W W' : (P' I q).Opens} (h : W ≤ W') (y : (F' I q).obj W') :
    F'val I q ((F' I q).res h y) =
      (P₁ I q).presheaf.map (homOfLE ((g I q).preimage_mono h)).op (F'val I q y) := rfl

lemma F'_smul_val (W' : (P' I q).Opens) (a : Γ(P' I q, W')) (y : (F' I q).obj W') :
    F'val I q (a • y) = ((g I q).appLE W' (g I q ⁻¹ᵁ W') le_rfl).hom a * F'val I q y := rfl

lemma F'_rsmul_val (W' : (P' I q).Opens) (r : Rr I) (y : (F' I q).obj W') :
    F'val I q (r • y) = algR₁ I q (g I q ⁻¹ᵁ W') r * F'val I q y := rfl

lemma F'_add_val (W' : (P' I q).Opens) (y y' : (F' I q).obj W') :
    F'val I q (y + y') = F'val I q y + F'val I q y' := rfl

lemma F'_zero_val (W' : (P' I q).Opens) : F'val I q (0 : (F' I q).obj W') = 0 := rfl

lemma F'_ext {W' : (P' I q).Opens} {y y' : (F' I q).obj W'} (h : F'val I q y = F'val I q y') :
    y = y' := Subtype.ext h

lemma isCoherent_F' : (F' I q).IsCoherent := fun U => by
  have : Module.Finite Γ(P' I q, U.1) ((OModulePresheaf.unit (π' I q)).obj U.1) :=
    inferInstanceAs (Module.Finite Γ(P' I q, U.1) Γ(P' I q, U.1))
  exact Module.Finite.of_surjective ((OModulePresheaf.kerImSES (φg I q)).proj.appSections U.1)
    ((OModulePresheaf.kerImSES (φg I q)).surjective U.1)

lemma res_eq_zero_iff_of_eq {X : Scheme.{u}} {W V₁ V₂ : X.Opens} (h : V₁ = V₂) (e₁ : V₁ ≤ W)
    (e₂ : V₂ ≤ W) (s : Γ(X, W)) :
    X.presheaf.map (homOfLE e₁).op s = 0 ↔ X.presheaf.map (homOfLE e₂).op s = 0 := by
  subst h; rfl

lemma isQuasicoherent_F' : (F' I q).IsQuasicoherent := by
  intro U f
  have hle : (P' I q).basicOpen f ≤ U.1 := (P' I q).basicOpen_le f
  constructor
  · intro x
    obtain ⟨a', ha'⟩ := F'_exists I q x
    have := U.2.isLocalization_basicOpen f
    obtain ⟨⟨a₀, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers f) a'
    let a₀' : (OModulePresheaf.unit (π' I q)).obj U.1 := a₀
    let y : (F' I q).obj U.1 := ⟨(φg I q).app U.1 a₀', ⟨a₀', rfl⟩⟩
    refine ⟨n, y, F'_ext I q ?_⟩
    rw [F'_res_val, F'_smul_val, ← ha']
    change (P₁ I q).presheaf.map (homOfLE ((g I q).preimage_mono hle)).op
        (((g I q).appLE U.1 (g I q ⁻¹ᵁ U.1) le_rfl).hom a₀) = _
    dsimp only at h
    rw [mul_comm] at h
    change ((P' I q).presheaf.map (homOfLE hle).op).hom (f ^ n) * a' =
      ((P' I q).presheaf.map (homOfLE hle).op).hom a₀ at h
    rw [← map_mul, h, g_appLE_res]
  · intro y hy
    obtain ⟨x, hx⟩ := F'_exists I q y
    have h0 : (P₁ I q).presheaf.map (homOfLE ((g I q).preimage_mono hle)).op (F'val I q y) = 0 :=
      congrArg Subtype.val hy
    set f₁ : Γ(P₁ I q, g I q ⁻¹ᵁ U.1) := ((g I q).appLE U.1 (g I q ⁻¹ᵁ U.1) le_rfl).hom f with hf₁
    have hopen : g I q ⁻¹ᵁ (P' I q).basicOpen f = (P₁ I q).basicOpen f₁ := by
      rw [Scheme.preimage_basicOpen, hf₁, Scheme.Hom.appLE_eq_app]
    rw [res_eq_zero_iff_of_eq hopen _ ((P₁ I q).basicOpen_le f₁)] at h0
    have := (U.2.preimage (g I q)).isLocalization_basicOpen f₁
    have h0' : algebraMap Γ(P₁ I q, g I q ⁻¹ᵁ U.1) Γ(P₁ I q, (P₁ I q).basicOpen f₁)
        (F'val I q y) = 0 := by
      rw [RingHom.algebraMap_toAlgebra]; exact h0
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f₁) _ _).mp h0'
    refine ⟨n, F'_ext I q ?_⟩
    rw [F'_smul_val, map_pow]
    exact hn

variable (K : P.OrderedAffineCover)

/-- The ordered affine cover obtained by pulling back the original cover. -/
def K' : (P' I q).OrderedAffineCover where
  ι := K.ι
  U i := fst' I q ⁻¹ᵁ K.U i
  isAffineOpen i := (K.isAffineOpen i).preimage _
  iSup_eq_top := Scheme.Hom.iSup_preimage_eq_top _ K.iSup_eq_top

/-- Identify cover indices by retaining their increasing tuples under base change. -/
def indexEquiv {i : ℕ} : K.Idx i ≃ (K' I q K).Idx i where
  toFun s := ⟨s.1, s.2⟩
  invFun s := ⟨s.1, s.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

lemma indexEquiv_face {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2)) :
    (K' I q K).face (indexEquiv I q K s) j = indexEquiv I q K (K.face s j) := rfl

lemma K'_inter_le_inter_face {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2)) :
    (K' I q K).inter (indexEquiv I q K s) ≤
      (K' I q K).inter (indexEquiv I q K (K.face s j)) := by
  rw [← indexEquiv_face]
  exact (K' I q K).inter_le_inter_face (indexEquiv I q K s) j

lemma K'_inter {i : ℕ} (s : K.Idx i) :
    (K' I q K).inter (indexEquiv I q K s) = fst' I q ⁻¹ᵁ K.inter s :=
  (preimage_iInf (fst' I q) fun j => K.U (s.1 j)).symm

lemma hW' {i : ℕ} (s : K.Idx i) :
    (K' I q K).inter (indexEquiv I q K s) = fst' I q ⁻¹ᵁ K.inter s ⊓ π' I q ⁻¹ᵁ ⊤ := by
  rw [K'_inter, Scheme.Hom.preimage_top, inf_top_eq]

lemma hW {i : ℕ} (s : K.Idx i) :
    g I q ⁻¹ᵁ (K' I q K).inter (indexEquiv I q K s) = p₁ I q ⁻¹ᵁ K.inter s ⊓ snd₁ I q ⁻¹ᵁ ⊤ := by
  rw [K'_inter, Scheme.Hom.preimage_top, inf_top_eq, Scheme.Hom.comp_preimage]

lemma e_s {i : ℕ} (s : K.Idx i) :
    g I q ⁻¹ᵁ (K' I q K).inter (indexEquiv I q K s) ≤ p₁ I q ⁻¹ᵁ K.inter s :=
  (hW I q K s).le.trans inf_le_left

lemma e'_s {i : ℕ} (s : K.Idx i) : (K' I q K).inter (indexEquiv I q K s) ≤ fst' I q ⁻¹ᵁ K.inter s :=
  (hW' I q K s).le.trans inf_le_left

/-- Evaluate the differential with indices and restriction modules transported together. -/
lemma d_reindex_apply (i : ℕ) (z : (F' I q).cochain (K' I q K) i)
    (s : K.Idx (i + 1)) :
    (F' I q).d (K' I q K) i z (indexEquiv I q K s) =
      ∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        (F' I q).res (K'_inter_le_inter_face I q K s j)
          (z (indexEquiv I q K (K.face s j))) :=
  (F' I q).d_apply (K' I q K) i z (indexEquiv I q K s)

end Setup

section Cochains

variable {A : Type u} [CommRing A] (I : Ideal A) {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A))
  [IsSeparated q] (K : P.OrderedAffineCover)

include q in
lemma haff {i : ℕ} (s : K.Idx i) : IsAffineOpen (K.inter s) := K.isAffineOpen_inter q s

/-- Identify sections on a polynomial base change with polynomials in affine sections. -/
def ΦC {i : ℕ} (s : K.Idx i) :
    Γ(P₁ I q, g I q ⁻¹ᵁ (K' I q K).inter (indexEquiv I q K s)) ≃+* Γ(P, K.inter s)[X] :=
  (RingEquiv.ofBijective (θ I q (K.inter s)
      (g I q ⁻¹ᵁ (K' I q K).inter (indexEquiv I q K s)) (e_s I q K s))
    (θ_bijective I q (haff q K s) (hW I q K s))).symm

lemma ΦC_θ {i : ℕ} (s : K.Idx i) (p : Γ(P, K.inter s)[X]) :
    ΦC I q K s (θ I q (K.inter s)
      (g I q ⁻¹ᵁ (K' I q K).inter (indexEquiv I q K s)) (e_s I q K s) p) = p :=
  (RingEquiv.ofBijective _ (θ_bijective I q (haff q K s) (hW I q K s))).symm_apply_apply p

lemma θ_ΦC {i : ℕ} (s : K.Idx i) (v : Γ(P₁ I q, g I q ⁻¹ᵁ (K' I q K).inter (indexEquiv I q K s))) :
    θ I q (K.inter s) (g I q ⁻¹ᵁ (K' I q K).inter (indexEquiv I q K s))
      (e_s I q K s) (ΦC I q K s v) = v :=
  (RingEquiv.ofBijective _ (θ_bijective I q (haff q K s) (hW I q K s))).apply_symm_apply v

lemma ΦC_res {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2))
    (v : Γ(P₁ I q, g I q ⁻¹ᵁ (K' I q K).inter (indexEquiv I q K (K.face s j)))) :
    ΦC I q K s ((P₁ I q).presheaf.map
        (homOfLE ((g I q).preimage_mono (K'_inter_le_inter_face I q K s j))).op v) =
      Polynomial.map (P.presheaf.map (homOfLE (K.inter_le_inter_face s j)).op).hom
        (ΦC I q K (K.face s j) v) := by
  have h := θ_res I q (e_s I q K (K.face s j)) (e_s I q K s) (K.inter_le_inter_face s j)
    ((g I q).preimage_mono (K'_inter_le_inter_face I q K s j)) (ΦC I q K (K.face s j) v)
  rw [θ_ΦC] at h
  exact (congrArg (ΦC I q K s) h).trans (ΦC_θ I q K s _)

lemma ΦC_algR₁ {i : ℕ} (s : K.Idx i) (r : Rr I) :
    ΦC I q K s (algR₁ I q _ r) = Polynomial.map (alg q (K.inter s)) (Rr.val I r) := by
  rw [algR₁_eq_θ I q (K.inter s) _ (e_s I q K s), ΦC_θ]

/-- Extract one polynomial coefficient from a cochain of the image presheaf. -/
def coeffC (i j : ℕ) (z : (F' I q).cochain (K' I q K) i) : (OModulePresheaf.unit q).cochain K i :=
  fun s => (ΦC I q K s (F'val I q (z (indexEquiv I q K s)))).coeff j

lemma coeffC_apply (i j : ℕ) (z : (F' I q).cochain (K' I q K) i) (s : K.Idx i) :
    coeffC I q K i j z s = (ΦC I q K s (F'val I q (z (indexEquiv I q K s)))).coeff j := rfl

lemma coeffC_add (i j : ℕ) (z z' : (F' I q).cochain (K' I q K) i) :
    coeffC I q K i j (z + z') = coeffC I q K i j z + coeffC I q K i j z' := by
  funext s
  change (ΦC I q K s (F'val I q
      (z (indexEquiv I q K s) + z' (indexEquiv I q K s)))).coeff j =
    (ΦC I q K s (F'val I q (z (indexEquiv I q K s)))).coeff j +
      (ΦC I q K s (F'val I q (z' (indexEquiv I q K s)))).coeff j
  rw [F'_add_val, map_add, coeff_add]

lemma coeffC_zero (i j : ℕ) : coeffC I q K i j 0 = 0 := by
  funext s
  change (ΦC I q K s (F'val I q (0 : (F' I q).obj _))).coeff j = 0
  rw [F'_zero_val, map_zero, coeff_zero]

lemma coeffC_sub (i j : ℕ) (z z' : (F' I q).cochain (K' I q K) i) :
    coeffC I q K i j (z - z') = coeffC I q K i j z - coeffC I q K i j z' := by
  rw [eq_sub_iff_add_eq, ← coeffC_add, sub_add_cancel]

/-- The additive map forgetting membership in the image presheaf. -/
def F'valHom (W' : (P' I q).Opens) : (F' I q).obj W' →+ Γ(P₁ I q, g I q ⁻¹ᵁ W') :=
  { toFun := F'val I q, map_zero' := rfl, map_add' := fun _ _ => rfl }

omit [IsSeparated q] in
lemma F'valHom_apply (W' : (P' I q).Opens) (y : (F' I q).obj W') :
    F'valHom I q W' y = F'val I q y := rfl

lemma coeffC_d (i j : ℕ) (z : (F' I q).cochain (K' I q K) i) :
    coeffC I q K (i + 1) j ((F' I q).d (K' I q K) i z) =
      (OModulePresheaf.unit q).d K i (coeffC I q K i j z) := by
  funext s
  rw [coeffC_apply, d_reindex_apply, OModulePresheaf.d_apply]
  change _ = ∑ j' : Fin (i + 2), ((-1 : ℤ) ^ (j' : ℕ)) •
    (P.presheaf.map (homOfLE (K.inter_le_inter_face s j')).op).hom
      (coeffC I q K i j z (K.face s j'))
  rw [← F'valHom_apply, map_sum, map_sum, ← lcoeff_apply, map_sum]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [map_zsmul, map_zsmul, map_zsmul, lcoeff_apply, F'valHom_apply, F'_res_val, ΦC_res, coeff_map]
  rfl

lemma coeffC_smul (i j : ℕ) (r : Rr I) (z : (F' I q).cochain (K' I q K) i) :
    coeffC I q K i j (r • z) =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal j,
        ((Rr.val I r).coeff x.1) • coeffC I q K i x.2 z := by
  funext s
  rw [Finset.sum_apply, coeffC_apply, Pi.smul_apply, F'_rsmul_val, map_mul, ΦC_algR₁, coeff_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [coeff_map]
  rfl

lemma coeffC_mem (i j : ℕ) (z : (F' I q).cochain (K' I q K) i) (s : K.Idx i) :
    (show Γ(P, K.inter s) from coeffC I q K i j z s) ∈
      Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        q.appLE ⊤ (K.inter s) (le_preimage_top q (K.inter s))).hom
        (I ^ j) := by
  obtain ⟨x, hx⟩ := F'_exists I q (z (indexEquiv I q K s))
  rw [coeffC_apply, ← hx]
  set J : Ideal Γ(P, K.inter s) := I.map (alg q (K.inter s)) with hJ
  let S : Subring Γ(P' I q, (K' I q K).inter (indexEquiv I q K s)) :=
    (reesAlgebra J).toSubring.comap
      ((ΦC I q K s).toRingHom.comp
        ((g I q).appLE ((K' I q K).inter (indexEquiv I q K s)) _ le_rfl).hom)
  have hS : Subring.closure (Set.range ((fst' I q).appLE (K.inter s)
      ((K' I q K).inter (indexEquiv I q K s))
      (e'_s I q K s)).hom ∪ Set.range ((π' I q).appLE ⊤ ((K' I q K).inter (indexEquiv I q K s))
        (le_preimage_top (π' I q) ((K' I q K).inter (indexEquiv I q K s)))).hom) ≤ S := by
    rw [Subring.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨r₀, rfl⟩)
    · change ΦC I q K s (((g I q).appLE ((K' I q K).inter (indexEquiv I q K s)) _ le_rfl).hom
        (((fst' I q).appLE (K.inter s) ((K' I q K).inter (indexEquiv I q K s))
          (e'_s I q K s)).hom c)) ∈ reesAlgebra J
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, ← θ_C I q _ _ (e_s I q K s), ΦC_θ]
      exact Subalgebra.algebraMap_mem (reesAlgebra J) c
    · change ΦC I q K s (((g I q).appLE ((K' I q K).inter (indexEquiv I q K s)) _ le_rfl).hom
        (((π' I q).appLE ⊤ ((K' I q K).inter (indexEquiv I q K s))
          (le_preimage_top (π' I q) ((K' I q K).inter (indexEquiv I q K s)))).hom r₀)) ∈
        reesAlgebra J
      have hr₀ : r₀ = (Scheme.ΓSpecIso (CommRingCat.of (Rr I))).inv.hom
          ((Scheme.ΓSpecIso (CommRingCat.of (Rr I))).hom.hom r₀) := by
        rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
      rw [hr₀]
      change ΦC I q K s (((g I q).appLE
        ((K' I q K).inter (indexEquiv I q K s)) _ le_rfl).hom (algR I q _ _)) ∈ _
      rw [g_appLE_algR, ΦC_algR₁]
      intro n
      rw [coeff_map, hJ, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ (Rr.coeff_mem I _ n)
  rw [closure_eq_top I q (haff q K s) (hW' I q K s)] at hS
  have hxS : x ∈ S := hS (Subring.mem_top x)
  have : ΦC I q K s (((g I q).appLE
      ((K' I q K).inter (indexEquiv I q K s)) _ le_rfl).hom x) ∈ reesAlgebra J := hxS
  have := (mem_reesAlgebra_iff _ _).mp this j
  rwa [hJ, ← Ideal.map_pow] at this

/-- Polynomials whose evaluations lift from sections of the Rees base change. -/
def Sθ {i : ℕ} (s : K.Idx i) : Subring Γ(P, K.inter s)[X] :=
  (((g I q).appLE ((K' I q K).inter (indexEquiv I q K s)) _ le_rfl).hom.range).comap
    (θ I q (K.inter s) (g I q ⁻¹ᵁ (K' I q K).inter (indexEquiv I q K s)) (e_s I q K s))

omit [IsSeparated q] in
lemma mem_range_of_mem_Sθ {i : ℕ} (s : K.Idx i) {p : Γ(P, K.inter s)[X]} (hp : p ∈ Sθ I q K s) :
    (show (OModulePresheaf.pushforwardUnit (π' I q) (g I q)).obj
      ((K' I q K).inter (indexEquiv I q K s)) from
      θ I q (K.inter s) (g I q ⁻¹ᵁ (K' I q K).inter (indexEquiv I q K s)) (e_s I q K s) p) ∈
      LinearMap.range ((φg I q).app ((K' I q K).inter (indexEquiv I q K s))) :=
  (mem_F'_iff I q _ _).mpr (RingHom.mem_range.mp (Subring.mem_comap.mp hp))

omit [IsSeparated q] in
lemma C_mem_Sθ {i : ℕ} (s : K.Idx i) (c : Γ(P, K.inter s)) : C c ∈ Sθ I q K s := by
  refine Subring.mem_comap.mpr (RingHom.mem_range.mpr
    ⟨((fst' I q).appLE (K.inter s)
      ((K' I q K).inter (indexEquiv I q K s)) (e'_s I q K s)).hom c, ?_⟩)
  rw [θ_C, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

omit [IsSeparated q] in
lemma map_mem_Sθ {i : ℕ} (s : K.Idx i) (r : Rr I) :
    Polynomial.map (alg q (K.inter s)) (Rr.val I r) ∈ Sθ I q K s := by
  refine Subring.mem_comap.mpr (RingHom.mem_range.mpr ⟨algR I q _ r, ?_⟩)
  rw [g_appLE_algR, algR₁_eq_θ I q (K.inter s) _ (e_s I q K s)]

omit [IsSeparated q] in
lemma monomial_mem_Sθ {i : ℕ} (s : K.Idx i) {k : ℕ} {x : Γ(P, K.inter s)}
    (hx : x ∈ Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      q.appLE ⊤ (K.inter s) (le_preimage_top q (K.inter s))).hom (I ^ k)) :
    monomial k x ∈ Sθ I q K s := by
  change x ∈ Ideal.map (alg q (K.inter s)) (I ^ k) at hx
  unfold Ideal.map at hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨a, ha, rfl⟩ := h
    have : monomial k (alg q (K.inter s) a) = Polynomial.map (alg q (K.inter s))
        (Rr.val I (Rr.mk I (monomial k a) (reesAlgebra.monomial_mem.mpr ha))) :=
      (Polynomial.map_monomial _).symm
    rw [this]
    exact map_mem_Sθ I q K s _
  | zero => rw [map_zero]; exact Subring.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Subring.add_mem _ hx hy
  | smul c x _ hx =>
    rw [smul_eq_mul, ← C_mul_monomial]
    exact Subring.mul_mem _ (C_mem_Sθ I q K s c) hx

/-- Lift a cochain with coefficients in an ideal power to a homogeneous Rees cochain. -/
def zC (i k : ℕ) (b : (OModulePresheaf.unit q).cochain K i)
    (hb : ∀ s : K.Idx i, b s ∈ Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      q.appLE ⊤ (K.inter s) (le_preimage_top q (K.inter s))).hom (I ^ k)) :
    (F' I q).cochain (K' I q K) i :=
  fun t =>
    let s : K.Idx i := (indexEquiv I q K).symm t
    ⟨_, mem_range_of_mem_Sθ I q K s (monomial_mem_Sθ I q K s (hb s))⟩

omit [IsSeparated q] in
lemma F'val_zC (i k : ℕ) (b : (OModulePresheaf.unit q).cochain K i)
    (hb : ∀ s : K.Idx i, b s ∈
      Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        q.appLE ⊤ (K.inter s) (le_preimage_top q (K.inter s))).hom (I ^ k)) (s : K.Idx i) :
    F'val I q (zC I q K i k b hb (indexEquiv I q K s)) =
      θ I q (K.inter s) (g I q ⁻¹ᵁ (K' I q K).inter (indexEquiv I q K s))
        (e_s I q K s) (monomial k (b s)) := rfl

lemma coeffC_zC (i k j : ℕ) (b : (OModulePresheaf.unit q).cochain K i)
    (hb : ∀ s : K.Idx i, b s ∈
      Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        q.appLE ⊤ (K.inter s) (le_preimage_top q (K.inter s))).hom (I ^ k)) :
    coeffC I q K i j (zC I q K i k b hb) = if j = k then b else 0 := by
  funext s
  rw [coeffC_apply, F'val_zC, ΦC_θ]
  let bs : Γ(P, K.inter s) := b s
  by_cases hj : j = k
  · have hcoef : (monomial k bs).coeff j = bs := by
      rw [hj]
      exact coeff_monomial_same k bs
    have hite : (if j = k then b else 0) = b := ite_eq_left hj
    exact hcoef.trans (congr_fun hite s).symm
  · have hcoef : (monomial k bs).coeff j = 0 := coeff_monomial_of_ne bs hj
    have hite : (if j = k then b else 0) = 0 := ite_eq_right hj
    exact hcoef.trans (congr_fun hite s).symm

omit [IsSeparated q] in
lemma F'val_d_zC (i k : ℕ) (b : (OModulePresheaf.unit q).cochain K i)
    (hb : ∀ s : K.Idx i, b s ∈
      Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        q.appLE ⊤ (K.inter s) (le_preimage_top q (K.inter s))).hom (I ^ k)) (s : K.Idx (i + 1)) :
    F'val I q ((F' I q).d (K' I q K) i (zC I q K i k b hb) (indexEquiv I q K s)) =
      θ I q (K.inter s) (g I q ⁻¹ᵁ (K' I q K).inter (indexEquiv I q K s)) (e_s I q K s)
        (monomial k ((OModulePresheaf.unit q).d K i b s)) := by
  rw [d_reindex_apply, OModulePresheaf.d_apply]
  change _ = θ I q (K.inter s) (g I q ⁻¹ᵁ (K' I q K).inter (indexEquiv I q K s)) (e_s I q K s)
    (monomial k (∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      (P.presheaf.map (homOfLE (K.inter_le_inter_face s j)).op).hom (b (K.face s j))))
  rw [← F'valHom_apply, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, map_zsmul, map_zsmul, F'valHom_apply, F'_res_val, F'val_zC,
    θ_res I q (e_s I q K (K.face s j)) (e_s I q K s) (K.inter_le_inter_face s j)]
  let bs : Γ(P, K.inter (K.face s j)) := b (K.face s j)
  let ρ : Γ(P, K.inter (K.face s j)) →+* Γ(P, K.inter s) :=
    (P.presheaf.map (homOfLE (K.inter_le_inter_face s j)).op).hom
  have hmap : Polynomial.map ρ (monomial k bs) = monomial k (ρ bs) :=
    Polynomial.map_monomial ρ (n := k) (a := bs)
  exact congrArg (fun p : Γ(P, K.inter s)[X] => ((-1 : ℤ) ^ (j : ℕ)) •
    θ I q (K.inter s) (g I q ⁻¹ᵁ (K' I q K).inter (indexEquiv I q K s)) (e_s I q K s) p) hmap

omit [IsSeparated q] in
lemma d_zC_eq_zero (i k : ℕ) (b : (OModulePresheaf.unit q).cochain K i)
    (hb : ∀ s : K.Idx i, b s ∈
      Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        q.appLE ⊤ (K.inter s) (le_preimage_top q (K.inter s))).hom (I ^ k))
    (hdb : (OModulePresheaf.unit q).d K i b = 0) :
    (F' I q).d (K' I q K) i (zC I q K i k b hb) = 0 := by
  funext t
  obtain ⟨s, rfl⟩ := (indexEquiv I q K).surjective t
  apply F'_ext I q
  rw [F'val_d_zC]
  let dbs : Γ(P, K.inter s) := (OModulePresheaf.unit q).d K i b s
  have hdbs : dbs = 0 := congr_fun hdb s
  change θ I q (K.inter s) (g I q ⁻¹ᵁ (K' I q K).inter (indexEquiv I q K s))
      (e_s I q K s) (monomial k dbs) =
    F'val I q (0 : (F' I q).obj ((K' I q K).inter (indexEquiv I q K s)))
  rw [hdbs, map_zero, map_zero, F'_zero_val]

end Cochains

section Main

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {P : Scheme.{u}}
  (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q] (K : P.OrderedAffineCover)

/-- The submodule of zero-cochains taking values in a fixed power of the base ideal. -/
def IC (m : ℕ) : Submodule A ((OModulePresheaf.unit q).cochain K 0) where
  carrier := {w | ∀ s, (show Γ(P, K.inter s) from w s) ∈
    Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      q.appLE ⊤ (K.inter s) (le_preimage_top q (K.inter s))).hom (I ^ m)}
  add_mem' hw hw' s := Ideal.add_mem _ (hw s) (hw' s)
  zero_mem' _ := Ideal.zero_mem _
  smul_mem' a _ hw s := Ideal.mul_mem_left _ (alg q (K.inter s) a) (hw s)

omit [IsNoetherianRing A] [IsProper q] in
lemma mem_IC {m : ℕ} (w : (OModulePresheaf.unit q).cochain K 0) :
    w ∈ IC I q K m ↔ ∀ s, (show Γ(P, K.inter s) from w s) ∈
      Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        q.appLE ⊤ (K.inter s) (le_preimage_top q (K.inter s))).hom (I ^ m) := Iff.rfl

omit [IsNoetherianRing A] [IsProper q] in
lemma IC_anti {m m' : ℕ} (h : m ≤ m') : IC I q K m' ≤ IC I q K m := fun _ hw s =>
  Ideal.map_mono (Ideal.pow_le_pow_right h) (hw s)

omit [IsNoetherianRing A] [IsProper q] in
lemma smul_mem_IC {a : A} {l m : ℕ} (ha : a ∈ I ^ l) {w : (OModulePresheaf.unit q).cochain K 0}
    (hw : w ∈ IC I q K m) : a • w ∈ IC I q K (l + m) := by
  intro s
  change alg q (K.inter s) a * (show Γ(P, K.inter s) from w s) ∈
    Ideal.map (alg q (K.inter s)) (I ^ (l + m))
  rw [pow_add, Ideal.map_mul]
  exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ ha) (hw s)

/-- Coboundaries of zero-cochains whose values lie in the specified ideal power. -/
abbrev Dg (m : ℕ) : Submodule A ((OModulePresheaf.unit q).cochain K 1) :=
  (IC I q K m).map ((OModulePresheaf.unit q).d K 0)

/-- One-cocycles of the image presheaf on the Rees base change. -/
def Z1 : Submodule (Rr I) ((F' I q).cochain (K' I q K) (0 + 1)) :=
  LinearMap.ker ((F' I q).d (K' I q K) (0 + 1))

/-- One-coboundaries regarded as a submodule of the one-cocycles. -/
def B1 : Submodule (Rr I) (Z1 I q K) :=
  (LinearMap.range ((F' I q).d (K' I q K) 0)).comap (Z1 I q K).subtype

omit [IsNoetherianRing A] [IsProper q] in
lemma mem_Z1 (z : (F' I q).cochain (K' I q K) (0 + 1)) :
    z ∈ Z1 I q K ↔ (F' I q).d (K' I q K) (0 + 1) z = 0 := LinearMap.mem_ker

omit [IsNoetherianRing A] [IsProper q] in
lemma mem_B1 (z : Z1 I q K) :
    z ∈ B1 I q K ↔ ∃ w', (F' I q).d (K' I q K) 0 w' = z.1 := by
  unfold B1; rw [Submodule.mem_comap]; exact LinearMap.mem_range

/-- The first Čech cohomology module of the image presheaf. -/
def M : Type u := Z1 I q K ⧸ B1 I q K

scoped instance : AddCommGroup (M I q K) := Submodule.Quotient.addCommGroup _
scoped instance : Module (Rr I) (M I q K) := Submodule.Quotient.module _

scoped instance : Module.Finite (Rr I) (M I q K) :=
  (AlgebraicGeometry.OModulePresheaf.cechFinite_of_isProper (F' I q) (isCoherent_F' I q)
    (isQuasicoherent_F' I q) (K' I q K)).2 0

scoped instance : _root_.IsNoetherian (Rr I) (M I q K) :=
  isNoetherian_of_isNoetherianRing_of_finite (Rr I) (M I q K)

/-- The cohomology class of a one-cocycle. -/
def mkM (z : Z1 I q K) : M I q K := Submodule.Quotient.mk (p := B1 I q K) z

omit [IsNoetherianRing A] [IsProper q] in
lemma mkM_add (z z' : Z1 I q K) : mkM I q K (z + z') = mkM I q K z + mkM I q K z' := rfl
omit [IsNoetherianRing A] [IsProper q] in
lemma mkM_smul (r : Rr I) (z : Z1 I q K) : mkM I q K (r • z) = r • mkM I q K z := rfl
omit [IsNoetherianRing A] [IsProper q] in
lemma mkM_zero : mkM I q K 0 = 0 := rfl
omit [IsNoetherianRing A] [IsProper q] in
lemma mkM_eq_mkM {z z' : Z1 I q K} : mkM I q K z = mkM I q K z' ↔ z - z' ∈ B1 I q K :=
  Submodule.Quotient.eq _

/-- The homogeneous Rees cocycle attached to a coboundary in an ideal power. -/
def zZ (k : ℕ) (b : (OModulePresheaf.unit q).cochain K 1)
    (hb₁ : b ∈ LinearMap.range ((OModulePresheaf.unit q).d K 0))
    (hb₂ : ∀ s : K.Idx 1, b s ∈ Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      q.appLE ⊤ (K.inter s) (le_preimage_top q (K.inter s))).hom (I ^ k)) : Z1 I q K :=
  ⟨zC I q K 1 k b hb₂, (mem_Z1 I q K _).mpr (d_zC_eq_zero I q K 1 k b hb₂ (by
    obtain ⟨w, rfl⟩ := hb₁
    exact LinearMap.congr_fun (AlgebraicGeometry.OModulePresheaf.d_comp_d
      (OModulePresheaf.unit q) K 0) w))⟩

/-- The cohomology class attached to a coboundary in an ideal power. -/
def cls (k : ℕ) (b : (OModulePresheaf.unit q).cochain K 1)
    (hb₁ : b ∈ LinearMap.range ((OModulePresheaf.unit q).d K 0))
    (hb₂ : ∀ s : K.Idx 1, b s ∈ Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      q.appLE ⊤ (K.inter s) (le_preimage_top q (K.inter s))).hom (I ^ k)) : M I q K :=
  mkM I q K (zZ I q K k b hb₁ hb₂)

/-- Classes arising from ideal powers up to a specified degree. -/
def gens (m : ℕ) : Set (M I q K) :=
  {x | ∃ k, k ≤ m ∧ ∃ b hb₁ hb₂, x = cls I q K k b hb₁ hb₂}

/-- The Rees submodule generated by classes through a specified degree. -/
def N (m : ℕ) : Submodule (Rr I) (M I q K) := Submodule.span (Rr I) (gens I q K m)

omit [IsNoetherianRing A] [IsProper q] in
lemma N_mono : Monotone (N I q K) := fun _ _ h =>
  Submodule.span_mono fun _ ⟨k, hk, b, hb₁, hb₂, hx⟩ => ⟨k, hk.trans h, b, hb₁, hb₂, hx⟩

/-- A class has a representative whose coefficients are controlled coboundaries. -/
def Good (c₀ : ℕ) (x : M I q K) : Prop :=
  ∃ z : Z1 I q K, mkM I q K z = x ∧ ∀ j, coeffC I q K 1 j z.1 ∈ Dg I q K (j - c₀)

omit [IsNoetherianRing A] in
lemma good_of_mem (c₀ : ℕ) {x : M I q K} (hx : x ∈ N I q K c₀) : Good I q K c₀ x := by
  unfold N at hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨k, hk, b, hb₁, hb₂, rfl⟩ := h
    refine ⟨zZ I q K k b hb₁ hb₂, rfl, fun j => ?_⟩
    change coeffC I q K 1 j (zC I q K 1 k b hb₂) ∈ _
    rw [coeffC_zC]
    split_ifs with hj
    · subst hj
      obtain ⟨w, rfl⟩ := hb₁
      refine Submodule.mem_map.mpr ⟨w, fun s => ?_, rfl⟩
      rw [Nat.sub_eq_zero_of_le hk, pow_zero, Ideal.one_eq_top, Ideal.map_top]
      trivial
    · exact Submodule.zero_mem _
  | zero =>
    exact ⟨0, mkM_zero I q K, fun j => by
      rw [Submodule.coe_zero, coeffC_zero]; exact Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨z, rfl, hz⟩ := hx
    obtain ⟨z', rfl, hz'⟩ := hy
    refine ⟨z + z', mkM_add I q K z z', fun j => ?_⟩
    rw [Submodule.coe_add, coeffC_add]
    exact Submodule.add_mem _ (hz j) (hz' j)
  | smul r x _ hx =>
    obtain ⟨z, rfl, hz⟩ := hx
    refine ⟨r • z, mkM_smul I q K r z, fun j => ?_⟩
    rw [Submodule.coe_smul, coeffC_smul]
    refine Submodule.sum_mem _ fun x hx => ?_
    obtain ⟨w, hw, hdw⟩ := Submodule.mem_map.mp (hz x.2)
    rw [← hdw, ← LinearMap.map_smul]
    refine Submodule.mem_map.mpr ⟨_, IC_anti I q K ?_ (smul_mem_IC I q K (Rr.coeff_mem I r x.1) hw),
      rfl⟩
    have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    omega

theorem main (n : ℕ) :
    ∃ c : ℕ, ∀ w : (OModulePresheaf.unit q).cochain K 0,
      (∀ s : K.Idx 1, (OModulePresheaf.unit q).d K 0 w s ∈
        Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
          q.appLE ⊤ (K.inter s) (le_preimage_top q (K.inter s))).hom
          (I ^ (n + c))) →
      ∃ w' : (OModulePresheaf.unit q).cochain K 0,
        (∀ s : K.Idx 0, w' s ∈
          Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
            q.appLE ⊤ (K.inter s) (le_preimage_top q (K.inter s))).hom
            (I ^ n)) ∧
        (OModulePresheaf.unit q).d K 0 w' = (OModulePresheaf.unit q).d K 0 w := by
  obtain ⟨c₀, hc₀⟩ := (monotone_stabilizes_iff_noetherian (R := Rr I) (M := M I q K)).mpr
    inferInstance ⟨N I q K, N_mono I q K⟩
  refine ⟨c₀, fun w hw => ?_⟩
  set b := (OModulePresheaf.unit q).d K 0 w with hb
  have hb₁ : b ∈ LinearMap.range ((OModulePresheaf.unit q).d K 0) := ⟨w, rfl⟩
  have hmem : cls I q K (n + c₀) b hb₁ hw ∈ N I q K (n + c₀) :=
    Submodule.subset_span ⟨n + c₀, le_rfl, b, hb₁, hw, rfl⟩
  have hstab : N I q K c₀ = N I q K (n + c₀) := hc₀ (n + c₀) (Nat.le_add_left c₀ n)
  rw [← hstab] at hmem
  obtain ⟨z, hz, hgood⟩ := good_of_mem I q K c₀ hmem
  have hdiff : zZ I q K (n + c₀) b hb₁ hw - z ∈ B1 I q K := (mkM_eq_mkM I q K).mp hz.symm
  obtain ⟨w', hw'⟩ := (mem_B1 I q K _).mp hdiff
  change (F' I q).d (K' I q K) 0 w' = zC I q K 1 (n + c₀) b hw - z.1 at hw'
  have key := congrArg (coeffC I q K 1 (n + c₀)) hw'
  rw [coeffC_d, coeffC_sub, coeffC_zC, ite_eq_left rfl] at key
  obtain ⟨w₁, hw₁, hdw₁⟩ := Submodule.mem_map.mp (hgood (n + c₀))
  rw [Nat.add_sub_cancel] at hw₁
  refine ⟨w₁ + coeffC I q K 0 (n + c₀) w', fun s => ?_, ?_⟩
  · have h2 := Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_add_right n c₀))
      (coeffC_mem I q K 0 (n + c₀) w' s)
    change (show Γ(P, K.inter s) from w₁ s) +
        (show Γ(P, K.inter s) from coeffC I q K 0 (n + c₀) w' s) ∈
      Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        q.appLE ⊤ (K.inter s) (le_preimage_top q (K.inter s))).hom (I ^ n)
    exact Ideal.add_mem _ (hw₁ s) h2
  · rw [map_add, hdw₁, key, add_sub_cancel]

end Main

end SolKS

open SolKS in
theorem _root_.AlgebraicGeometry.OModulePresheaf.exists_d_eq_d_of_forall_d_mem_pow_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (K : P.OrderedAffineCover) (n : ℕ) :
    ∃ c : ℕ, ∀ w : (OModulePresheaf.unit q).cochain K 0,
      (∀ s : K.Idx 1, (OModulePresheaf.unit q).d K 0 w s ∈
        Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
          q.appLE ⊤ (K.inter s) (le_preimage_top q (K.inter s))).hom
          (I ^ (n + c))) →
      ∃ w' : (OModulePresheaf.unit q).cochain K 0,
        (∀ s : K.Idx 0, w' s ∈
          Ideal.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
            q.appLE ⊤ (K.inter s) (le_preimage_top q (K.inter s))).hom
            (I ^ n)) ∧
        (OModulePresheaf.unit q).d K 0 w' = (OModulePresheaf.unit q).d K 0 w :=
  SolKS.main I q K n
end
end AlgebraicCurves.Cohomology.Sheaves.Proofs.ReesCechApproximation
end ProofImplementation

attribute [-instance]
  AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul
  AlgebraicGeometry.OModulePresheaf.Leray.biC_module
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
  DoubleComplex.instModuleE₂I
  DoubleComplex.Bounded.modR
  DoubleComplex.instModuleE₂II
  DoubleComplex.instAddCommGroupE₂II
  DoubleComplex.Bounded.abGrp
  DoubleComplex.instAddCommGroupE₂I
  AlgebraicGeometry.ChowDatum.hι_closed
  AlgebraicGeometry.ChowDatumProj.hιN_closed
  AlgebraicGeometry.ChowDatumProj.hp_proper
  AlgebraicGeometry.ChowDatum.hp_isoU
  AlgebraicGeometry.ChowDatum.hp_proper
  AlgebraicGeometry.ProjSpace.algebraAway
  AlgebraicGeometry.ProjSpace.instIsProperProdOverπ
  AlgebraicGeometry.ChowDatumProj.hp_isoU
  AlgebraicGeometry.ProjSpace.isProper_π
  AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
  ProjSpaceCech.GradedModule.H.module
  ProjSpaceCech.GradedModule.H.addCommGroup
  ProjSpaceCech.GradedModule.sec.instAdd
  ProjSpaceCech.GradedModule.sec.instNeg
  ProjSpaceCech.GradedModule.acg
  ProjSpaceCech.GradedModule.Frac.setoid
  ProjSpaceCech.GradedModule.modR
  ProjSpaceCech.GradedModule.sec.instModule
  ProjSpaceCech.GradedModule.sec.instAddCommGroup
  ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance]
  ProjSpaceCech.GradedModule.Presentation.fJ
  ProjSpaceCech.GradedModule.sec.instSMul
  ProjSpaceCech.Twist.H.module
  ProjSpaceCech.Idx.instFintype
  ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq
  ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup
  ProjSpaceCech.Twist.cochain.instModule
attribute [-simp]
  AlgebraicGeometry.OModulePresheaf.prod_obj
  AlgebraicGeometry.OModulePresheaf.restrOpen_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj
  AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj
  AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj
  AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
  DoubleComplex.Bounded.mk.injEq
  DoubleComplex.Bounded.mk.sizeOf_spec
  DoubleComplex.Convergence.mk.injEq
  DoubleComplex.Convergence.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.injEq
  AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
attribute [-simp]
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatumProj.mk.injEq
  AlgebraicGeometry.ChowDatum.mk.injEq
  ProjSpaceCech.GradedModule.mk.injEq
  ProjSpaceCech.GradedModule.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Presentation.mk.injEq
  ProjSpaceCech.GradedModule.Frac.mk.injEq
  ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap
  ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq

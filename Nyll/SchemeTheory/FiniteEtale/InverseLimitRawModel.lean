/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Descent.AffineTransitionOverHomFamily
import Nyll.SchemeTheory.FiniteEtale.RawOverlapFiniteness
import Nyll.SchemeTheory.FiniteEtale.InverseLimitRecoveredModel
import Nyll.SchemeTheory.Gluing.RecoveredPullbackOverlaps
import Nyll.SchemeTheory.Gluing.RecoveredOverlapTransport
import Nyll.SchemeTheory.Gluing.RelativeChartBaseChange

/-!
# An actual stage model from standard recovered affine charts

The finite family of recovered overlap transitions descends by the real
qcqs scheme Hom theorem. The descended local models retain their literal
cartesian overlaps and their covering maps into the original object.
Eventual equality and gluing then supply a finite-etale stage model.
-/

noncomputable section

universe u

open CategoryTheory Limits
open AlgebraicGeometry.Scheme.Cover
open AlgebraicGeometry.AffineTransitionHom

namespace AlgebraicGeometry.FiniteEtale

/-- Standard recovered affine local models produce a finite-etale model
over an original stage of the inverse system. -/
theorem exists_inverse_limit_model_of_standard_charts
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) (𝒰 : (D.obj i).OpenCover.{u}) [Finite 𝒰.I₀]
    [∀ a : 𝒰.I₀, IsAffine (𝒰.X a)]
    (M : ∀ a : 𝒰.I₀, Over (𝒰.X a)) [∀ a : 𝒰.I₀, IsFiniteEtale (M a).hom]
    (X : FiniteEtale c.pt)
    (e : ∀ a : 𝒰.I₀,
      (Over.pullback (pullback.fst (𝒰.f a) (c.π.app i))).obj (M a) ≅
        (Over.pullback (pullback.snd (𝒰.f a) (c.π.app i))).obj
          ((FiniteEtale.forget c.pt).obj X)) :
    ∃ (j : I) (N : FiniteEtale (D.obj j)),
      Nonempty ((FiniteEtale.pullback (c.π.app j)).obj N ≅ X) := by
  let Z : Over c.pt := (FiniteEtale.forget c.pt).obj X
  let A : 𝒰.I₀ → Over (D.obj i) := gluingLocalOver 𝒰 M
  let V : 𝒰.I₀ × 𝒰.I₀ → Over (D.obj i) := gluingOverlapOver 𝒰 M
  let d : ∀ a b : 𝒰.I₀, V (a, b) ⟶ A a := gluingOverlapFirst 𝒰 M
  let y : ∀ a : 𝒰.I₀, (A a).left ⟶ 𝒰.X a := fun a ↦ (M a).hom
  have hy : ∀ a : 𝒰.I₀, y a ≫ 𝒰.f a = (A a).hom := fun _ ↦ rfl
  let ℓ : ∀ a b : 𝒰.I₀, (V (a, b)).left ⟶ 𝒰.X b :=
    fun a b ↦ pullback.snd ((M a).hom ≫ 𝒰.f a) (𝒰.f b)
  have hV : ∀ a b : 𝒰.I₀,
      IsPullback (d a b).left (ℓ a b) (y a ≫ 𝒰.f a) (𝒰.f b) :=
    fun a b ↦ IsPullback.of_hasPullback ((M a).hom ≫ 𝒰.f a) (𝒰.f b)
  let F : Over (D.obj i) ⥤ Over c.pt := Over.pullback (c.π.app i)
  let h : ∀ a : 𝒰.I₀, F.obj (A a) ⟶ Z := fun a ↦
    Over.homMk (recoveredPullbackChartMap (c.π.app i) 𝒰 M Z e a)
      (recoveredPullbackChartMap_structure (c.π.app i) 𝒰 M Z e a)
  have : ∀ a : 𝒰.I₀, IsOpenImmersion (h a).left :=
    fun a ↦ recoveredPullbackChartMap_isOpenImmersion (c.π.app i) 𝒰 M Z e a
  have hcover : ∀ x : Z.left, ∃ (a : 𝒰.I₀) (z : (F.obj (A a)).left),
      (h a).left z = x :=
    (recoveredPullbackChartCover (c.π.app i) 𝒰 M Z e).exists_eq
  let a : ∀ k : 𝒰.I₀ × 𝒰.I₀, F.obj (V k) ⟶ F.obj (V k.swap) :=
    fun k ↦ recoveredPullbackTransition (c.π.app i) 𝒰 M Z e k.1 k.2
  have hPB : ∀ k l : 𝒰.I₀,
      IsPullback (F.map (d k l)).left (a (k, l) ≫ F.map (d l k)).left
        (h k).left (h l).left :=
    recoveredPullbackTransition_isPullback (c.π.app i) 𝒰 M Z e
  let D₀ : Over i ⥤ Over (D.obj i) := Over.post D
  let c₀ : Cone D₀ := (Over.conePost D i).obj c
  have : ∀ {j k : Over i} (f : j ⟶ k), IsAffineHom (D₀.map f).left :=
    fun f ↦ inferInstanceAs (IsAffineHom (D.map f.left))
  have : ∀ j : Over i, CompactSpace (D₀.obj j).left :=
    fun j ↦ inferInstanceAs (CompactSpace (D.obj j.left))
  have : ∀ j : Over i, QuasiSeparatedSpace (D₀.obj j).left :=
    fun j ↦ inferInstanceAs (QuasiSeparatedSpace (D.obj j.left))
  have : ∀ k : 𝒰.I₀ × 𝒰.I₀, QuasiCompact (V k).hom :=
    fun k ↦ rawOverlap_quasiCompact 𝒰 M k.1 k.2
  have : ∀ k : 𝒰.I₀ × 𝒰.I₀, QuasiSeparated (V k).hom :=
    fun k ↦ rawOverlap_quasiSeparated 𝒰 M k.1 k.2
  have : ∀ k : 𝒰.I₀ × 𝒰.I₀, LocallyOfFinitePresentation (V k.swap).hom :=
    fun k ↦ rawOverlap_locallyOfFinitePresentation 𝒰 M k.2 k.1
  obtain ⟨j, b, hb⟩ := exists_over_hom_stage_family D₀ c₀
    (Over.isLimitConePost i hc) V (fun k ↦ V k.swap) a
  let φ : D.obj j.left ⟶ D.obj i := D.map j.hom
  let P : Over (D.obj i) ⥤ Over (D.obj j.left) := Over.pullback φ
  let Q : Over (D.obj j.left) ⥤ Over c.pt := Over.pullback (c.π.app j.left)
  let G : Over (D.obj i) ⥤ Over c.pt := P ⋙ Q
  let E : F ≅ G := overInverseLimitPullbackComparison D₀ c₀ j
  let 𝒰' : (D.obj j.left).OpenCover.{u} := swappedPullbackCover φ 𝒰
  have : Finite 𝒰'.I₀ := inferInstanceAs (Finite 𝒰.I₀)
  let A' : 𝒰.I₀ → Over (D.obj j.left) := fun k ↦ P.obj (A k)
  let V' : 𝒰.I₀ × 𝒰.I₀ → Over (D.obj j.left) := fun k ↦ P.obj (V k)
  let d' : ∀ k l : 𝒰.I₀, V' (k, l) ⟶ A' k := fun k l ↦ P.map (d k l)
  let y' : ∀ k : 𝒰.I₀, (A' k).left ⟶ 𝒰'.X k :=
    relativeBaseChangedChartStructure 𝒰 A y hy φ
  have hy' : ∀ k : 𝒰.I₀, y' k ≫ 𝒰'.f k = (A' k).hom :=
    relativeBaseChangedChartStructure_base 𝒰 A y hy φ
  let ℓ' : ∀ k l : 𝒰.I₀, (V' (k, l)).left ⟶ 𝒰'.X l :=
    relativeBaseChangedOverlapSecond 𝒰 A V d y hy ℓ hV φ
  have hV' : ∀ k l : 𝒰.I₀,
      IsPullback (d' k l).left (ℓ' k l) (y' k ≫ 𝒰'.f k) (𝒰'.f l) :=
    relativeBaseChangedOverlap_isPullback 𝒰 A V d y hy ℓ hV φ
  let t' : ∀ k l : 𝒰.I₀, V' (k, l) ⟶ V' (l, k) := fun k l ↦ b (k, l)
  have ht' : ∀ k l : 𝒰.I₀, (t' k l).left ≫ (d' l k).left ≫ y' l = ℓ' k l :=
    relativeBaseChangedTransition_structure 𝒰 A V d y hy ℓ hV φ t'
  let h' : ∀ k : 𝒰.I₀, Q.obj (A' k) ⟶ Z := fun k ↦ E.inv.app (A k) ≫ h k
  have : ∀ k : 𝒰'.I₀, IsOpenImmersion (h' k).left :=
    fun k ↦ recoveredChartTransport_isOpenImmersion E (h (show 𝒰.I₀ from k))
  have hcover' : ∀ x : Z.left, ∃ (k : 𝒰.I₀) (z : (Q.obj (A' k)).left),
      (h' k).left z = x := recoveredChartTransport_covers E A Z h hcover
  have hoverlap' : ∀ k l : 𝒰.I₀,
      IsPullback (Q.map (d' k l)).left (Q.map (t' k l ≫ d' l k)).left
        (h' k).left (h' l).left := by
    intro k l
    have H := recoveredOverlapTransport_isPullback E (d k l) (d l k) (h k) (h l)
      (a (k, l)) (Q.map (t' k l)) (hb (k, l)) (hPB k l)
    have hmap : Q.map (t' k l ≫ d' l k) = Q.map (t' k l) ≫ G.map (d l k) :=
      Q.map_comp (t' k l) (d' l k)
    rw [hmap]
    exact H
  have : ∀ k : 𝒰.I₀, IsFiniteEtale (y k) :=
    fun k ↦ inferInstanceAs (IsFiniteEtale (M k).hom)
  have : ∀ k : 𝒰'.I₀, IsFiniteEtale (y' k) :=
    fun k ↦ relativeBaseChangedChartStructure_finiteEtale 𝒰 A y hy φ
      (show 𝒰.I₀ from k)
  have : ∀ k : 𝒰'.I₀, CompactSpace (𝒰'.X k) :=
    fun k ↦ relativeBaseChangedChart_compactSpace 𝒰 φ (show 𝒰.I₀ from k)
  obtain ⟨j', _, N, hN⟩ := exists_inverse_limit_model_of_recovered_charts
    D c hc j.left 𝒰' A' V' d' y' hy' ℓ' hV' t' ht' X h' hcover' hoverlap'
  exact ⟨j', N, hN⟩

end AlgebraicGeometry.FiniteEtale

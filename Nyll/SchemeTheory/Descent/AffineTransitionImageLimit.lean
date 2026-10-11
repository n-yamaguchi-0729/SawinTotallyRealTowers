/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Descent.AffineTransitionImageDiagram
import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Recovering a closed subscheme from its stage images

Sections on affine preimages descend to an actual ambient stage. This detects
the kernel of a quasi-compact morphism from its stage kernels and supplies the
universal property of the corresponding scheme-theoretic image limit.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AffineTransitionImage

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i k} (f : i ⟶ k), IsAffineHom (D.map f)]

include hc in
private theorem exists_affine_preimage_section (i : I) (V : (D.obj i).Opens)
    (hV : IsAffineOpen V) (s : Γ(c.pt, c.π.app i ⁻¹ᵁ V)) :
    ∃ (k : I) (f : k ⟶ i) (t : Γ(D.obj k, D.map f ⁻¹ᵁ V)),
      (c.π.app k).appLE (D.map f ⁻¹ᵁ V) (c.π.app i ⁻¹ᵁ V)
        (by rw [← Scheme.Hom.comp_preimage, c.w f]) t = s := by
  have (k : Over i) : IsAffine ((opensDiagram D i V).obj k) :=
    hV.preimage (D.map k.hom)
  obtain ⟨k, t, ht⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit
    (opensDiagram D i V) (opensCone D c i V) (isLimitOpensCone D c hc i V)
    ((c.π.app i ⁻¹ᵁ V).topIso.inv s)
  let t' : Γ((D.map k.hom ⁻¹ᵁ V).toScheme, ⊤) := t
  have ht' : ((c.π.app k.left).resLE (D.map k.hom ⁻¹ᵁ V) (c.π.app i ⁻¹ᵁ V)
      (by rw [← Scheme.Hom.comp_preimage, c.w k.hom])).appTop t' =
        (c.π.app i ⁻¹ᵁ V).topIso.inv s := ht
  refine ⟨k.left, k.hom, (D.map k.hom ⁻¹ᵁ V).topIso.hom t', ?_⟩
  apply (c.π.app i ⁻¹ᵁ V).topIso.commRingCatIsoToRingEquiv.symm.injective
  change (c.π.app i ⁻¹ᵁ V).topIso.inv
      ((c.π.app k.left).appLE _ _ _ ((D.map k.hom ⁻¹ᵁ V).topIso.hom t')) =
    (c.π.app i ⁻¹ᵁ V).topIso.inv s
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top] at ht'
  exact ht'

private lemma appLE_eq_zero_of_mem_ker {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.affineOpens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U)
    (s : Γ(Y, U)) (hs : s ∈ f.ker.ideal U) : f.appLE U V h s = 0 := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply,
    RingHom.mem_ker.mp (f.ideal_ker_le U hs), map_zero]

private lemma mem_ker_of_appLE_eq_zero {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] (U : Y.affineOpens) (V : X.Opens) (h : V = f ⁻¹ᵁ U)
    (s : Γ(Y, U)) (hs : f.appLE U V h.le s = 0) : s ∈ f.ker.ideal U := by
  subst V
  rw [Scheme.Hom.appLE_eq_app] at hs
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
  exact hs

private lemma app_eq_zero_of_stage_kernel_le {X Y Z T : Scheme.{u}}
    (p : X ⟶ Y) [QuasiCompact p] (j : Z ⟶ X) [QuasiCompact j] (g : T ⟶ X)
    (U : Y.affineOpens) (V : X.Opens) (hpre : V = p ⁻¹ᵁ U)
    (s : Γ(X, V)) (t : Γ(Y, U)) (ht : p.appLE U V hpre.le t = s)
    (hjs : j.app V s = 0) (h : (j ≫ p).ker ≤ (g ≫ p).ker) :
    g.app V s = 0 := by
  have htj : (j ≫ p).appLE U (j ⁻¹ᵁ V)
      (by rw [Scheme.Hom.comp_preimage, ← hpre]) t = 0 := by
    rw [← Scheme.Hom.appLE_comp_appLE j p U V (j ⁻¹ᵁ V) hpre.le le_rfl,
      CommRingCat.comp_apply, ht, Scheme.Hom.appLE_eq_app]
    exact hjs
  have htk : t ∈ (j ≫ p).ker.ideal U :=
    mem_ker_of_appLE_eq_zero (j ≫ p) U (j ⁻¹ᵁ V)
      (by rw [Scheme.Hom.comp_preimage, ← hpre]) t htj
  have htkg : t ∈ (g ≫ p).ker.ideal U := h U htk
  have hgt := appLE_eq_zero_of_mem_ker (g ≫ p) U (g ⁻¹ᵁ V)
    (by rw [Scheme.Hom.comp_preimage, ← hpre]) t htkg
  rw [← Scheme.Hom.appLE_comp_appLE g p U V (g ⁻¹ᵁ V) hpre.le le_rfl,
    CommRingCat.comp_apply, ht, Scheme.Hom.appLE_eq_app] at hgt
  exact hgt

include hc in
/-- Kernels into an affine-transition limit are detected by the actual kernels
at the ambient stages. The source of the second morphism need not be compact. -/
theorem ker_le_of_stage_ker_le [∀ i, QuasiSeparatedSpace (D.obj i)]
    {Z T : Scheme.{u}} (j : Z ⟶ c.pt) [QuasiCompact j] (g : T ⟶ c.pt)
    (h : ∀ i, (j ≫ c.π.app i).ker ≤ (g ≫ c.π.app i).ker) :
    j.ker ≤ g.ker := by
  have (i : I) : IsAffineHom (c.π.app i) := isAffineHom_π_app D c hc i
  apply Scheme.IdealSheafData.le_ofIdeals_iff.mpr
  intro U s hs
  rcases U with ⟨U, hU⟩
  obtain ⟨i, V, hV, rfl⟩ := exists_isAffineOpen_preimage_eq D c hc U hU
  obtain ⟨k, f, t, ht⟩ := exists_affine_preimage_section D c hc i V hV s
  have hpre : c.π.app i ⁻¹ᵁ V = c.π.app k ⁻¹ᵁ (D.map f ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, c.w f]
  have hStageAffine : IsAffineOpen (D.map f ⁻¹ᵁ V) := hV.preimage (D.map f)
  have hjs : j.app (c.π.app i ⁻¹ᵁ V) s = 0 :=
    RingHom.mem_ker.mp (j.ideal_ker_le _ hs)
  exact RingHom.mem_ker.mpr
    (app_eq_zero_of_stage_kernel_le (c.π.app k) j g
      ⟨D.map f ⁻¹ᵁ V, hStageAffine⟩ (c.π.app i ⁻¹ᵁ V) hpre s t ht hjs (h k))

/-- A closed subscheme of an affine-transition limit is the limit of its
actual scheme-theoretic images at the ambient stages. -/
def coneIsLimit [∀ i, QuasiSeparatedSpace (D.obj i)]
    {Z : Scheme.{u}} (j : Z ⟶ c.pt) [IsClosedImmersion j] :
    IsLimit (cone D c j) := by
  let ambient (s : Cone (diagram D c j)) : Cone D :=
    { pt := s.pt, π := s.π ≫ inclusions D c j }
  let a (s : Cone (diagram D c j)) : s.pt ⟶ c.pt := hc.lift (ambient s)
  have ha (s : Cone (diagram D c j)) (i : I) :
      a s ≫ c.π.app i = s.π.app i ≫ inclusion D c j i :=
    hc.fac (ambient s) i
  have hker (s : Cone (diagram D c j)) : j.ker ≤ (a s).ker := by
    apply ker_le_of_stage_ker_le D c hc j (a s)
    intro i
    rw [ha]
    exact (Scheme.IdealSheafData.ker_subschemeι (j ≫ c.π.app i).ker).symm.le.trans
      (Scheme.Hom.le_ker_comp (s.π.app i) (inclusion D c j i))
  refine
    { lift := fun s => IsClosedImmersion.lift j (a s) (hker s)
      fac := ?_
      uniq := ?_ }
  · intro s i
    apply (cancel_mono (inclusion D c j i)).mp
    rw [Category.assoc, cone_projection_inclusion, ← Category.assoc,
      IsClosedImmersion.lift_fac, ha]
  · intro s m hm
    apply (cancel_mono j).mp
    rw [IsClosedImmersion.lift_fac]
    apply hc.hom_ext
    intro i
    rw [ha, Category.assoc, ← cone_projection_inclusion D c j i,
      ← Category.assoc, hm i]

end AlgebraicGeometry.AffineTransitionImage

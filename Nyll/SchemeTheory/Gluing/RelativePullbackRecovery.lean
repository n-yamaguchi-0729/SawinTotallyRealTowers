/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Gluing.RelativePullback
import Nyll.SchemeTheory.Gluing.CoefficientCover
import Nyll.SchemeTheory.Gluing.OverCover

/-!
# Recovering the actual glued model after a later base change

The native pullback of the glued model and the original scheme have the
same recovered charts and actual overlaps. Common-cover recovery therefore
produces an isomorphism over the limit base, retaining the actual structural
morphism rather than only an isomorphism of underlying schemes.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Cover

variable {S T L : Scheme.{u}} (𝒰 : S.OpenCover)
variable (A : 𝒰.I₀ → Over S) (V : 𝒰.I₀ × 𝒰.I₀ → Over S)
variable (d : ∀ i j : 𝒰.I₀, V (i, j) ⟶ A i)
variable (y : ∀ i : 𝒰.I₀, (A i).left ⟶ 𝒰.X i)
variable (ℓ : ∀ i j : 𝒰.I₀, (V (i, j)).left ⟶ 𝒰.X j)
variable (hV : ∀ i j : 𝒰.I₀, IsPullback (d i j).left (ℓ i j) (y i ≫ 𝒰.f i) (𝒰.f j))
variable (t : ∀ i j : 𝒰.I₀, V (i, j) ⟶ V (j, i))
variable (ht : ∀ i j : 𝒰.I₀, (t i j).left ≫ (d j i).left ≫ y j = ℓ i j)
variable (ψ : T ⟶ S)
variable (hdiag : ∀ i : 𝒰.I₀,
  (Over.pullback ψ).map (t i i) = 𝟙 ((Over.pullback ψ).obj (V (i, i))))
variable (hcycle : ∀ i j k : 𝒰.I₀,
  (Over.pullback ψ).map
      (relativeTripleTransition 𝒰 A V d y ℓ hV t ht i j k ≫
        relativeTripleTransition 𝒰 A V d y ℓ hV t ht j k i ≫
          relativeTripleTransition 𝒰 A V d y ℓ hV t ht k i j) =
    𝟙 ((Over.pullback ψ).obj (relativeTriple 𝒰 A V d i j k)))

/-- The native pullback of the glued model is isomorphic over the new base
to the scheme covered by the actual recovered local models. -/
theorem exists_relativePullbackGlue_recovery_iso
    (q : (relativeGlueDataOfPullbackEquations 𝒰 A V d y ℓ hV t ht ψ hdiag hcycle).glued ⟶ T)
    (hq : ∀ i : 𝒰.I₀,
      (relativeGlueDataOfPullbackEquations 𝒰 A V d y ℓ hV t ht ψ hdiag hcycle).ι i ≫ q =
        ((Over.pullback ψ).obj (A i)).hom)
    (ρ : L ⟶ T) (χ : L ⟶ S) (hχ : χ = ρ ≫ ψ)
    (Z : Over L)
    (h : ∀ i : 𝒰.I₀, (Over.pullback χ).obj (A i) ⟶ Z)
    [∀ i : 𝒰.I₀, IsOpenImmersion (h i).left]
    (hcover : ∀ z : Z.left, ∃ (i : 𝒰.I₀) (a : ((Over.pullback χ).obj (A i)).left),
      (h i).left a = z)
    (hoverlap : ∀ i j : 𝒰.I₀,
      IsPullback ((Over.pullback χ).map (d i j)).left
        ((Over.pullback χ).map (t i j ≫ d j i)).left (h i).left (h j).left) :
    Nonempty ((Over.pullback ρ).obj (Over.mk q) ≅ Z) := by
  let G := relativeGlueDataOfPullbackEquations 𝒰 A V d y ℓ hV t ht ψ hdiag hcycle
  let F := Over.pullback ψ
  let R := Over.pullback ρ
  let N : Over T := Over.mk q
  let e : Over.pullback χ ≅ F ⋙ R :=
    eqToIso (congrArg (fun f : L ⟶ S ↦ Over.pullback f) hχ) ≪≫ Over.pullbackComp ρ ψ
  let M (i : 𝒰.I₀) : Over L := R.obj (F.obj (A i))
  let H (i : 𝒰.I₀) : M i ⟶ Z := e.inv.app (A i) ≫ h i
  let eA (i : 𝒰.I₀) : ((Over.pullback χ).obj (A i)).left ≅ (M i).left :=
    (Over.forget L).mapIso (e.app (A i))
  let eV (i j : 𝒰.I₀) : ((Over.pullback χ).obj (V (i, j))).left ≅
      (R.obj (F.obj (V (i, j)))).left :=
    (Over.forget L).mapIso (e.app (V (i, j)))
  let 𝒜 : Z.left.OpenCover :=
    { I₀ := 𝒰.I₀
      X := fun i ↦ ((Over.pullback χ).obj (A i)).left
      f := fun i ↦ (h i).left
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨hcover, inferInstance⟩ }
  let 𝒜' : Z.left.OpenCover :=
    Scheme.Cover.copy 𝒜 𝒰.I₀ (fun i ↦ (M i).left) (fun i ↦ (H i).left)
      (Equiv.refl _) (fun i ↦ (eA i).symm) (fun _ ↦ rfl)
  have : ∀ i : 𝒰.I₀, IsOpenImmersion (H i).left := fun i ↦ 𝒜'.map_prop i
  have hH (i j : 𝒰.I₀) :
      IsPullback ((R.map (F.map (d i j))).left)
        ((R.map (F.map (t i j ≫ d j i))).left) (H i).left (H j).left := by
    refine (hoverlap i j).of_iso (eV i j) (eA i) (eA j) (Iso.refl Z.left) ?_ ?_ ?_ ?_
    · exact congrArg (fun m ↦ m.left) (e.hom.naturality (d i j))
    · exact congrArg (fun m ↦ m.left) (e.hom.naturality (t i j ≫ d j i))
    · change (h i).left ≫ 𝟙 Z.left = (eA i).hom ≫ ((eA i).inv ≫ (h i).left)
      rw [Category.comp_id, Iso.hom_inv_id_assoc]
    · change (h j).left ≫ 𝟙 Z.left = (eA j).hom ≫ ((eA j).inv ≫ (h j).left)
      rw [Category.comp_id, Iso.hom_inv_id_assoc]
  let m (i : 𝒰.I₀) : F.obj (A i) ⟶ N := Over.homMk (G.ι i) (hq i)
  have : ∀ i : 𝒰.I₀, IsOpenImmersion (m i).left := fun i ↦ G.ι_isOpenImmersion i
  let 𝒬 := overCoefficientPullbackCover ρ N (fun i ↦ F.obj (A i)) m G.ι_jointly_surjective
  have : ∀ i : 𝒰.I₀, IsOpenImmersion (R.map (m i)).left := fun i ↦ 𝒬.map_prop i
  have hm (i j : 𝒰.I₀) : IsPullback (F.map (d i j)).left
      (F.map (t i j ≫ d j i)).left (m i).left (m j).left := by
    have Hmap : (F.map (t i j ≫ d j i)).left = G.t i j ≫ G.f j i :=
      congrArg (fun a ↦ a.left) (F.map_comp (t i j) (d j i))
    rw [Hmap]
    exact IsPullback.of_isLimit (G.vPullbackConeIsLimit i j)
  have hm' (i j : 𝒰.I₀) : IsPullback (R.map (F.map (d i j))).left
      (R.map (F.map (t i j ≫ d j i))).left (R.map (m i)).left (R.map (m j)).left :=
    overCoefficientPullback_map_isPullback ρ (F.map (d i j))
      (F.map (t i j ≫ d j i)) (m i) (m j) (hm i j)
  obtain ⟨E, _⟩ := exists_over_iso_of_common_open_cover (R.obj N) Z M
    (fun ij ↦ (R.obj (F.obj (V ij))).left)
    (fun i j ↦ (R.map (F.map (d i j))).left)
    (fun i j ↦ (R.map (F.map (t i j ≫ d j i))).left)
    (fun i ↦ R.map (m i)) H 𝒬.exists_eq 𝒜'.exists_eq hm' hH
  exact ⟨E⟩

end AlgebraicGeometry.Scheme.Cover

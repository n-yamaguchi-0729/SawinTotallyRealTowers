/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
public import Nyll.ProCGroups.ProC.OpenNormalSubgroups.ProCGroup
public import Nyll.ProCGroups.Profinite.OpenSubgroups

/-!
# Continuous extensions from finite quotients

Unique extension to finite in-class groups in the native universe supplies unique extension
to pro-C targets in any universe. Common in-class refinements enforce compatibility; no
closure property of the finite-group class is required.
-/

@[expose] public section

open CategoryTheory

namespace ProCGroups.ProC

universe u v w

/-- A finite discrete group in the class has an in-class open-normal basis. Only invariance
under multiplicative equivalence is needed, since the trivial subgroup is a basis. -/
theorem HasOpenNormalBasisInClass.of_finite_discrete_mem
    {C : FiniteGroupClass.{u}} {H : Type u} [Group H] [TopologicalSpace H]
    [DiscreteTopology H] (hH : C H) : HasOpenNormalBasisInClass C H := by
  intro W _ h1W
  let B : OpenNormalSubgroup H :=
    { toOpenSubgroup :=
        { toSubgroup := ⊥
          isOpen' := isOpen_discrete _ } }
  refine ⟨B, ?_, C.mem_of_mulEquiv QuotientGroup.quotientBot.symm hH⟩
  intro x hx
  change x = 1 at hx
  exact hx.symm ▸ h1W

/-- A finite extension problem with unique solutions in the native universe has a unique
continuous solution in every pro-C target universe. The two maps on `X` specify the values
that the extension must preserve. -/
theorem existsUnique_continuousExtension_of_finiteQuotients
    {C : FiniteGroupClass.{u}}
    {X : Type w} {F : Type u} [Group F] [TopologicalSpace F]
    (ι : X → F)
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : HasOpenNormalBasisInClassAcrossUniverses C G) (φ : X → G)
    (hfinite : ∀ {H : Type u} [Group H] [TopologicalSpace H]
      [DiscreteTopology H] [Finite H], C H → ∀ q : G →ₜ* H,
        ∃! f : F →ₜ* H, ∀ x, f (ι x) = q (φ x)) :
    ∃! f : F →ₜ* G, ∀ x, f (ι x) = φ x := by
  classical
  have hfiniteAcross {H : Type v} [Group H] [TopologicalSpace H]
      [DiscreteTopology H] (hH : C.MemAcrossUniverses H) (q : G →ₜ* H) :
      ∃! f : F →ₜ* H, ∀ x, f (ι x) = q (φ x) := by
    obtain ⟨H₀, hH₀, ⟨e⟩⟩ := hH
    let : TopologicalSpace H₀ := ⊥
    let : DiscreteTopology H₀ := ⟨rfl⟩
    let : Finite H₀ := C.finite hH₀
    let e' : H₀ ≃ₜ* H :=
      { e with
        continuous_toFun := continuous_of_discreteTopology
        continuous_invFun := continuous_of_discreteTopology }
    let e₀ : H →ₜ* H₀ := ContinuousMonoidHom.toContinuousMonoidHom e'.symm
    let e₁ : H₀ →ₜ* H := ContinuousMonoidHom.toContinuousMonoidHom e'
    obtain ⟨f₀, hf₀, huniq⟩ := hfinite hH₀ (e₀.comp q)
    refine ⟨e₁.comp f₀, ?_, ?_⟩
    · intro x
      change e' (f₀ (ι x)) = q (φ x)
      rw [hf₀ x]
      exact e'.apply_symm_apply _
    · intro g hg
      have hg₀ : e₀.comp g = f₀ := huniq _ (fun x => congrArg e'.symm (hg x))
      ext y
      have hy := DFunLike.congr_fun hg₀ y
      change e'.symm (g y) = f₀ y at hy
      change g y = e' (f₀ y)
      exact e'.symm.injective (by rw [e'.symm_apply_apply]; exact hy)
  let P : ProfiniteGrp.{v} := ProfiniteGrp.of G
  let D := ProfiniteGrp.diagram P
  let π (U : OpenNormalSubgroup G) : G →ₜ* D.obj U :=
    ((ProfiniteGrp.limitCone D).π.app U).hom.comp (ProfiniteGrp.toLimit P).hom
  let q {U V : OpenNormalSubgroup G} (h : U ≤ V) : D.obj U →ₜ* D.obj V :=
    (D.map (homOfLE h)).hom
  have hrefine (U : OpenNormalSubgroup G) :
      ∃ V : OpenNormalSubgroup G, V ≤ U ∧ C.MemAcrossUniverses (D.obj V) := by
    obtain ⟨V, hVU, hV⟩ := hG (U : Set G) U.toOpenSubgroup.isOpen' U.one_mem
    exact ⟨V, hVU, hV⟩
  let V (U : OpenNormalSubgroup G) := Classical.choose (hrefine U)
  have hVU (U : OpenNormalSubgroup G) : V U ≤ U :=
    (Classical.choose_spec (hrefine U)).1
  have hVC (U : OpenNormalSubgroup G) : C.MemAcrossUniverses (D.obj (V U)) :=
    (Classical.choose_spec (hrefine U)).2
  have hstage (U : OpenNormalSubgroup G) (hU : C.MemAcrossUniverses (D.obj U)) :
      ∃! f : F →ₜ* D.obj U, ∀ x, f (ι x) = π U (φ x) := by
    let : Finite (D.obj U) := openNormalSubgroup_finiteQuotient (G := G) U
    let : DiscreteTopology (D.obj U) := Finite.instDiscreteTopology
    exact hfiniteAcross hU (π U)
  let fV (U : OpenNormalSubgroup G) : F →ₜ* D.obj (V U) :=
    Classical.choose (ExistsUnique.exists (hstage (V U) (hVC U)))
  have hfV (U : OpenNormalSubgroup G) (x : X) : fV U (ι x) = π (V U) (φ x) :=
    Classical.choose_spec (ExistsUnique.exists (hstage (V U) (hVC U))) x
  let f (U : OpenNormalSubgroup G) : F →ₜ* D.obj U := (q (hVU U)).comp (fV U)
  have hf (U : OpenNormalSubgroup G) (x : X) : f U (ι x) = π U (φ x) := by
    change q (hVU U) (fV U (ι x)) = π U (φ x)
    rw [hfV U x]
    rfl
  have hcompat {U T : OpenNormalSubgroup G} (i : U ⟶ T) :
      (D.map i).hom.comp (f U) = f T := by
    obtain ⟨W, hW, hWC⟩ := hrefine (V U ⊓ V T)
    have hWU : W ≤ V U := hW.trans inf_le_left
    have hWT : W ≤ V T := hW.trans inf_le_right
    obtain ⟨fW, hfW, _⟩ := hstage W hWC
    have hU : (q hWU).comp fW = fV U :=
      (hstage (V U) (hVC U)).unique
        (fun x => by
          change q hWU (fW (ι x)) = π (V U) (φ x)
          rw [hfW x]
          rfl)
        (hfV U)
    have hT : (q hWT).comp fW = fV T :=
      (hstage (V T) (hVC T)).unique
        (fun x => by
          change q hWT (fW (ι x)) = π (V T) (φ x)
          rw [hfW x]
          rfl)
        (hfV T)
    ext y
    change D.map i (q (hVU U) (fV U y)) = q (hVU T) (fV T y)
    rw [← DFunLike.congr_fun hU y, ← DFunLike.congr_fun hT y]
    change (D.map i).hom (q (hVU U) (q hWU (fW y))) =
      q (hVU T) (q hWT (fW y))
    induction fW y using Quotient.inductionOn with
    | h z => rfl
  let fL : F →ₜ* ProfiniteGrp.limit D :=
    { toFun := fun y => ⟨fun U => f U y, by
        intro U T i
        exact DFunLike.congr_fun (hcompat i) y⟩
      map_one' := Subtype.ext (funext fun U => (f U).map_one)
      map_mul' := fun x y => Subtype.ext (funext fun U => (f U).map_mul x y)
      continuous_toFun := continuous_induced_rng.mpr (continuous_pi fun U =>
        (f U).continuous_toFun) }
  let e := ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor P
  let lift : F →ₜ* G := (ContinuousMonoidHom.toContinuousMonoidHom e.symm).comp fL
  have hlift (x : X) : lift (ι x) = φ x := by
    apply e.injective
    change e (e.symm (fL (ι x))) = e (φ x)
    rw [e.apply_symm_apply]
    apply ProfiniteGrp.limit_ext
    intro U
    exact hf U x
  refine ⟨lift, hlift, ?_⟩
  intro g hg
  ext y
  apply e.injective
  apply ProfiniteGrp.limit_ext
  intro U
  have heq : (π (V U)).comp g = (π (V U)).comp lift :=
    (hstage (V U) (hVC U)).unique
      (fun x => congrArg (π (V U)) (hg x))
      (fun x => congrArg (π (V U)) (hlift x))
  have hy := congrArg (q (hVU U)) (DFunLike.congr_fun heq y)
  exact hy

end ProCGroups.ProC

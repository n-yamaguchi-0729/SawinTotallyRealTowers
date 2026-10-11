/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.DifferentialModule.Identity

/-!
# Fox differential: completed — differential module — map — comap

The principal declarations in this module are:

- `completedGroupAlgebraComapIndex`
  The index map that sends a target finite quotient to its pullback finite quotient on the source.
- `completedGroupAlgebraComapQuotientMap`
  The quotient map from the pulled-back source quotient to the target quotient induced by the
  original homomorphism.
- `completedGroupAlgebraComapIndex_subgroup`
  The subgroup underlying the comap index is the subgroup-theoretic comap.
- `completedGroupAlgebraComapQuotientMap_mk`
  The pullback quotient map sends the class of a source element to the class of its image in the
  target quotient in the Fox differential construction.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups
open ProCGroups.ProC

universe u v

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/--
The index map that sends a target finite quotient to its pullback finite quotient on the source.
-/
def completedGroupAlgebraComapIndex
    (ψ : ContinuousMonoidHom G H) (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex H) :
    _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G := by
  let V : OpenNormalSubgroup H := (OrderDual.ofDual U).1
  let W : OpenNormalSubgroup G := OpenNormalSubgroup.comap ψ.toMonoidHom ψ.continuous_toFun V
  refine OrderDual.toDual ⟨W, ?_⟩
  let q : G →* H ⧸ (V : Subgroup H) :=
    (QuotientGroup.mk' (V : Subgroup H)).comp ψ.toMonoidHom
  let f : G ⧸ (W : Subgroup G) → H ⧸ (V : Subgroup H) :=
    QuotientGroup.map _ _ ψ.toMonoidHom (by
      intro g hg
      simpa [W] using hg)
  have hf : Function.Injective f := by
    intro x y hxy
    rcases QuotientGroup.mk'_surjective (W : Subgroup G) x with ⟨a, rfl⟩
    rcases QuotientGroup.mk'_surjective (W : Subgroup G) y with ⟨b, rfl⟩
    apply QuotientGroup.eq.2
    change ψ (a⁻¹ * b) ∈ (V : Subgroup H)
    have hv : (ψ a)⁻¹ * ψ b ∈ (V : Subgroup H) := QuotientGroup.eq.1 hxy
    simpa using hv
  exact
    letI : Finite (H ⧸ (V : Subgroup H)) := (OrderDual.ofDual U).2
    Finite.of_injective f hf

omit [IsTopologicalGroup G] in
/-- The subgroup underlying the comap index is the subgroup-theoretic comap. -/
@[simp]
theorem completedGroupAlgebraComapIndex_subgroup
    (ψ : ContinuousMonoidHom G H) (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex H) :
    (((OrderDual.ofDual (completedGroupAlgebraComapIndex (G := G) (H := H) ψ U)).1 :
        OpenNormalSubgroup G) : Subgroup G) =
      Subgroup.comap ψ.toMonoidHom
        (((OrderDual.ofDual U).1 : OpenNormalSubgroup H) : Subgroup H) := by
  rfl

/--
The quotient map from the pulled-back source quotient to the target quotient induced by the
original homomorphism.
-/
def completedGroupAlgebraComapQuotientMap
    (ψ : ContinuousMonoidHom G H) (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex H) :
    _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G
        (completedGroupAlgebraComapIndex (G := G) (H := H) ψ U) →*
      _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient H U :=
  QuotientGroup.map _ _ ψ.toMonoidHom (by
    intro g hg
    simpa [completedGroupAlgebraComapIndex] using hg)

/--
The pullback quotient map sends the class of a source element to the class of its image in the
target quotient in the Fox differential construction.
-/
@[simp]
theorem completedGroupAlgebraComapQuotientMap_mk
    (ψ : ContinuousMonoidHom G H) (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex
        H) (g : G) :
    completedGroupAlgebraComapQuotientMap (G := G) (H := H) ψ U
        (QuotientGroup.mk' _ g) =
      QuotientGroup.mk' (((OrderDual.ofDual U).1 : OpenNormalSubgroup H) : Subgroup H) (ψ g) := by
  rfl


/--
If \(\psi : G \to H\) is surjective, the induced map from the pulled-back finite quotient \(G /
\psi^{-1}(U)\) to \(H / U\) is surjective. This is the finite-quotient input used later to lift
coefficients in the completed free-derivative construction.
-/
theorem completedGroupAlgebraComapQuotientMap_surjective
    (ψ : ContinuousMonoidHom G H) (hψ : Function.Surjective ψ)
    (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex H) :
    Function.Surjective
      (completedGroupAlgebraComapQuotientMap (G := G) (H := H) ψ U) := by
  intro q
  rcases QuotientGroup.mk'_surjective
      ((((OrderDual.ofDual U).1 : OpenNormalSubgroup H) : Subgroup H)) q with
    ⟨h, rfl⟩
  rcases hψ h with ⟨g, rfl⟩
  refine ⟨QuotientGroup.mk'
      ((((OrderDual.ofDual
        (completedGroupAlgebraComapIndex (G := G) (H := H) ψ U)).1 :
          OpenNormalSubgroup G) : Subgroup G)) g, ?_⟩
  rw [completedGroupAlgebraComapQuotientMap_mk]

omit [IsTopologicalGroup G] in
/-- Comap of all-finite completed-group-algebra indices is monotone. -/
theorem completedGroupAlgebraComapIndex_mono
    (ψ : ContinuousMonoidHom G H) {U V : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex
        H} (hUV : U ≤ V) :
    completedGroupAlgebraComapIndex (G := G) (H := H) ψ U ≤
      completedGroupAlgebraComapIndex (G := G) (H := H) ψ V := by
  change
    Subgroup.comap ψ.toMonoidHom
        (((OrderDual.ofDual V).1 : OpenNormalSubgroup H) : Subgroup H) ≤
      Subgroup.comap ψ.toMonoidHom
        (((OrderDual.ofDual U).1 : OpenNormalSubgroup H) : Subgroup H)
  exact Subgroup.comap_mono hUV

/-- The comap quotient maps are compatible with refinement of finite quotients. -/
@[simp]
theorem completedGroupAlgebraComapQuotientMap_compatible
    (ψ : ContinuousMonoidHom G H) {U V : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex
        H} (hUV : U ≤ V) :
    (OpenNormalSubgroupInClass.map
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := H)
        (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV).comp
        (completedGroupAlgebraComapQuotientMap (G := G) (H := H) ψ V) =
      (completedGroupAlgebraComapQuotientMap (G := G) (H := H) ψ U).comp
        (OpenNormalSubgroupInClass.map
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
          (U := OrderDual.ofDual
            (completedGroupAlgebraComapIndex (G := G) (H := H) ψ U))
          (V := OrderDual.ofDual
            (completedGroupAlgebraComapIndex (G := G) (H := H) ψ V))
          (completedGroupAlgebraComapIndex_mono (G := G) (H := H) ψ hUV)) := by
  ext q
  rcases QuotientGroup.mk'_surjective
      ((((OrderDual.ofDual
        (completedGroupAlgebraComapIndex (G := G) (H := H) ψ V)).1 :
          OpenNormalSubgroup G) : Subgroup G)) q with ⟨g, rfl⟩
  rfl

end

end FoxDifferential

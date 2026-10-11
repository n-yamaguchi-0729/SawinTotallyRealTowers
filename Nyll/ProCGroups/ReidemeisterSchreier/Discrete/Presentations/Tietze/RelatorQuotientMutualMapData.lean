/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Relators.Congruence
import Nyll.ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Relators.Operations

/-!
# Reidemeister Schreier / Discrete / Presentations / Tietze / Relator Quotient Mutual Map Data

This module packages mutually inverse maps between relator quotients.  It
provides reflexive, symmetric, and transitive composition together with a
one-sided constructor when the inverse data can be derived.
-/

universe u v w

namespace ReidemeisterSchreier.Discrete.Presentations

variable {G H K : Type*} [Group G] [Group H] [Group K]

/--
Mutual homomorphisms respecting relators induce an isomorphism between the corresponding relator
quotients.
-/
noncomputable def quotientEquivOfRelatorsByMutualMaps
    (R : Set G) (S : Set H)
    (f : G →* H) (g : H →* G)
    (hR : ∀ r ∈ R, f r ∈ Subgroup.normalClosure S)
    (hS : ∀ s ∈ S, g s ∈ Subgroup.normalClosure R)
    (hgf : ∀ x : G, g (f x) * x⁻¹ ∈ Subgroup.normalClosure R)
    (hfg : ∀ y : H, f (g y) * y⁻¹ ∈ Subgroup.normalClosure S) :
    G ⧸ Subgroup.normalClosure R ≃* H ⧸ Subgroup.normalClosure S := by
  let NR : Subgroup G := Subgroup.normalClosure R
  let NS : Subgroup H := Subgroup.normalClosure S
  have hfNR : NR ≤ Subgroup.comap f NS := by
    exact Subgroup.normalClosure_le_normal hR
  have hgNS : NS ≤ Subgroup.comap g NR := by
    exact Subgroup.normalClosure_le_normal hS
  let F : G ⧸ NR →* H ⧸ NS :=
    QuotientGroup.lift NR ((QuotientGroup.mk' NS).comp f) (by
      intro x hx
      rw [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff (N := NS) (f x)).2 (hfNR hx))
  let K : H ⧸ NS →* G ⧸ NR :=
    QuotientGroup.lift NS ((QuotientGroup.mk' NR).comp g) (by
      intro y hy
      rw [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff (N := NR) (g y)).2 (hgNS hy))
  refine
    { toFun := F
      invFun := K
      left_inv := ?_
      right_inv := ?_
      map_mul' := fun a b => F.map_mul a b }
  · intro x
    rcases QuotientGroup.mk'_surjective NR x with ⟨x, rfl⟩
    change K (F (QuotientGroup.mk' NR x)) = QuotientGroup.mk' NR x
    simp only [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_iff_div_mem (N := NR) (x := g (f x)) (y := x)).2
      (by simpa [NR, div_eq_mul_inv] using hgf x)
  · intro y
    rcases QuotientGroup.mk'_surjective NS y with ⟨y, rfl⟩
    change F (K (QuotientGroup.mk' NS y)) = QuotientGroup.mk' NS y
    simp only [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_iff_div_mem (N := NS) (x := f (g y)) (y := y)).2
      (by simpa [NS, div_eq_mul_inv] using hfg y)

/--
Mutual relator-quotient map data records forward and inverse homomorphisms that are inverse
modulo the two relator normal closures.
-/
structure RelatorQuotientMutualMapData
    (R : Set G) (S : Set H) where
  /-- The forward homomorphism from the source presentation group to the target one. -/
  toHom : G →* H
  /-- The homomorphism in the reverse direction. -/
  invHom : H →* G
  /-- The forward homomorphism sends each source relator into the target normal closure. -/
  mapsRelators : ∀ r ∈ R, toHom r ∈ Subgroup.normalClosure S
  /-- The reverse homomorphism sends each target relator into the source normal closure. -/
  mapsTargetRelators : ∀ s ∈ S, invHom s ∈ Subgroup.normalClosure R
  /-- The reverse-after-forward composite is the identity modulo the source relators. -/
  inv_toHom : ∀ x : G, invHom (toHom x) * x⁻¹ ∈ Subgroup.normalClosure R
  /-- The forward-after-reverse composite is the identity modulo the target relators. -/
  to_invHom : ∀ y : H, toHom (invHom y) * y⁻¹ ∈ Subgroup.normalClosure S

namespace RelatorQuotientMutualMapData

variable {R : Set G} {S : Set H} {T : Set K}

/-- The identity homomorphism gives reflexive mutual map data for a relator quotient. -/
def refl (R : Set G) :
    RelatorQuotientMutualMapData R R where
  toHom := MonoidHom.id G
  invHom := MonoidHom.id G
  mapsRelators := by
    intro r hr
    exact Subgroup.subset_normalClosure hr
  mapsTargetRelators := by
    intro r hr
    exact Subgroup.subset_normalClosure hr
  inv_toHom := by
    intro x
    simp only [MonoidHom.id_apply, mul_inv_cancel, one_mem]
  to_invHom := by
    intro x
    simp only [MonoidHom.id_apply, mul_inv_cancel, one_mem]

/-- Swapping the forward and inverse homomorphisms gives the symmetric mutual map data. -/
def symm
    (D : RelatorQuotientMutualMapData R S) :
    RelatorQuotientMutualMapData S R where
  toHom := D.invHom
  invHom := D.toHom
  mapsRelators := D.mapsTargetRelators
  mapsTargetRelators := D.mapsRelators
  inv_toHom := D.to_invHom
  to_invHom := D.inv_toHom

/--
Composing two pieces of mutual map data gives transitive mutual map data between relator
quotients.
-/
def trans
    (D₁ : RelatorQuotientMutualMapData R S)
    (D₂ : RelatorQuotientMutualMapData S T) :
    RelatorQuotientMutualMapData R T where
  toHom := D₂.toHom.comp D₁.toHom
  invHom := D₁.invHom.comp D₂.invHom
  mapsRelators := by
    intro r hr
    exact map_mem_normalClosure_of_relators D₂.toHom D₂.mapsRelators
      (D₁.mapsRelators r hr)
  mapsTargetRelators := by
    intro t ht
    exact map_mem_normalClosure_of_relators D₁.invHom D₁.mapsTargetRelators
      (D₂.mapsTargetRelators t ht)
  inv_toHom := by
    intro x
    let y : H := D₁.toHom x
    have h₂ :
        D₂.invHom (D₂.toHom y) * y⁻¹ ∈ Subgroup.normalClosure S :=
      D₂.inv_toHom y
    have h₂map :
        D₁.invHom (D₂.invHom (D₂.toHom y) * y⁻¹) ∈
          Subgroup.normalClosure R :=
      map_mem_normalClosure_of_relators D₁.invHom D₁.mapsTargetRelators h₂
    have h₂map' :
        D₁.invHom (D₂.invHom (D₂.toHom y)) *
            (D₁.invHom y)⁻¹ ∈
          Subgroup.normalClosure R := by
      simpa using h₂map
    have h₁ :
        D₁.invHom y * x⁻¹ ∈ Subgroup.normalClosure R :=
      D₁.inv_toHom x
    have hprod := Subgroup.mul_mem (Subgroup.normalClosure R) h₂map' h₁
    have hmul :
        (D₁.invHom (D₂.invHom (D₂.toHom y)) *
              (D₁.invHom y)⁻¹) *
            (D₁.invHom y * x⁻¹) =
          D₁.invHom (D₂.invHom (D₂.toHom y)) * x⁻¹ := by
      group
    simpa [MonoidHom.comp_apply, y, hmul] using hprod
  to_invHom := by
    intro z
    let y : H := D₂.invHom z
    have h₁ :
        D₁.toHom (D₁.invHom y) * y⁻¹ ∈ Subgroup.normalClosure S :=
      D₁.to_invHom y
    have h₁map :
        D₂.toHom (D₁.toHom (D₁.invHom y) * y⁻¹) ∈
          Subgroup.normalClosure T :=
      map_mem_normalClosure_of_relators D₂.toHom D₂.mapsRelators h₁
    have h₁map' :
        D₂.toHom (D₁.toHom (D₁.invHom y)) *
            (D₂.toHom y)⁻¹ ∈
          Subgroup.normalClosure T := by
      simpa using h₁map
    have h₂ :
        D₂.toHom y * z⁻¹ ∈ Subgroup.normalClosure T :=
      D₂.to_invHom z
    have hprod := Subgroup.mul_mem (Subgroup.normalClosure T) h₁map' h₂
    have hmul :
        (D₂.toHom (D₁.toHom (D₁.invHom y)) *
              (D₂.toHom y)⁻¹) *
            (D₂.toHom y * z⁻¹) =
          D₂.toHom (D₁.toHom (D₁.invHom y)) * z⁻¹ := by
      group
    simpa [MonoidHom.comp_apply, y, hmul] using hprod

end RelatorQuotientMutualMapData

/-- Equal normal closures provide mutual relator-quotient map data using the identity maps. -/
def relatorQuotientMutualMapDataOfNormalClosureEq
    {R S : Set G}
    (h : Subgroup.normalClosure R = Subgroup.normalClosure S) :
    RelatorQuotientMutualMapData R S where
  toHom := MonoidHom.id G
  invHom := MonoidHom.id G
  mapsRelators := by
    intro r hr
    rw [← h]
    exact Subgroup.subset_normalClosure hr
  mapsTargetRelators := by
    intro s hs
    rw [h]
    exact Subgroup.subset_normalClosure hs
  inv_toHom := by
    intro x
    simp only [MonoidHom.id_apply, mul_inv_cancel, one_mem]
  to_invHom := by
    intro x
    simp only [MonoidHom.id_apply, mul_inv_cancel, one_mem]

/-- Relator-equivalent defining relators give mutual map data between the relator quotients. -/
def relatorQuotientMutualMapDataOfRelatorEquivalent
    {R S : Set G}
    (hR_to_S : ∀ r ∈ R, RelatorEquivalent S r 1)
    (hS_to_R : ∀ s ∈ S, RelatorEquivalent R s 1) :
    RelatorQuotientMutualMapData R S :=
  relatorQuotientMutualMapDataOfNormalClosureEq
    (normalClosure_eq_of_relatorEquivalent hR_to_S hS_to_R)

/--
A multiplicative equivalence carrying one normal closure to the other provides mutual
relator-quotient map data.
-/
def relatorQuotientMutualMapDataOfNormalClosureMapEq
    (R : Set G) (S : Set H) (e : G ≃* H)
    (hmap :
      Subgroup.map e.toMonoidHom (Subgroup.normalClosure R) =
        Subgroup.normalClosure S) :
    RelatorQuotientMutualMapData R S where
  toHom := e.toMonoidHom
  invHom := e.symm.toMonoidHom
  mapsRelators := by
    intro r hr
    have hrmap : e r ∈ Subgroup.map e.toMonoidHom (Subgroup.normalClosure R) :=
      ⟨r, Subgroup.subset_normalClosure hr, rfl⟩
    rw [← hmap]
    exact hrmap
  mapsTargetRelators := by
    intro s hs
    have hsmap : s ∈ Subgroup.map e.toMonoidHom (Subgroup.normalClosure R) := by
      rw [hmap]
      exact Subgroup.subset_normalClosure hs
    rcases hsmap with ⟨r, hr, hrs⟩
    simpa [← hrs] using hr
  inv_toHom := by
    intro x
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulEquiv.symm_apply_apply,
        mul_inv_cancel, one_mem]
  to_invHom := by
    intro y
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulEquiv.apply_symm_apply,
        mul_inv_cancel, one_mem]

/--
A multiplicative equivalence identifies normal closures when the images of relators in both
directions lie in the corresponding normal closures.
-/
theorem map_normalClosure_eq_of_mulEquiv_relator_images_mem_normalClosure
    (e : G ≃* H) (R : Set G) (S : Set H)
    (hR_to_S : ∀ r ∈ R, e r ∈ Subgroup.normalClosure S)
    (hS_to_R : ∀ s ∈ S, e.symm s ∈ Subgroup.normalClosure R) :
    Subgroup.map e.toMonoidHom (Subgroup.normalClosure R) =
      Subgroup.normalClosure S := by
  apply le_antisymm
  · rw [Subgroup.map_normalClosure _ e.toMonoidHom e.surjective]
    refine Subgroup.normalClosure_le_normal ?_
    rintro z ⟨r, hr, rfl⟩
    exact hR_to_S r hr
  · rw [Subgroup.map_normalClosure _ e.toMonoidHom e.surjective]
    refine Subgroup.normalClosure_le_normal ?_
    intro s hs
    have hsmap : s ∈ Subgroup.map e.toMonoidHom (Subgroup.normalClosure R) :=
      ⟨e.symm s, hS_to_R s hs, by simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
          MulEquiv.apply_symm_apply]⟩
    rwa [Subgroup.map_normalClosure _ e.toMonoidHom e.surjective] at hsmap


end ReidemeisterSchreier.Discrete.Presentations

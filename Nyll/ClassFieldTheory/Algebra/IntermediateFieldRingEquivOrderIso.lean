/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.Logic.Equiv.Set

/-!
# Intermediate fields under compatible base and ambient equivalences

The image is the actual image subfield of the specified ambient equivalence.
No replacement embedding or closure is selected in this construction.
-/

@[expose] public section

noncomputable section

namespace ClassFieldTheory

universe u v w x

variable {K : Type u} {Ω : Type v} {M : Type w} {Ψ : Type x}
  [Field K] [Field Ω] [Field M] [Field Ψ] [Algebra K Ω] [Algebra M Ψ]

/-- The image of an intermediate field under compatible equivalences of its
base and ambient fields. -/
def intermediateFieldMapRingEquiv
    (e : K ≃+* M) (c : Ω ≃+* Ψ)
    (hc : ∀ a : K, c (algebraMap K Ω a) = algebraMap M Ψ (e a))
    (L : IntermediateField K Ω) : IntermediateField M Ψ := by
  refine (L.toSubfield.map c.toRingHom).toIntermediateField ?_
  intro a
  refine ⟨algebraMap K Ω (e.symm a), L.algebraMap_mem _, ?_⟩
  change c (algebraMap K Ω (e.symm a)) = algebraMap M Ψ a
  rw [hc, e.apply_symm_apply]

/-- The restricted ambient equivalence acts on the same elements of the
original intermediate field. -/
def intermediateFieldMapRingEquivEquiv
    (e : K ≃+* M) (c : Ω ≃+* Ψ)
    (hc : ∀ a : K, c (algebraMap K Ω a) = algebraMap M Ψ (e a))
    (L : IntermediateField K Ω) :
    L ≃+* intermediateFieldMapRingEquiv e c hc L where
  toFun a := ⟨c a, ⟨a, a.property, rfl⟩⟩
  invFun b := ⟨c.symm b, by
    obtain ⟨a, ha, hab⟩ := b.property
    have hba : c.symm (b : Ψ) = a := by
      rw [← hab]
      exact c.symm_apply_apply a
    exact hba.symm ▸ ha⟩
  left_inv a := Subtype.ext (c.symm_apply_apply a)
  right_inv b := Subtype.ext (c.apply_symm_apply b)
  map_mul' a b := Subtype.ext (c.map_mul a b)
  map_add' a b := Subtype.ext (c.map_add a b)

/-- The restricted map retains the value of the original ambient map. -/
@[simp]
theorem intermediateFieldMapRingEquivEquiv_apply
    (e : K ≃+* M) (c : Ω ≃+* Ψ)
    (hc : ∀ a : K, c (algebraMap K Ω a) = algebraMap M Ψ (e a))
    (L : IntermediateField K Ω) (a : L) :
    (intermediateFieldMapRingEquivEquiv e c hc L a : Ψ) = c a :=
  rfl

/-- The restricted equivalence and the specified base equivalence commute
with the actual intermediate-field embeddings. -/
theorem intermediateFieldMapRingEquivEquiv_commutes
    (e : K ≃+* M) (c : Ω ≃+* Ψ)
    (hc : ∀ a : K, c (algebraMap K Ω a) = algebraMap M Ψ (e a))
    (L : IntermediateField K Ω) :
    (algebraMap M (intermediateFieldMapRingEquiv e c hc L)).comp e.toRingHom =
      (intermediateFieldMapRingEquivEquiv e c hc L).toRingHom.comp
        (algebraMap K L) := by
  apply RingHom.ext
  intro a
  apply Subtype.ext
  exact (hc a).symm

/-- Compatibility also holds for the inverse equivalences. -/
theorem intermediateFieldMapRingEquiv_symm_commutes
    (e : K ≃+* M) (c : Ω ≃+* Ψ)
    (hc : ∀ a : K, c (algebraMap K Ω a) = algebraMap M Ψ (e a))
    (a : M) :
    c.symm (algebraMap M Ψ a) = algebraMap K Ω (e.symm a) := by
  apply c.injective
  rw [c.apply_symm_apply, hc, e.apply_symm_apply]

/-- Compatible equivalences give an order equivalence of the actual
intermediate-field lattices. -/
def intermediateFieldRingEquivOrderIso
    (e : K ≃+* M) (c : Ω ≃+* Ψ)
    (hc : ∀ a : K, c (algebraMap K Ω a) = algebraMap M Ψ (e a)) :
    IntermediateField K Ω ≃o IntermediateField M Ψ where
  toFun := intermediateFieldMapRingEquiv e c hc
  invFun := intermediateFieldMapRingEquiv e.symm c.symm
    (intermediateFieldMapRingEquiv_symm_commutes e c hc)
  left_inv L := by
    apply SetLike.coe_injective
    change c.symm '' (c '' (L : Set Ω)) = (L : Set Ω)
    exact c.toEquiv.symm_image_image _
  right_inv L := by
    apply SetLike.coe_injective
    change c '' (c.symm '' (L : Set Ψ)) = (L : Set Ψ)
    exact c.toEquiv.image_symm_image _
  map_rel_iff' := by
    intro L N
    change c '' (L : Set Ω) ⊆ c '' (N : Set Ω) ↔ (L : Set Ω) ⊆ N
    exact Set.image_subset_image_iff c.injective

end ClassFieldTheory

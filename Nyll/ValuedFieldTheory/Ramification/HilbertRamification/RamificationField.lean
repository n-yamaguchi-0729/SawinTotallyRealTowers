/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RamificationGroup

/-!
# Hilbert ramification theory: ramification field

This file contains the fixed-field part of the ramification-field definition, over the
decomposition field `Z_w`.  The base valuation-subring file owns
the definitions of `G_w`, `I_w`, `R_w`, `Z_w`, `T_w`, and `V_w`; here we record
the tower-level Galois correspondence for `G(L / V_w)` as a subgroup of
`G(L / Z_w)`.
-/

namespace RamificationTheory


noncomputable section

universe u v

namespace HilbertRamification
namespace ValuationSubring


variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]

/-- Prime-decomposition statement:
identify inertia with the Galois group over the inertia field. -/
def inertiaGroupEquivGalInertiaField_of_finiteDimensional
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    inertiaGroup K A ≃* (L ≃ₐ[inertiaField K A] L) :=
  (inertiaGroupEquivInAut (K := K) A).trans
    (inertiaGroupInAutEquivGalInertiaField_of_finiteDimensional (K := K) A)

/-- `L/T_w` is Galois because `T_w` is the fixed field of the inertia group. -/
instance inertiaField_isGalois
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    IsGalois (inertiaField K A) L :=
  IsGalois.of_fixed_field L (inertiaGroupInAut K A)

/-- States the theorem `inertiaGroupEquivGalInertiaField_of_finiteDimensional_apply`. -/
@[simp] theorem inertiaGroupEquivGalInertiaField_of_finiteDimensional_apply
    [FiniteDimensional K L] (A : _root_.ValuationSubring L)
    (σ : inertiaGroup K A) (x : L) :
    inertiaGroupEquivGalInertiaField_of_finiteDimensional (K := K) A σ x =
      ((σ : decompositionGroup K A) : L ≃ₐ[K] L) x :=
  rfl

/-- States the theorem `mem_ramificationFieldOverInertiaField_iff`. -/
@[simp] theorem mem_ramificationFieldOverInertiaField_iff
    (A : _root_.ValuationSubring L) (x : L) :
    x ∈ ramificationFieldOverInertiaField K A ↔
      ∀ σ : ramificationGroup K A,
        (((σ : inertiaGroup K A) : decompositionGroup K A) : L ≃ₐ[K] L) x = x := by
  rw [ramificationFieldOverInertiaField,
    IntermediateField.mem_extendScalars, mem_ramificationField_iff]

/-- The ramification field satisfies:
view `R_w` as a subgroup of `G(L/T_w)`. -/
def ramificationGroupToGalInertiaField
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    ramificationGroup K A →* (L ≃ₐ[inertiaField K A] L) :=
  (inertiaGroupEquivGalInertiaField_of_finiteDimensional (K := K) A).toMonoidHom.comp
    (ramificationGroup K A).subtype

/-- States the theorem `ramificationGroupToGalInertiaField_apply`. -/
@[simp] theorem ramificationGroupToGalInertiaField_apply
    [FiniteDimensional K L] (A : _root_.ValuationSubring L)
    (σ : ramificationGroup K A) (x : L) :
    ramificationGroupToGalInertiaField (K := K) A σ x =
      (((σ : inertiaGroup K A) : decompositionGroup K A) : L ≃ₐ[K] L) x :=
  rfl

/-- The ramification field satisfies:
the transported ramification subgroup inside `G(L/T_w)`. -/
abbrev ramificationGroupOverInertiaField
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    Subgroup (L ≃ₐ[inertiaField K A] L) :=
  (ramificationGroupToGalInertiaField (K := K) A).range

/-- States the theorem `mem_ramificationGroupOverInertiaField_iff`. -/
@[simp] theorem mem_ramificationGroupOverInertiaField_iff
    [FiniteDimensional K L] (A : _root_.ValuationSubring L)
    (σ : L ≃ₐ[inertiaField K A] L) :
    σ ∈ ramificationGroupOverInertiaField (K := K) A ↔
      ∃ τ : ramificationGroup K A,
        ramificationGroupToGalInertiaField (K := K) A τ = σ :=
  MonoidHom.mem_range

/-- The transported subgroup agrees with the image of `R_w` under
`I_w = G(L/T_w)`. -/
theorem ramificationGroupOverInertiaField_eq_map
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    Subgroup.map (inertiaGroupEquivGalInertiaField_of_finiteDimensional (K := K) A).toMonoidHom
        (ramificationGroup K A) =
      ramificationGroupOverInertiaField (K := K) A := by
  ext σ
  rw [mem_ramificationGroupOverInertiaField_iff]
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨⟨τ, hτ⟩, rfl⟩
  · rintro ⟨τ, rfl⟩
    exact ⟨(τ : inertiaGroup K A), τ.property, rfl⟩

/-- The transported ramification subgroup is normal in `G(L/T_w)`. -/
instance ramificationGroupOverInertiaField_normal
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    (ramificationGroupOverInertiaField (K := K) A).Normal := by
  let e := inertiaGroupEquivGalInertiaField_of_finiteDimensional (K := K) A
  rw [← ramificationGroupOverInertiaField_eq_map (K := K) A]
  simpa [e] using
    (Subgroup.Normal.map (ramificationGroup_normal (K := K) A)
      e.toMonoidHom e.surjective)

/-- The ramification field satisfies:
the fixed field of the transported ramification subgroup over `T_w` is `V_w`.
-/
theorem ramificationFieldOverInertiaField_fixedField_eq_of_finiteDimensional
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    IntermediateField.fixedField
        (ramificationGroupOverInertiaField (K := K) A) =
      ramificationFieldOverInertiaField K A := by
  ext x
  rw [IntermediateField.mem_fixedField_iff,
    mem_ramificationFieldOverInertiaField_iff]
  constructor
  · intro hx τ
    have hτ :
        ramificationGroupToGalInertiaField (K := K) A τ ∈
          ramificationGroupOverInertiaField (K := K) A := by
      exact ⟨τ, rfl⟩
    simpa using hx
      (ramificationGroupToGalInertiaField (K := K) A τ) hτ
  · intro hx σ hσ
    rcases
      (mem_ramificationGroupOverInertiaField_iff (K := K) A σ).mp hσ with
      ⟨τ, rfl⟩
    simpa using hx τ

/-- The ramification field satisfies:
`G(L/V_w)` over the inertia field is the transported ramification subgroup.
-/
theorem ramificationFieldOverInertiaField_fixingSubgroup_eq_of_finiteDimensional
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    (ramificationFieldOverInertiaField K A).fixingSubgroup =
      ramificationGroupOverInertiaField (K := K) A := by
  rw [← ramificationFieldOverInertiaField_fixedField_eq_of_finiteDimensional
    (K := K) A]
  exact
    IntermediateField.fixingSubgroup_fixedField
      (ramificationGroupOverInertiaField (K := K) A)

/-- Inertia-character exactness:
transport the quotient `I_w/R_w` along `I_w = G(L/T_w)`. -/
def inertiaGroupQuotientRamificationEquivGalInertiaQuotient_of_finiteDimensional
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    inertiaGroup K A ⧸ ramificationGroup K A ≃*
      (L ≃ₐ[inertiaField K A] L) ⧸
        ramificationGroupOverInertiaField (K := K) A :=
  QuotientGroup.congr
    (ramificationGroup K A)
    (ramificationGroupOverInertiaField (K := K) A)
    (inertiaGroupEquivGalInertiaField_of_finiteDimensional (K := K) A)
    (ramificationGroupOverInertiaField_eq_map (K := K) A)

/-- Inertia-character exactness:
the Galois correspondence gives `G(L/T_w)/R_w ≃ G(V_w/T_w)`. -/
def galInertiaQuotientRamificationEquivGalRamificationFieldOverInertia_of_finiteDimensional
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    (L ≃ₐ[inertiaField K A] L) ⧸
        ramificationGroupOverInertiaField (K := K) A ≃*
      (ramificationFieldOverInertiaField K A ≃ₐ[inertiaField K A]
        ramificationFieldOverInertiaField K A) := by
  rw [← ramificationFieldOverInertiaField_fixedField_eq_of_finiteDimensional
    (K := K) A]
  exact
    IsGalois.normalAutEquivQuotient
      (ramificationGroupOverInertiaField (K := K) A)

/-- Inertia-character exactness:
the quotient `I_w/R_w` is the Galois group of the ramification field over the
inertia field. -/
def inertiaGroupQuotientRamificationEquivGalRamificationFieldOverInertia_of_finiteDimensional
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    inertiaGroup K A ⧸ ramificationGroup K A ≃*
      (ramificationFieldOverInertiaField K A ≃ₐ[inertiaField K A]
        ramificationFieldOverInertiaField K A) :=
  (inertiaGroupQuotientRamificationEquivGalInertiaQuotient_of_finiteDimensional
    (K := K) A).trans
    (galInertiaQuotientRamificationEquivGalRamificationFieldOverInertia_of_finiteDimensional
      (K := K) A)

/-- States the theorem `mem_ramificationFieldOverDecompositionField_iff`. -/
@[simp] theorem mem_ramificationFieldOverDecompositionField_iff
    (A : _root_.ValuationSubring L) (x : L) :
    x ∈ ramificationFieldOverDecompositionField K A ↔
      ∀ σ : ramificationGroup K A,
        (((σ : inertiaGroup K A) : decompositionGroup K A) : L ≃ₐ[K] L) x = x := by
  rw [ramificationFieldOverDecompositionField,
    IntermediateField.mem_extendScalars, mem_ramificationField_iff]

/-- The ramification field satisfies:
view `R_w` as a subgroup of `G(L/Z_w)` through the decomposition-field
identification `G_w = G(L/Z_w)`. -/
def ramificationGroupToGalDecompositionField
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    ramificationGroup K A →* (L ≃ₐ[decompositionField K A] L) :=
  (decompositionGroupEquivGalDecompositionField_of_finiteDimensional
    (K := K) A).toMonoidHom.comp
    ((inertiaGroup K A).subtype.comp (ramificationGroup K A).subtype)

/-- States the theorem `ramificationGroupToGalDecompositionField_apply`. -/
@[simp] theorem ramificationGroupToGalDecompositionField_apply
    [FiniteDimensional K L] (A : _root_.ValuationSubring L)
    (σ : ramificationGroup K A) :
    ramificationGroupToGalDecompositionField (K := K) A σ =
      decompositionGroupEquivGalDecompositionField_of_finiteDimensional
        (K := K) A ((σ : inertiaGroup K A) : decompositionGroup K A) :=
  rfl

/-- The ramification field satisfies:
the transported ramification subgroup inside `G(L/Z_w)`. -/
abbrev ramificationGroupOverDecompositionField
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    Subgroup (L ≃ₐ[decompositionField K A] L) :=
  (ramificationGroupToGalDecompositionField (K := K) A).range

/-- States the theorem `mem_ramificationGroupOverDecompositionField_iff`. -/
@[simp] theorem mem_ramificationGroupOverDecompositionField_iff
    [FiniteDimensional K L] (A : _root_.ValuationSubring L)
    (σ : L ≃ₐ[decompositionField K A] L) :
    σ ∈ ramificationGroupOverDecompositionField (K := K) A ↔
      ∃ τ : ramificationGroup K A,
        ramificationGroupToGalDecompositionField (K := K) A τ = σ :=
  MonoidHom.mem_range

/-- The ramification field satisfies:
the fixed field of the transported ramification subgroup over `Z_w` is `V_w`.
-/
theorem ramificationFieldOverDecompositionField_fixedField_eq_of_finiteDimensional
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    IntermediateField.fixedField
        (ramificationGroupOverDecompositionField (K := K) A) =
      ramificationFieldOverDecompositionField K A := by
  ext x
  rw [IntermediateField.mem_fixedField_iff,
    mem_ramificationFieldOverDecompositionField_iff]
  constructor
  · intro hx τ
    have hτ :
        ramificationGroupToGalDecompositionField (K := K) A τ ∈
          ramificationGroupOverDecompositionField (K := K) A := by
      exact ⟨τ, rfl⟩
    simpa using hx
      (ramificationGroupToGalDecompositionField (K := K) A τ) hτ
  · intro hx σ hσ
    rcases
      (mem_ramificationGroupOverDecompositionField_iff (K := K) A σ).mp hσ with
      ⟨τ, rfl⟩
    simpa using hx τ

/-- The ramification field satisfies:
`G(L/V_w)` over the decomposition field is the transported ramification
subgroup. -/
theorem ramificationFieldOverDecompositionField_fixingSubgroup_eq_of_finiteDimensional
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    (ramificationFieldOverDecompositionField K A).fixingSubgroup =
      ramificationGroupOverDecompositionField (K := K) A := by
  rw [← ramificationFieldOverDecompositionField_fixedField_eq_of_finiteDimensional
    (K := K) A]
  exact
    IntermediateField.fixingSubgroup_fixedField
      (ramificationGroupOverDecompositionField (K := K) A)

/-- The ramification field satisfies:
the transported ramification group is the Galois group `G(L/V_w)` in the tower
`Z_w ⊆ V_w ⊆ L`. -/
def ramificationGroupEquivGalOverDecompositionField
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    ramificationGroupOverDecompositionField (K := K) A ≃*
      (L ≃ₐ[ramificationFieldOverDecompositionField K A] L) :=
  (MulEquiv.subgroupCongr
      (ramificationFieldOverDecompositionField_fixingSubgroup_eq_of_finiteDimensional
        (K := K) A).symm).trans
    (IntermediateField.fixingSubgroupEquiv
      (ramificationFieldOverDecompositionField K A))

end ValuationSubring
end HilbertRamification

end
end RamificationTheory

import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.GroupTheory.PGroup

set_option autoImplicit false

/-!
# Galois p-groups in binary composita

Restriction embeds the automorphism group of a compositum of normal
subextensions into the product of their automorphism groups. Consequently,
p-group automorphism groups are preserved by composita. This applies in
particular to finite Galois extensions; neither finiteness nor primality of
`p` is needed for the group-theoretic argument.
-/

universe u v w

namespace ClassFieldTower.Sawin

private theorem isPGroup_prod
    {p : ℕ} {G : Type u} {H : Type v} [Group G] [Group H]
    (hG : IsPGroup p G) (hH : IsPGroup p H) :
    IsPGroup p (G × H) := by
  rintro ⟨g, h⟩
  obtain ⟨a, ha⟩ := hG g
  obtain ⟨b, hb⟩ := hH h
  refine ⟨a + b, Prod.ext ?_ ?_⟩
  · change g ^ p ^ (a + b) = 1
    rw [pow_add, pow_mul, ha, one_pow]
  · change h ^ p ^ (a + b) = 1
    rw [Nat.add_comm, pow_add, pow_mul, hb, one_pow]

/-- The Galois group of a compositum of normal intermediate fields is a
p-group when both factors have p-group Galois groups. In particular, this
preserves p-group Galois groups of finite Galois extensions. -/
theorem isPGroup_galois_sup
    {p : ℕ} {K : Type u} {Ω : Type w}
    [Field K] [Field Ω] [Algebra K Ω]
    (E₁ E₂ : IntermediateField K Ω) [Normal K E₁] [Normal K E₂]
    (h₁ : IsPGroup p (E₁ ≃ₐ[K] E₁))
    (h₂ : IsPGroup p (E₂ ≃ₐ[K] E₂)) :
    IsPGroup p
      ((E₁ ⊔ E₂ : IntermediateField K Ω) ≃ₐ[K]
        (E₁ ⊔ E₂ : IntermediateField K Ω)) := by
  let S : IntermediateField K Ω := E₁ ⊔ E₂
  let A : IntermediateField K S :=
    IntermediateField.restrict (show E₁ ≤ E₁ ⊔ E₂ from le_sup_left)
  let B : IntermediateField K S :=
    IntermediateField.restrict (show E₂ ≤ E₁ ⊔ E₂ from le_sup_right)
  let eA : E₁ ≃ₐ[K] A :=
    IntermediateField.restrictAlgEquiv (show E₁ ≤ E₁ ⊔ E₂ from le_sup_left)
  let eB : E₂ ≃ₐ[K] B :=
    IntermediateField.restrictAlgEquiv (show E₂ ≤ E₁ ⊔ E₂ from le_sup_right)
  let : Normal K A := Normal.of_algEquiv eA
  let : Normal K B := Normal.of_algEquiv eB
  let rA : (S ≃ₐ[K] S) →* (A ≃ₐ[K] A) := AlgEquiv.restrictNormalHom A
  let rB : (S ≃ₐ[K] S) →* (B ≃ₐ[K] B) := AlgEquiv.restrictNormalHom B
  have hA : IsPGroup p (A ≃ₐ[K] A) := h₁.of_equiv (AlgEquiv.autCongr eA)
  have hB : IsPGroup p (B ≃ₐ[K] B) := h₂.of_equiv (AlgEquiv.autCongr eB)
  apply (isPGroup_prod hA hB).of_injective (rA.prod rB)
  apply (MonoidHom.ker_eq_bot_iff (rA.prod rB)).mp
  rw [MonoidHom.ker_prod]
  change (AlgEquiv.restrictNormalHom A).ker ⊓
      (AlgEquiv.restrictNormalHom B).ker = ⊥
  rw [IntermediateField.restrictNormalHom_ker,
    IntermediateField.restrictNormalHom_ker,
    ← IntermediateField.fixingSubgroup_sup]
  have hSup : A ⊔ B = ⊤ := by
    apply IntermediateField.lift_injective S
    rw [IntermediateField.lift_sup,
      IntermediateField.lift_restrict,
      IntermediateField.lift_restrict,
      IntermediateField.lift_top]
  rw [hSup, IntermediateField.fixingSubgroup_top]

end ClassFieldTower.Sawin

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Basic

/-!
# Principal ideles and the idele class group

Principal idèles and the class projection are defined on the standard
idele group of adele units.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

namespace NumberField

variable {K}

/-- Ring-of-integers units mapped to the units of the number field. -/
def ringUnitToFieldUnit : (𝓞 K)ˣ →* Kˣ :=
  Units.map (algebraMap (𝓞 K) K)

end NumberField

namespace IdeleGroup

/-- The diagonal embedding of `Kˣ` into the idele group. -/
abbrev principalIdele : Kˣ →* IdeleGroup K :=
  NumberField.IdeleGroup.unitEmbedding (𝓞 K) K

variable {K}

/-- The finite component of a principal idele is the image of the
underlying field element in the corresponding completion. -/
@[simp]
theorem finiteComponent_principalIdele
    (x : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ((finiteComponent v (principalIdele K x) :
      (v.adicCompletion K)ˣ) : v.adicCompletion K) = (x : K) :=
  rfl

/-- The infinite component of a principal idele is the image of the
underlying field element in the corresponding completion. -/
@[simp]
theorem infiniteComponent_principalIdele
    (x : Kˣ) (w : InfinitePlace K) :
    ((infiniteComponent w (principalIdele K x) :
      w.Completionˣ) : w.Completion) = (x : K) := by
  change algebraMap K w.Completion (x : K) = (x : K)
  rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
    Algebra.algebraMap_self_apply]

variable (K)

/-- The diagonal map from field units to ideles is injective. -/
theorem principalIdele_injective :
    Function.Injective (principalIdele K) :=
  Units.map_injective
    (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 K) (K := K))

/-- The subgroup of principal ideles. -/
abbrev principalSubgroup : Subgroup (IdeleGroup K) :=
  NumberField.IdeleGroup.principalSubgroup (𝓞 K) K

/-- The multiplicative group `Kˣ`, identified with the subgroup of principal
ideles. -/
def principalEquiv : Kˣ ≃* principalSubgroup K :=
  MonoidHom.ofInjective (principalIdele_injective K)

@[simp]
theorem coe_principalEquiv (x : Kˣ) :
    (principalEquiv K x : IdeleGroup K) = principalIdele K x :=
  MonoidHom.ofInjective_apply (principalIdele_injective K)

end IdeleGroup

/-- The idele class group `C_K = I_K / Kˣ`. -/
abbrev IdeleClassGroup := NumberField.IdeleClassGroup (𝓞 K) K

namespace IdeleGroup

/-- The quotient homomorphism from idèles to their classes. -/
abbrev toStandardClass : IdeleGroup K →* IdeleClassGroup K :=
  QuotientGroup.mk' (principalSubgroup K)

/-- The class of an idèle in the principal quotient. -/
theorem toStandardClass_apply (a : IdeleGroup K) :
    toStandardClass K a = QuotientGroup.mk' (principalSubgroup K) a :=
  rfl

/-- Every idèle class has a representative. -/
theorem toStandardClass_surjective : Function.Surjective (toStandardClass K) :=
  QuotientGroup.mk'_surjective (principalSubgroup K)

/-- Multiplication on the standard principal quotient is commutative. -/
instance : IsMulCommutative (IdeleClassGroup K) := by
  refine IsMulCommutative.of_comm ?_
  intro a b
  obtain ⟨x, rfl⟩ := toStandardClass_surjective K a
  obtain ⟨y, rfl⟩ := toStandardClass_surjective K b
  rw [← map_mul, ← map_mul, mul_comm x y]

/-- Use the Mathlib commutative group structure on quotients of the standard class group. -/
instance classQuotientCommGroup (H : Subgroup (IdeleClassGroup K)) :
    CommGroup (IdeleClassGroup K ⧸ H) :=
  @QuotientGroup.Quotient.commGroup (IdeleClassGroup K)
    (QuotientGroup.Quotient.commGroup (principalSubgroup K)) H

/-- The kernel of the class projection is the subgroup of principal idèles. -/
theorem toStandardClass_ker : (toStandardClass K).ker = principalSubgroup K :=
  QuotientGroup.ker_mk' (principalSubgroup K)

/-- A principal idèle has trivial class in the standard quotient. -/
@[simp]
theorem toStandardClass_principalIdele (x : Kˣ) :
    toStandardClass K (principalIdele K x) = 1 := by
  apply MonoidHom.mem_ker.mp
  rw [toStandardClass_ker]
  exact ⟨x, rfl⟩

/-- A raw idele has trivial class exactly when it is principal. -/
theorem toStandardClass_eq_one_iff (a : IdeleGroup K) :
    toStandardClass K a = 1 ↔ a ∈ principalSubgroup K := by
  change a ∈ (toStandardClass K).ker ↔ a ∈ principalSubgroup K
  rw [toStandardClass_ker]

/-- Two raw ideles represent the same class exactly when their ratio is principal. -/
theorem toStandardClass_eq_iff (a b : IdeleGroup K) :
    toStandardClass K a = toStandardClass K b ↔ a⁻¹ * b ∈ principalSubgroup K :=
  eq_comm.trans ((MonoidHom.eq_iff (toStandardClass K)).trans (by rw [toStandardClass_ker]))

/-- Prove a property of idèle classes by choosing a representative in raw coordinates. -/
@[elab_as_elim]
theorem toStandardClass_induction_on {P : IdeleClassGroup K → Prop} (c : IdeleClassGroup K)
    (h : ∀ a : IdeleGroup K, P (toStandardClass K a)) : P c := by
  obtain ⟨a, rfl⟩ := toStandardClass_surjective K c
  exact h a

section Lift

variable {G : Type*} [Monoid G]

/-- Descend a homomorphism that kills principal idèles. -/
noncomputable def liftToStandardClass (f : IdeleGroup K →* G)
    (h : principalSubgroup K ≤ f.ker) : IdeleClassGroup K →* G :=
  QuotientGroup.lift (principalSubgroup K) f h

/-- The descended homomorphism has the original value on each representative. -/
@[simp]
theorem liftToStandardClass_toStandardClass (f : IdeleGroup K →* G)
    (h : principalSubgroup K ≤ f.ker) (a : IdeleGroup K) :
    liftToStandardClass K f h (toStandardClass K a) = f a :=
  QuotientGroup.lift_mk (principalSubgroup K) h a

end Lift

variable (L : Type*) [Field L] [NumberField L]

/-- The map on classes induced by a raw idele homomorphism preserving principal ideles. -/
noncomputable def mapStandardClass (f : IdeleGroup K →* IdeleGroup L)
    (h : principalSubgroup K ≤ (principalSubgroup L).comap f) :
    IdeleClassGroup K →* IdeleClassGroup L :=
  liftToStandardClass K ((toStandardClass L).comp f)
    (fun a ha => (toStandardClass_eq_one_iff L (f a)).2 (h ha))

/-- On representatives the class homomorphism applies the original raw homomorphism. -/
@[simp]
theorem mapStandardClass_toStandardClass (f : IdeleGroup K →* IdeleGroup L)
    (h : principalSubgroup K ≤ (principalSubgroup L).comap f) (a : IdeleGroup K) :
    mapStandardClass K L f h (toStandardClass K a) = toStandardClass L (f a) :=
  liftToStandardClass_toStandardClass K _ _ a

end IdeleGroup

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.IntermediateFieldRingEquivOrderIso
public import Nyll.ProCGroups.Abelian.TopologicalAbelianization
public import Nyll.GaloisCohomology.Topology.GaloisConjugation
public import Mathlib.FieldTheory.AbsoluteGaloisGroup

/-!
# Absolute Galois groups under an equivalence of base fields

A field equivalence extends to an equivalence of the chosen algebraic closures.
Conjugation then identifies the absolute Galois groups, including their Krull
topologies, and hence their topological abelianizations.
-/

@[expose] public section

noncomputable section

namespace ClassFieldTheory

universe u v w z

variable {K : Type u} {M : Type v} {Ω : Type w} {Ψ : Type z}
  [Field K] [Field M] [Field Ω] [Field Ψ]
  [Algebra K Ω] [Algebra M Ψ]

/-- The inverse semilinear equivalence respects the inverse coefficient map. -/
theorem semilinear_symm_algebraMap (e : K ≃+* M) (E : Ω ≃+* Ψ)
    (hE : ∀ x : K, E (algebraMap K Ω x) = algebraMap M Ψ (e x))
    (y : M) :
    E.symm (algebraMap M Ψ y) = algebraMap K Ω (e.symm y) := by
  apply E.injective
  rw [E.apply_symm_apply, hE, e.apply_symm_apply]

/-- Conjugation transports a Galois automorphism along compatible field equivalences. -/
def semilinearGaloisConjugate (e : K ≃+* M) (E : Ω ≃+* Ψ)
    (hE : ∀ x : K, E (algebraMap K Ω x) = algebraMap M Ψ (e x))
    (σ : Gal(Ω/K)) : Gal(Ψ/M) where
  toRingEquiv := (E.symm.trans σ.toRingEquiv).trans E
  commutes' := by
    intro y
    change E (σ (E.symm (algebraMap M Ψ y))) = algebraMap M Ψ y
    rw [semilinear_symm_algebraMap e E hE y, σ.commutes, hE,
      e.apply_symm_apply]

/-- Compatible field equivalences identify their Galois groups. -/
def semilinearGaloisEquiv (e : K ≃+* M) (E : Ω ≃+* Ψ)
    (hE : ∀ x : K, E (algebraMap K Ω x) = algebraMap M Ψ (e x)) :
    Gal(Ω/K) ≃* Gal(Ψ/M) where
  toFun := semilinearGaloisConjugate e E hE
  invFun := semilinearGaloisConjugate e.symm E.symm
    (semilinear_symm_algebraMap e E hE)
  left_inv σ := by
    apply AlgEquiv.ext
    intro x
    simp [semilinearGaloisConjugate]
  right_inv σ := by
    apply AlgEquiv.ext
    intro x
    simp [semilinearGaloisConjugate]
  map_mul' σ τ := by
    apply AlgEquiv.ext
    intro x
    simp [semilinearGaloisConjugate, AlgEquiv.mul_apply]

/-- Semilinear conjugation identifies the Krull topological Galois groups. -/
def semilinearGaloisContinuousEquiv (e : K ≃+* M) (E : Ω ≃+* Ψ)
    (hE : ∀ x : K, E (algebraMap K Ω x) = algebraMap M Ψ (e x)) :
    Gal(Ω/K) ≃ₜ* Gal(Ψ/M) where
  toMulEquiv := semilinearGaloisEquiv e E hE
  continuous_toFun :=
    RamificationTheory.Field.absoluteGaloisGroup.semilinear_conjugation_continuous
      e E hE (semilinearGaloisEquiv e E hE).toMonoidHom (by intro σ; rfl)
  continuous_invFun :=
    RamificationTheory.Field.absoluteGaloisGroup.semilinear_conjugation_continuous
      e.symm E.symm (semilinear_symm_algebraMap e E hE)
      (semilinearGaloisEquiv e.symm E.symm
        (semilinear_symm_algebraMap e E hE)).toMonoidHom (by intro σ; rfl)


/-- Compatible field equivalences take the fixed field to the fixed field of
its actual conjugated subgroup, using the original image subfield. -/
theorem intermediateFieldMapRingEquiv_fixedField
    {K : Type u} {Ω : Type w} {M : Type v} {Ψ : Type z}
    [Field K] [Field Ω] [Field M] [Field Ψ] [Algebra K Ω] [Algebra M Ψ]
    (e : K ≃+* M) (c : Ω ≃+* Ψ)
    (hc : ∀ a : K, c (algebraMap K Ω a) = algebraMap M Ψ (e a))
    (S : Subgroup Gal(Ω/K)) :
    intermediateFieldMapRingEquiv e c hc (IntermediateField.fixedField S) =
      IntermediateField.fixedField
        (S.map (semilinearGaloisEquiv e c hc).toMonoidHom) := by
  ext y
  change (∃ z, z ∈ IntermediateField.fixedField S ∧ c z = y) ↔ _
  constructor
  · rintro ⟨z, hz, rfl⟩
    apply (IntermediateField.mem_fixedField_iff _ _).mpr
    rintro σ ⟨τ, hτ, rfl⟩
    change c (τ (c.symm (c z))) = c z
    rw [c.symm_apply_apply, (IntermediateField.mem_fixedField_iff S z).mp hz τ hτ]
  · intro hy
    refine ⟨c.symm y, ?_, c.apply_symm_apply y⟩
    apply (IntermediateField.mem_fixedField_iff _ _).mpr
    intro σ hσ
    apply c.injective
    have h := (IntermediateField.mem_fixedField_iff _ y).mp hy
      (semilinearGaloisEquiv e c hc σ)
      (Subgroup.mem_map_of_mem (semilinearGaloisEquiv e c hc).toMonoidHom hσ)
    change c (σ (c.symm y)) = y at h
    exact h.trans (c.apply_symm_apply y).symm


/-- Changing the compatible ambient-field equivalence changes conjugation by
an inner automorphism, which disappears in topological abelianization. -/
theorem semilinearGaloisAbelianizationEquiv_independent
    (e : K ≃+* M) (E F : Ω ≃+* Ψ)
    (hE : ∀ x : K, E (algebraMap K Ω x) = algebraMap M Ψ (e x))
    (hF : ∀ x : K, F (algebraMap K Ω x) = algebraMap M Ψ (e x)) :
    ProCGroups.Abelian.TopologicalAbelianization.congr
        (semilinearGaloisContinuousEquiv e E hE) =
      ProCGroups.Abelian.TopologicalAbelianization.congr
        (semilinearGaloisContinuousEquiv e F hF) := by
  let δ : Gal(Ψ/M) :=
    { toRingEquiv := E.symm.trans F
      commutes' := by
        intro x
        change F (E.symm (algebraMap M Ψ x)) = algebraMap M Ψ x
        rw [semilinear_symm_algebraMap e E hE x, hF, e.apply_symm_apply] }
  have hconj (σ : Gal(Ω/K)) :
      semilinearGaloisContinuousEquiv e F hF σ =
        δ * semilinearGaloisContinuousEquiv e E hE σ * δ⁻¹ := by
    apply AlgEquiv.ext
    intro x
    change F (σ (F.symm x)) =
      F (E.symm (E (σ (E.symm (E (F.symm x))))))
    rw [E.symm_apply_apply, E.symm_apply_apply]
  apply ContinuousMulEquiv.ext
  intro q
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk'_surjective
    (commutator Gal(Ω/K)).topologicalClosure q
  let π : Gal(Ψ/M) →* TopologicalAbelianization Gal(Ψ/M) :=
    QuotientGroup.mk' (commutator Gal(Ψ/M)).topologicalClosure
  change π (semilinearGaloisContinuousEquiv e E hE σ) =
    π (semilinearGaloisContinuousEquiv e F hF σ)
  rw [hconj, map_mul, map_mul, map_inv]
  rw [mul_comm (π δ) (π (semilinearGaloisContinuousEquiv e E hE σ)),
    mul_assoc, mul_inv_cancel, mul_one]

/-- A field equivalence identifies the Krull topological absolute Galois groups
of its source and target fields. -/
noncomputable def absoluteGaloisGroupEquivOfRingEquiv (e : K ≃+* M) :
    Field.absoluteGaloisGroup K ≃ₜ* Field.absoluteGaloisGroup M :=
  semilinearGaloisContinuousEquiv e
    (IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure M) e)
    (IsAlgClosure.equivOfEquiv_algebraMap
      (AlgebraicClosure K) (AlgebraicClosure M) e)

/-- The induced equivalence of Mathlib's topological abelianizations. -/
noncomputable def absoluteGaloisGroupAbelianizationEquivOfRingEquiv
    (e : K ≃+* M) :
    Field.absoluteGaloisGroupAbelianization K ≃ₜ*
      Field.absoluteGaloisGroupAbelianization M :=
  ProCGroups.Abelian.TopologicalAbelianization.congr
    (absoluteGaloisGroupEquivOfRingEquiv e)

end ClassFieldTheory

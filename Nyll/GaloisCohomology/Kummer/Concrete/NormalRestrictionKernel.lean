/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.NormalRestrictionKernelFinite
import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugation
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The actual normal-restriction kernel

The kernel of restriction from Gal(Ω/K) to Gal(M/K) is Gal(Ω/M), with the
same underlying field automorphisms. For finite M/K and Galois Ω/K this is
a continuous equivalence. Actual subgroup conjugation becomes semilinear
conjugation by the same ambient automorphism.
-/

namespace KummerTheory

open scoped Topology

universe u

variable {K : Type u} (M : Type u) (Ω : Type u)
  [Field K] [Field M] [Field Ω]
  [Algebra K M] [Algebra K Ω] [Algebra M Ω] [IsScalarTower K M Ω]
  [Normal K M]

/-- Reinterpret an automorphism in the restriction kernel as an M-linear
automorphism, and restrict scalars for the inverse. -/
def normalRestrictionKernelEquiv :
    (AlgEquiv.restrictNormalHom M : Gal(Ω/K) →* Gal(M/K)).ker ≃* Gal(Ω/M) where
  toFun σ :=
    { σ.val.toRingEquiv with
      commutes' := fun m => by
        change σ.val (algebraMap M Ω m) = algebraMap M Ω m
        rw [← σ.val.restrictNormal_commutes M m]
        have hσ : σ.val.restrictNormal M = 1 := σ.property
        rw [hσ]
        rfl }
  invFun σ := ⟨σ.restrictScalars K, by
    apply AlgEquiv.ext
    intro m
    apply (algebraMap M Ω).injective
    change algebraMap M Ω ((σ.restrictScalars K).restrictNormal M m) = algebraMap M Ω m
    rw [AlgEquiv.restrictNormal_commutes]
    exact σ.commutes m⟩
  left_inv σ := by
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    rfl
  right_inv σ := by
    apply AlgEquiv.ext
    intro x
    rfl
  map_mul' σ τ := by
    apply AlgEquiv.ext
    intro x
    rfl

/-- Forward reinterpretation leaves ambient evaluation unchanged. -/
@[simp] theorem normalRestrictionKernelEquiv_apply
    (σ : (AlgEquiv.restrictNormalHom M : Gal(Ω/K) →* Gal(M/K)).ker) (x : Ω) :
    normalRestrictionKernelEquiv M Ω σ x = (σ : Gal(Ω/K)) x := rfl

/-- The inverse is actual restriction of scalars. -/
@[simp] theorem normalRestrictionKernelEquiv_symm_apply (σ : Gal(Ω/M)) :
    ((normalRestrictionKernelEquiv (K := K) M Ω).symm σ : Gal(Ω/K)) =
      σ.restrictScalars K := rfl

/-- An ambient automorphism is semilinear over its actual restriction to M. -/
theorem normalRestriction_algebraMap (g : Gal(Ω/K)) (m : M) :
    g.toRingEquiv (algebraMap M Ω m) =
      algebraMap M Ω ((g.restrictNormal M).toRingEquiv m) :=
  (g.restrictNormal_commutes M m).symm

/-- Kernel conjugation and semilinear conjugation use the same representative. -/
theorem normalRestrictionKernelEquiv_conjNormal (g : Gal(Ω/K))
    (σ : (AlgEquiv.restrictNormalHom M : Gal(Ω/K) →* Gal(M/K)).ker) :
    normalRestrictionKernelEquiv M Ω (MulAut.conjNormal g σ) =
      semilinearGaloisConjugate (g.restrictNormal M).toRingEquiv g.toRingEquiv
        (normalRestriction_algebraMap M Ω g) (normalRestrictionKernelEquiv M Ω σ) := by
  apply AlgEquiv.ext
  intro x
  rw [normalRestrictionKernelEquiv_apply, semilinearGaloisConjugate_apply,
    normalRestrictionKernelEquiv_apply]
  change (g * (σ : Gal(Ω/K)) * g⁻¹) x = g ((σ : Gal(Ω/K)) (g.symm x))
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.coe_inv]

variable [FiniteDimensional K M]

-- The finite intermediate field E adds only its canonical scalar restrictions.
-- The K/M/Ω field-algebra tower is fixed once; no alternate module is installed.
private theorem normalRestrictionKernelEquiv_continuous :
    Continuous (normalRestrictionKernelEquiv (K := K) M Ω) := by
  apply continuous_of_tendsto_nhds_one (normalRestrictionKernelEquiv M Ω)
  rw [Filter.tendsto_def]
  intro U hU
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff M Ω U).mp hU
  have : FiniteDimensional K (E.restrictScalars K) := FiniteDimensional.trans K M E
  have hO : IsOpen ((Subtype.val :
      (AlgEquiv.restrictNormalHom M : Gal(Ω/K) →* Gal(M/K)).ker → Gal(Ω/K)) ⁻¹'
      ((E.restrictScalars K).fixingSubgroup : Set Gal(Ω/K))) :=
    (E.restrictScalars K).fixingSubgroup_isOpen.preimage continuous_subtype_val
  apply Filter.mem_of_superset
    (hO.mem_nhds (Subgroup.one_mem (E.restrictScalars K).fixingSubgroup))
  intro σ hσ
  apply hEU
  apply (IntermediateField.mem_fixingSubgroup_iff E
    (normalRestrictionKernelEquiv M Ω σ)).mpr
  intro x hx
  rw [normalRestrictionKernelEquiv_apply]
  exact (IntermediateField.mem_fixingSubgroup_iff (E.restrictScalars K) σ.val).mp hσ x hx

variable [IsGalois K Ω]

/-- The actual restriction-kernel identification is a homeomorphism for
the subgroup and Krull topologies. -/
def normalRestrictionKernelContinuousEquiv :
    (AlgEquiv.restrictNormalHom M : Gal(Ω/K) →* Gal(M/K)).ker ≃ₜ* Gal(Ω/M) := by
  have hclosed : IsClosed
      ((AlgEquiv.restrictNormalHom M : Gal(Ω/K) →* Gal(M/K)).ker : Set Gal(Ω/K)) :=
    (show OpenSubgroup Gal(Ω/K) from
      ⟨(AlgEquiv.restrictNormalHom M : Gal(Ω/K) →* Gal(M/K)).ker,
        normalRestrictionKernel_isOpen (K := K) (M := M) (Ω := Ω)⟩).isClosed
  have : CompactSpace (AlgEquiv.restrictNormalHom M : Gal(Ω/K) →* Gal(M/K)).ker :=
    hclosed.isClosedEmbedding_subtypeVal.compactSpace
  have : Algebra.IsAlgebraic M Ω := Algebra.IsAlgebraic.tower_top (K := K) M
  exact
    { normalRestrictionKernelEquiv M Ω with
      continuous_toFun := normalRestrictionKernelEquiv_continuous M Ω
      continuous_invFun :=
        (normalRestrictionKernelEquiv_continuous
          (K := K) M Ω).continuous_symm_of_equiv_compact_to_t2 }

/-- Evaluation of the continuous equivalence preserves the representative. -/
@[simp] theorem normalRestrictionKernelContinuousEquiv_apply
    (σ : (AlgEquiv.restrictNormalHom M : Gal(Ω/K) →* Gal(M/K)).ker) (x : Ω) :
    normalRestrictionKernelContinuousEquiv M Ω σ x = (σ : Gal(Ω/K)) x := rfl

/-- The inverse continuous equivalence restricts scalars on the representative. -/
@[simp] theorem normalRestrictionKernelContinuousEquiv_symm_apply (σ : Gal(Ω/M)) :
    ((normalRestrictionKernelContinuousEquiv (K := K) M Ω).symm σ : Gal(Ω/K)) =
      σ.restrictScalars K := rfl

/-- Continuous kernel transport intertwines actual conjugation with
semilinear conjugation by the same ambient lift. -/
theorem normalRestrictionKernelContinuousEquiv_conjNormal (g : Gal(Ω/K))
    (σ : (AlgEquiv.restrictNormalHom M : Gal(Ω/K) →* Gal(M/K)).ker) :
    normalRestrictionKernelContinuousEquiv M Ω (MulAut.conjNormal g σ) =
      semilinearGaloisConjugate (g.restrictNormal M).toRingEquiv g.toRingEquiv
        (normalRestriction_algebraMap M Ω g)
        (normalRestrictionKernelContinuousEquiv M Ω σ) :=
  normalRestrictionKernelEquiv_conjNormal M Ω g σ

end KummerTheory

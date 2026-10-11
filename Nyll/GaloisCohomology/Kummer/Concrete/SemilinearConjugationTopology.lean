/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.KrullTopology
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugation

/-!
# Continuity of semilinear Galois conjugation

The inverse images of a basis of a finite intermediate field generate a finite
intermediate field. Its fixing subgroup maps into the original fixing subgroup
under semilinear conjugation. This proves continuity for the Krull topology
without putting a topology on the extension field.
-/

namespace KummerTheory

open scoped Topology

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
  [Algebra.IsAlgebraic K Ω]

/-- Semilinear conjugation is continuous for the Krull topology. -/
theorem semilinearGaloisConjugateEquiv_continuous (τ : K ≃+* K) (e : Ω ≃+* Ω)
    (he : ∀ k : K, e (algebraMap K Ω k) = algebraMap K Ω (τ k)) :
    Continuous (semilinearGaloisConjugateEquiv τ e he) := by
  apply continuous_of_tendsto_nhds_one (semilinearGaloisConjugateEquiv τ e he)
  rw [Filter.tendsto_def]
  intro U hU
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff K Ω U).mp hU
  let b : Module.Basis (Fin (Module.finrank K E)) K E := Module.finBasis K E
  let S : Set Ω := Set.range (fun i : Fin (Module.finrank K E) => e.symm (b i : Ω))
  let F : IntermediateField K Ω := IntermediateField.adjoin K S
  have hF : FiniteDimensional K F :=
    IntermediateField.finiteDimensional_adjoin
      (fun (x : Ω) (_hx : x ∈ S) => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  apply (krullTopology_mem_nhds_one_iff K Ω
    ((semilinearGaloisConjugateEquiv τ e he) ⁻¹' U)).mpr
  refine ⟨F, hF, ?_⟩
  intro σ hσ
  apply hEU
  apply (IntermediateField.mem_fixingSubgroup_iff E
    (semilinearGaloisConjugateEquiv τ e he σ)).mpr
  have hb : ((semilinearGaloisConjugateEquiv τ e he σ).toAlgHom.comp E.val).toLinearMap =
      E.val.toLinearMap := by
    apply b.ext
    intro i
    change semilinearGaloisConjugateEquiv τ e he σ (b i : Ω) = (b i : Ω)
    rw [semilinearGaloisConjugateEquiv_apply, semilinearGaloisConjugate_apply]
    have hfix : σ (e.symm (b i : Ω)) = e.symm (b i : Ω) :=
      (IntermediateField.mem_fixingSubgroup_iff F σ).mp hσ (e.symm (b i : Ω))
        (IntermediateField.subset_adjoin K S ⟨i, rfl⟩)
    rw [hfix, e.apply_symm_apply]
  intro x hx
  exact DFunLike.congr_fun hb (⟨x, hx⟩ : E)

/-- Semilinear conjugation is a continuous automorphism of the relative
Galois group, including continuity of its inverse. -/
def semilinearGaloisConjugateContinuousEquiv (τ : K ≃+* K) (e : Ω ≃+* Ω)
    (he : ∀ k : K, e (algebraMap K Ω k) = algebraMap K Ω (τ k)) :
    Gal(Ω/K) ≃ₜ* Gal(Ω/K) where
  toMulEquiv := semilinearGaloisConjugateEquiv τ e he
  continuous_toFun := semilinearGaloisConjugateEquiv_continuous τ e he
  continuous_invFun := semilinearGaloisConjugateEquiv_continuous τ.symm e.symm
    (semilinear_symm_algebraMap τ e he)

/-- The continuous conjugation evaluates by the constructed algebraic
conjugation. -/
theorem semilinearGaloisConjugateContinuousEquiv_apply (τ : K ≃+* K) (e : Ω ≃+* Ω)
    (he : ∀ k : K, e (algebraMap K Ω k) = algebraMap K Ω (τ k))
    (σ : Gal(Ω/K)) :
    semilinearGaloisConjugateContinuousEquiv τ e he σ =
      semilinearGaloisConjugate τ e he σ := by
  rfl

end KummerTheory

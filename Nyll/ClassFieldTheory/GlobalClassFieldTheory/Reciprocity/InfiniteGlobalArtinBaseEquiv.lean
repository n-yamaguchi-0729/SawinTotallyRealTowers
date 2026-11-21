/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalArtinBaseEquiv
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfiniteGlobalArtinDescent
public import Nyll.ClassFieldTheory.Algebra.IntermediateFieldRingEquivOrderIso
public import Nyll.ClassFieldTheory.Algebra.AbelianGaloisEquiv

/-!
# Naturality of infinite global Artin maps

Finite layers are transported by the specified ambient field equivalence.
Their finite Artin values determine the infinite Artin action on every element.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory.Reciprocity

universe u v w x

variable {K : Type u} {Ω : Type v} {M : Type w} {Ψ : Type x}
  [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
  [Field M] [NumberField M] [Field Ψ] [Algebra M Ψ] [IsAbelianGalois M Ψ]

/-- The descended infinite map retains the actual finite projection on each
idèle class, with the specified finite intermediate field unchanged. -/
theorem infiniteGlobalIdeleClassArtinMonoidHom_finiteProjection
    (a : IdeleClassGroup K) (E : FiniteGaloisIntermediateField K Ω) :
    let : NumberField E := NumberField.of_module_finite K E
    AlgEquiv.restrictNormalHom E
        (infiniteGlobalIdeleClassArtinMonoidHom (K := K) (Ω := Ω) a) =
      globalNormResidueMonoidHom K E a := by
  intro numberFieldE
  obtain ⟨b, rfl⟩ := IdeleGroup.toStandardClass_surjective K a
  rw [infiniteGlobalIdeleClassArtinMonoidHom_mk,
    globalNormResidueMonoidHom_mk]
  exact restrictNormalHom_infiniteGlobalArtinMonoidHom K Ω b E

/-- Compatible base and ambient equivalences intertwine the actual infinite
Artin maps. Finite pointwise reciprocity supplies the equality on each element. -/
theorem infiniteGlobalIdeleClassArtinMonoidHom_semilinear
    (e : K ≃ₐ[ℚ] M) (c : Ω ≃+* Ψ)
    (hc : ∀ t : K, c (algebraMap K Ω t) = algebraMap M Ψ (e t))
    (a : IdeleClassGroup K) :
    ClassFieldTheory.semilinearGaloisEquiv e.toRingEquiv c hc
        (infiniteGlobalIdeleClassArtinMonoidHom (K := K) (Ω := Ω) a) =
      infiniteGlobalIdeleClassArtinMonoidHom (K := M) (Ω := Ψ)
        (ideleClassCongr e a) := by
  let σ := infiniteGlobalIdeleClassArtinMonoidHom (K := K) (Ω := Ω) a
  let τ := infiniteGlobalIdeleClassArtinMonoidHom (K := M) (Ω := Ψ)
    (ideleClassCongr e a)
  apply AlgEquiv.ext
  intro y
  obtain ⟨z, rfl⟩ := c.surjective y
  change c (σ (c.symm (c z))) = τ (c z)
  rw [c.symm_apply_apply]
  let E : FiniteGaloisIntermediateField K Ω :=
    FiniteGaloisIntermediateField.adjoin K {z}
  have hz : z ∈ E.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin K {z} (Set.mem_singleton z)
  let zE : E := ⟨z, hz⟩
  let F₀ := ClassFieldTheory.intermediateFieldMapRingEquiv
    e.toRingEquiv c hc E.toIntermediateField
  let r₀ : E ≃+* F₀ := ClassFieldTheory.intermediateFieldMapRingEquivEquiv
    e.toRingEquiv c hc E.toIntermediateField
  have hbase : (algebraMap M F₀).comp e.toRingHom =
      r₀.toRingHom.comp (algebraMap K E) :=
    ClassFieldTheory.intermediateFieldMapRingEquivEquiv_commutes
      e.toRingEquiv c hc E.toIntermediateField
  let : FiniteDimensional M F₀ := Module.Finite.of_equiv_equiv e.toRingEquiv r₀ hbase
  let : IsAbelianGalois K E := IsAbelianGalois.of_algHom E.toIntermediateField.val
  let : IsAbelianGalois M F₀ :=
    ClassFieldTheory.isAbelianGalois_of_equiv_equiv e.toRingEquiv r₀ hbase
  let F : FiniteGaloisIntermediateField M Ψ :=
    { toIntermediateField := F₀
      finiteDimensional := inferInstance
      isGalois := inferInstance }
  let r : E ≃+* F := r₀
  let : NumberField E := NumberField.of_module_finite K E
  let : NumberField F := NumberField.of_module_finite M F
  have hfiniteBase (t : K) : r (algebraMap K E t) = algebraMap M F (e t) :=
    (congrArg (fun f : K →+* F₀ => f t) hbase).symm
  have hfinite := globalIdeleClassArtinMonoidHom_semilinear
    e r.toRatAlgEquiv hfiniteBase a
  have hvalue := congrArg (fun g : Gal(F/M) => (g (r zE) : Ψ)) hfinite
  change c ((globalNormResidueMonoidHom K E a)
      (r.symm (r zE)) : Ω) =
    (globalNormResidueMonoidHom M F
      (ideleClassCongr e a) (r zE) : Ψ) at hvalue
  rw [r.symm_apply_apply] at hvalue
  rw [← infiniteGlobalIdeleClassArtinMonoidHom_finiteProjection a E,
    ← infiniteGlobalIdeleClassArtinMonoidHom_finiteProjection (ideleClassCongr e a) F]
    at hvalue
  have hsource := AlgEquiv.restrictNormal_commutes σ E zE
  have htarget := AlgEquiv.restrictNormal_commutes τ F (r zE)
  change (AlgEquiv.restrictNormalHom E σ zE : Ω) = σ z at hsource
  change (AlgEquiv.restrictNormalHom F τ (r zE) : Ψ) = τ (c z) at htarget
  exact (congrArg c hsource).symm.trans (hvalue.trans htarget)

end GlobalClassFieldTheory.Reciprocity

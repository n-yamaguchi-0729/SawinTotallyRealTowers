import GaloisCohomology.Kummer.Concrete.ContinuousCharacters
import GaloisCohomology.Kummer.Concrete.FiniteGeneration
import GaloisCohomology.Kummer.Concrete.InfiniteContinuity

set_option autoImplicit false

/-!
# Infinite Kummer character equivalence

Continuous characters of an infinite Galois group factor through finite
Galois stages.  Finite Kummer surjectivity at such a stage then supplies a
radical representative in the ambient extension.
-/

noncomputable section

namespace KummerTheory

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

private theorem primitiveRoots_intermediate_nonempty
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (E : IntermediateField K Ω) :
    (primitiveRoots (n : ℕ) E).Nonempty := by
  obtain ⟨ζ, hζ⟩ := hmu
  refine ⟨algebraMap K E ζ, (mem_primitiveRoots n.pos).2 ?_⟩
  exact ((mem_primitiveRoots n.pos).1 hζ).map_of_injective
    (algebraMap K E).injective

private def intermediateNthRootsEquiv
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (E : IntermediateField K Ω) :
    nthRootsSubgroup E (n : ℕ) ≃* nthRootsSubgroup Ω (n : ℕ) :=
  rootsOfUnityEquivOfPrimitiveRoots (algebraMap E Ω).injective
    (primitiveRoots_intermediate_nonempty n hmu E)

private theorem intermediateNthRootsEquiv_apply_val
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (E : IntermediateField K Ω) (u : nthRootsSubgroup E (n : ℕ)) :
    ((intermediateNthRootsEquiv n hmu E u : nthRootsSubgroup Ω (n : ℕ)) : Ωˣ) =
      Units.map (algebraMap E Ω).toMonoidHom (u : Eˣ) := by
  apply Units.ext
  exact (val_rootsOfUnityEquivOfPrimitiveRoots_apply_coe
    (algebraMap E Ω).injective (primitiveRoots_intermediate_nonempty n hmu E) u).symm

private theorem rootQuotient_map_intermediate
    (E : IntermediateField K Ω) [Normal K E]
    (β : Eˣ) (σ : Gal(Ω/K)) :
    rootQuotient (K := K) (L := Ω)
        (Units.map (algebraMap E Ω).toMonoidHom β) σ =
      Units.map (algebraMap E Ω).toMonoidHom
        (rootQuotient (K := K) (L := E) β
          (AlgEquiv.restrictNormalHom E σ)) := by
  apply Units.ext
  simp only [rootQuotient, Units.val_div_eq_div_val, Units.coe_map]
  change σ (algebraMap E Ω (β : E)) / algebraMap E Ω (β : E) =
    algebraMap E Ω
      ((AlgEquiv.restrictNormalHom E σ) (β : E) / (β : E))
  rw [map_div₀]
  exact congrArg (fun x : Ω => x / algebraMap E Ω (β : E))
    (AlgEquiv.restrictNormal_commutes σ E (β : E)).symm

private def finiteRadicalToAmbient
    (n : ℕ+) (E : IntermediateField K Ω)
    (a : (chosenFiniteKummerRadicalDatum (K := K) (L := E) n).carrier) :
    (chosenFiniteKummerRadicalDatum (K := K) (L := Ω) n).carrier := by
  let DE := chosenFiniteKummerRadicalDatum (K := K) (L := E) n
  let βΩ : Ωˣ := Units.map (algebraMap E Ω).toMonoidHom (DE.root a)
  refine ⟨a.1, βΩ, ?_⟩
  rw [← map_pow, DE.root_pow_eq_map]
  apply Units.ext
  exact IsScalarTower.algebraMap_apply K E Ω (a.1 : K)

private theorem finiteRadicalToAmbient_mapped_root_pow
    (n : ℕ+) (E : IntermediateField K Ω)
    (a : (chosenFiniteKummerRadicalDatum (K := K) (L := E) n).carrier) :
    (Units.map (algebraMap E Ω).toMonoidHom
        ((chosenFiniteKummerRadicalDatum (K := K) (L := E) n).root a)) ^ (n : ℕ) =
      Units.map (algebraMap K Ω).toMonoidHom
        (finiteRadicalToAmbient n E a).1 := by
  let DE := chosenFiniteKummerRadicalDatum (K := K) (L := E) n
  rw [← map_pow, DE.root_pow_eq_map]
  apply Units.ext
  exact IsScalarTower.algebraMap_apply K E Ω (a.1 : K)

variable [IsGalois K Ω]

/-- Every continuous `μₙ(Ω)`-valued character is represented by a radical
class when a primitive `n`-th root of unity lies in the base field. -/
theorem infiniteKummerContinuousQuotientCharacter_surjective_of_primitiveRoots
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Function.Surjective
      (infiniteKummerContinuousQuotientCharacter n
        (nthRootsOfUnityInBase_of_primitiveRoots (K := K) (L := Ω) n hmu)) := by
  let hbaseΩ : NthRootsOfUnityInBase (K := K) (L := Ω) n :=
    nthRootsOfUnityInBase_of_primitiveRoots (K := K) (L := Ω) n hmu
  let DΩ := chosenFiniteKummerRadicalDatum (K := K) (L := Ω) n
  intro χ
  obtain ⟨E, χEΩ, hfactor⟩ :=
    continuousCharacter_factors_through_finiteGalois χ
  let DE := chosenFiniteKummerRadicalDatum (K := K) (L := E) n
  let hbaseE : NthRootsOfUnityInBase (K := K) (L := E) n :=
    nthRootsOfUnityInBase_of_primitiveRoots (K := K) (L := E) n hmu
  let hfixedE := nthRootsOfUnity_fixed (K := K) (L := E) n hbaseE
  let eμ : nthRootsSubgroup E (n : ℕ) ≃* nthRootsSubgroup Ω (n : ℕ) :=
    intermediateNthRootsEquiv n hmu E.toIntermediateField
  let χE : Gal(E/K) →* nthRootsSubgroup E (n : ℕ) :=
    eμ.symm.toMonoidHom.comp χEΩ
  obtain ⟨qE, hqE⟩ :=
    finiteKummerQuotientCharacter_surjective (K := K) (L := E) n hbaseE χE
  obtain ⟨a, rfl⟩ := DE.radicalQuotientMk_surjective qE
  let aΩ : DΩ.carrier := finiteRadicalToAmbient n E.toIntermediateField a
  refine ⟨DΩ.radicalQuotientMk aΩ, ?_⟩
  apply ContinuousMonoidHom.ext
  intro σ
  apply Subtype.ext
  let τ : Gal(E/K) := AlgEquiv.restrictNormalHom E σ
  have hfinite : DE.rootCharacterToMuWithoutSection a hfixedE = χE := by
    change
      DE.quotientKummerCharacterWithoutSection hfixedE
          (DE.radicalQuotientMk a) = χE at hqE
    rw [DE.quotientKummerCharacterWithoutSection_mk] at hqE
    change DE.kummerCharacterWithoutSection hfixedE a = χE
    exact hqE
  have hfinite_at : DE.rootCharacterToMuWithoutSection a hfixedE τ = χE τ :=
    congrArg (fun ψ : Gal(E/K) →* nthRootsSubgroup E (n : ℕ) => ψ τ) hfinite
  have htransport : eμ (DE.rootCharacterToMuWithoutSection a hfixedE τ) = χEΩ τ := by
    rw [hfinite_at]
    change eμ (eμ.symm (χEΩ τ)) = χEΩ τ
    exact eμ.apply_symm_apply (χEΩ τ)
  have hfactor_at : χEΩ τ = χ σ := by
    exact congrArg
      (fun ψ : Gal(Ω/K) →* DiscreteNthRootsSubgroup Ω (n : ℕ) => ψ σ) hfactor
  change DΩ.rootCharacter aΩ
      (nthRootsOfUnity_fixed (K := K) (L := Ω) n hbaseΩ) σ = (χ σ : Ωˣ)
  rw [← DΩ.rootCharacter_eq_of_same_pow
    (nthRootsOfUnity_fixed (K := K) (L := Ω) n hbaseΩ) aΩ
      (finiteRadicalToAmbient_mapped_root_pow n E.toIntermediateField a) σ]
  rw [rootQuotient_map_intermediate E.toIntermediateField
    ((chosenFiniteKummerRadicalDatum (K := K) (L := E) n).root a) σ]
  change Units.map (algebraMap E.toIntermediateField Ω).toMonoidHom
      ((DE.rootCharacterToMuWithoutSection a hfixedE τ :
        nthRootsSubgroup E (n : ℕ)) : Eˣ) = (χ σ : Ωˣ)
  rw [← intermediateNthRootsEquiv_apply_val n hmu E.toIntermediateField
    (DE.rootCharacterToMuWithoutSection a hfixedE τ)]
  exact congrArg (fun u : DiscreteNthRootsSubgroup Ω (n : ℕ) => (u : Ωˣ))
    (htransport.trans hfactor_at)

/-- Continuous Kummer characters of an infinite Galois extension are
multiplicatively equivalent to its radical quotient. -/
def infiniteKummerContinuousCharacterEquivOfPrimitiveRoots
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    (chosenFiniteKummerRadicalDatum (K := K) (L := Ω) n).RadicalQuotient ≃*
      (Gal(Ω/K) →ₜ* DiscreteNthRootsSubgroup Ω (n : ℕ)) :=
  MulEquiv.ofBijective
    (infiniteKummerContinuousQuotientCharacter n
      (nthRootsOfUnityInBase_of_primitiveRoots (K := K) (L := Ω) n hmu))
    ⟨infiniteKummerContinuousQuotientCharacter_injective n
        (nthRootsOfUnityInBase_of_primitiveRoots (K := K) (L := Ω) n hmu),
      infiniteKummerContinuousQuotientCharacter_surjective_of_primitiveRoots n hmu⟩

end KummerTheory

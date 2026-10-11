/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.GaloisCohomology.Topology.AbsoluteGaloisLiftComparison
import Nyll.GaloisCohomology.Topology.FiniteExtensionGalois
import Nyll.GaloisCohomology.Kummer.Concrete.PrimeToCyclotomicTower
import Nyll.GaloisCohomology.Kummer.Concrete.GaloisClosureTransport
import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteConjugation
import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugation
import Nyll.GaloisCohomology.ProP.PrimeToIndexCharacterExtension

/-!
# Restriction and extension of absolute Galois characters

Compute character restriction through compatible algebraic closures.
For a finite Galois extension, characters of modulus coprime to the degree
are detected by restriction, and invariant characters admit extensions.
-/

namespace KummerTheory

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

/-- A compatible equivalence of closures computes restriction on characters. -/
theorem character_map_algebraMap_eq
    {A : Type*} [CommGroup A] [TopologicalSpace A]
    (e : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure E)
    (χ : Gal(AlgebraicClosure K/K) →ₜ* A)
    (σ : Gal(AlgebraicClosure E/E)) :
    χ (Field.absoluteGaloisGroup.map (algebraMap K E) σ) =
      χ ((galoisClosureTransport e).symm (σ.restrictScalars K)) := by
  apply Field.absoluteGaloisGroup.character_map_apply_of_lift
    (algebraMap K E) e.toRingHom
  · intro x
    exact (e.commutes x).trans (IsScalarTower.algebraMap_apply K E (AlgebraicClosure E) x)
  · intro x
    change e (e.symm (σ (e x))) = σ (e x)
    exact e.apply_symm_apply _

/-- A finite Galois extension has degree equal to the index of scalar restriction. -/
theorem finiteExtensionGaloisOpenSubgroup_index
    (K E Ω : Type*) [Field K] [Field E] [Field Ω]
    [Algebra K E] [Algebra E Ω] [Algebra K Ω] [IsScalarTower K E Ω]
    [FiniteDimensional K E] [IsGalois K E] [IsAlgClosure E Ω] :
    (GaloisCohomology.finiteExtensionGaloisOpenSubgroup K E Ω).toSubgroup.index =
      Module.finrank K E := by
  have : Normal K Ω := (IsAlgClosure.ofAlgebraic K E Ω).normal
  change (AlgEquiv.restrictScalarsHom K : Gal(Ω/E) →* Gal(Ω/K)).range.index = _
  rw [restrictScalarsHom_range_eq_normalRestrictionKer K E Ω, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr
      (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := E) (E := Ω))]
  exact (Nat.card_congr (Subgroup.topEquiv :
    (⊤ : Subgroup Gal(E/K)) ≃* Gal(E/K)).toEquiv).trans
      (IsGalois.card_aut_eq_finrank K E)

/-- Prime-to-degree absolute characters are detected after finite Galois base extension. -/
theorem absoluteCharacterRestriction_injective_of_coprime_finrank
    [FiniteDimensional K E] [IsGalois K E]
    (n : ℕ) (hn : (Module.finrank K E).Coprime n) :
    Function.Injective (fun χ : Gal(AlgebraicClosure K/K) →ₜ* Multiplicative (ZMod n) =>
      (χ.comp (Field.absoluteGaloisGroup.map (algebraMap K E)) :
        Gal(AlgebraicClosure E/E) →ₜ* Multiplicative (ZMod n))) := by
  have : IsAlgClosure K (AlgebraicClosure E) := IsAlgClosure.ofAlgebraic K E _
  let e := IsAlgClosure.equiv K (AlgebraicClosure K) (AlgebraicClosure E)
  let c := galoisClosureTransport e
  let c' : Gal(AlgebraicClosure E/K) →ₜ* Gal(AlgebraicClosure K/K) :=
    ⟨c.symm.toMonoidHom, c.symm.continuous⟩
  let H := GaloisCohomology.finiteExtensionGaloisOpenSubgroup K E (AlgebraicClosure E)
  let d := GaloisCohomology.finiteExtensionGaloisOpenSubgroupEquiv K E (AlgebraicClosure E)
  have : H.toSubgroup.Normal := by
    change (AlgEquiv.restrictScalarsHom K :
      Gal(AlgebraicClosure E/E) →* Gal(AlgebraicClosure E/K)).range.Normal
    rw [restrictScalarsHom_range_eq_normalRestrictionKer K E (AlgebraicClosure E)]
    infer_instance
  have hindex : H.toSubgroup.index.Coprime n := by
    rw [finiteExtensionGaloisOpenSubgroup_index K E (AlgebraicClosure E)]
    exact hn
  intro φ ψ hres
  have h : (φ.comp c').toMonoidHom =
      (ψ.comp c').toMonoidHom := by
    apply ClassFieldTower.Cohomology.cyclicCharacterRestriction_injective_of_index_coprime
      H.toSubgroup n hindex
    apply MonoidHom.ext
    intro h
    obtain ⟨σ, rfl⟩ := d.surjective h
    change φ (c.symm (σ.restrictScalars K)) = ψ (c.symm (σ.restrictScalars K))
    exact (character_map_algebraMap_eq e φ σ).symm.trans
      ((DFunLike.congr_fun hres σ).trans (character_map_algebraMap_eq e ψ σ))
  apply ContinuousMonoidHom.ext
  intro σ
  have heq := DFunLike.congr_fun h (c σ)
  change φ (c.symm (c σ)) = ψ (c.symm (c σ)) at heq
  simpa only [c.symm_apply_apply] using heq

/-- An invariant cyclic character descends through a finite Galois extension
whose degree is coprime to its modulus. Restriction is mathlib's actual map. -/
theorem exists_absoluteCharacter_extension_of_coprime_finrank
    [FiniteDimensional K E] [IsGalois K E]
    (n : ℕ) (hn : (Module.finrank K E).Coprime n)
    (χ : Gal(AlgebraicClosure E/E) →ₜ* Multiplicative (ZMod n))
    (hinv : ∀ (δ : Gal(E/K)) (σ : Gal(AlgebraicClosure E/E)),
      χ (absoluteGaloisConjugate δ.toRingEquiv σ) = χ σ) :
    ∃ ψ : Gal(AlgebraicClosure K/K) →ₜ* Multiplicative (ZMod n),
      (ψ.comp (Field.absoluteGaloisGroup.map (algebraMap K E)) :
        Gal(AlgebraicClosure E/E) →ₜ* Multiplicative (ZMod n)) = χ := by
  have : IsAlgClosure K (AlgebraicClosure E) := IsAlgClosure.ofAlgebraic K E _
  let e := IsAlgClosure.equiv K (AlgebraicClosure K) (AlgebraicClosure E)
  let c := galoisClosureTransport e
  let H := GaloisCohomology.finiteExtensionGaloisOpenSubgroup K E (AlgebraicClosure E)
  let d := GaloisCohomology.finiteExtensionGaloisOpenSubgroupEquiv K E (AlgebraicClosure E)
  have : H.toSubgroup.Normal := by
    change (AlgEquiv.restrictScalarsHom K :
      Gal(AlgebraicClosure E/E) →* Gal(AlgebraicClosure E/K)).range.Normal
    rw [restrictScalarsHom_range_eq_normalRestrictionKer K E (AlgebraicClosure E)]
    infer_instance
  have hindex : H.toSubgroup.index = Module.finrank K E :=
    finiteExtensionGaloisOpenSubgroup_index K E (AlgebraicClosure E)
  have : H.toSubgroup.FiniteIndex := ⟨by
    rw [hindex]
    exact (Module.finrank_pos (R := K) (M := E)).ne'⟩
  let φ : H →ₜ* Multiplicative (ZMod n) :=
    χ.comp ⟨d.symm.toMonoidHom, d.symm.continuous⟩
  have hφ : ∀ (g : Gal(AlgebraicClosure E/K)) (h : H),
      φ (MulAut.conjNormal g h) = φ h := by
    intro g h
    let δ : Gal(E/K) := g.restrictNormal E
    have hg (x : E) : g (algebraMap E (AlgebraicClosure E) x) =
        algebraMap E (AlgebraicClosure E) (δ x) :=
      (g.restrictNormal_commutes E x).symm
    let σ : Gal(AlgebraicClosure E/E) := d.symm h
    have hσ : σ.restrictScalars K = (h : Gal(AlgebraicClosure E/K)) :=
      congrArg Subtype.val (d.apply_symm_apply h)
    have hconj : d.symm (MulAut.conjNormal g h) =
        semilinearGaloisConjugate δ.toRingEquiv g.toRingEquiv hg σ := by
      apply AlgEquiv.restrictScalars_injective K
      calc
        (d.symm (MulAut.conjNormal g h)).restrictScalars K =
            (MulAut.conjNormal g h : H) :=
          congrArg Subtype.val (d.apply_symm_apply (MulAut.conjNormal g h))
        _ = g * σ.restrictScalars K * g⁻¹ := by
          rw [hσ]
          rfl
        _ = (semilinearGaloisConjugate δ.toRingEquiv g.toRingEquiv hg σ).restrictScalars K := by
          apply AlgEquiv.ext
          intro x
          rfl
    change χ (d.symm (MulAut.conjNormal g h)) = χ σ
    rw [hconj]
    exact (map_semilinearGaloisConjugate_eq χ.toMonoidHom δ.toRingEquiv
      (IsAlgClosure.equivOfEquiv (AlgebraicClosure E) (AlgebraicClosure E) δ.toRingEquiv)
      g.toRingEquiv
      (IsAlgClosure.equivOfEquiv_algebraMap (AlgebraicClosure E)
        (AlgebraicClosure E) δ.toRingEquiv) hg σ).trans (hinv δ σ)
  let ψΩ := ClassFieldTower.Cohomology.primeToIndexCharacterExtension H n φ
  let ψ : Gal(AlgebraicClosure K/K) →ₜ* Multiplicative (ZMod n) :=
    ψΩ.comp ⟨c.toMonoidHom, c.continuous⟩
  refine ⟨ψ, ?_⟩
  apply ContinuousMonoidHom.ext
  intro σ
  change ψ (Field.absoluteGaloisGroup.map (algebraMap K E) σ) = χ σ
  calc
    ψ (Field.absoluteGaloisGroup.map (algebraMap K E) σ) =
        ψ (c.symm (σ.restrictScalars K)) := character_map_algebraMap_eq e ψ σ
    _ = ψΩ (σ.restrictScalars K) := congrArg ψΩ (c.apply_symm_apply _)
    _ = φ (d σ) :=
      ClassFieldTower.Cohomology.primeToIndexCharacterExtension_subtype H n
        (hindex.symm ▸ hn) φ hφ (d σ)
    _ = χ σ := congrArg χ (d.symm_apply_apply σ)

end KummerTheory

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.SeparableAbsoluteKummer
import Nyll.GaloisCohomology.Topology.SeparableGaloisMap

/-!
# Kummer characters under embeddings of arbitrary fields

The chosen map of algebraic closures restricts to the separable closures and
carries root quotients to root quotients. This gives the naturality of Kummer
characters under actual absolute Galois restriction, in every characteristic
prime to the exponent.
-/

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory Field.absoluteGaloisGroup ValuationTheory.Completion

variable {K L : Type*} [Field K] [Field L]

/-- If the source contains the roots of unity, embedding the source field
identifies the discrete groups of roots in the two separable closures. -/
noncomputable def separableNthRootsFieldMapEquiv (f : K →+* L) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    DiscreteNthRootsSubgroup (SeparableClosure K) (n : ℕ) ≃ₜ*
      DiscreteNthRootsSubgroup (SeparableClosure L) (n : ℕ) := by
  let : Algebra K L := f.toAlgebra
  exact
    { toMulEquiv := (nthRootsSubgroupEquivOfPrimitiveRoots K (SeparableClosure K) n hmu).symm.trans
        (nthRootsSubgroupEquivOfPrimitiveRoots K (SeparableClosure L) n hmu)
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

/-- The coefficient equivalence is induced by the chosen closure embedding. -/
theorem separableNthRootsFieldMapEquiv_coe (f : K →+* L) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (u : DiscreteNthRootsSubgroup (SeparableClosure K) (n : ℕ)) :
    (separableNthRootsFieldMapEquiv f n hmu u : (SeparableClosure L)ˣ) =
      Units.map (separableClosureLift f).toMonoidHom (u : (SeparableClosure K)ˣ) := by
  let : Algebra K L := f.toAlgebra
  obtain ⟨a, rfl⟩ := (nthRootsSubgroupEquivOfPrimitiveRoots K
    (SeparableClosure K) n hmu).surjective u
  change ((nthRootsSubgroupEquivOfPrimitiveRoots K (SeparableClosure L) n hmu)
    ((nthRootsSubgroupEquivOfPrimitiveRoots K (SeparableClosure K) n hmu).symm
      ((nthRootsSubgroupEquivOfPrimitiveRoots K (SeparableClosure K) n hmu) a)) :
      (SeparableClosure L)ˣ) = _
  rw [MulEquiv.symm_apply_apply]
  apply Units.ext
  change algebraMap K (SeparableClosure L) ((a : Kˣ) : K) =
    separableClosureLift f (algebraMap K (SeparableClosure K) ((a : Kˣ) : K))
  exact (separableClosureLift_algebraMap f ((a : Kˣ) : K)).symm

/-- The Kummer root quotient commutes with restriction along a field embedding. -/
theorem separableKummerCharacter_fieldMap
    (f : K →+* L) (n : ℕ+) [NeZero ((n : ℕ) : K)] [NeZero ((n : ℕ) : L)]
    (hmuK : (primitiveRoots (n : ℕ) K).Nonempty)
    (hmuL : (primitiveRoots (n : ℕ) L).Nonempty)
    (a : Kˣ) (σ : Gal(AlgebraicClosure L/L)) :
    Units.map (separableClosureLift f).toMonoidHom
      ((separableKummerContinuousNthRootsCharacterEquiv K n hmuK
        (a : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range)
        (separableClosureAutEquiv K (map f σ)) :
          DiscreteNthRootsSubgroup (SeparableClosure K) (n : ℕ)) :
          (SeparableClosure K)ˣ) =
      ((separableKummerContinuousNthRootsCharacterEquiv L n hmuL
        ((Units.map f.toMonoidHom a) : Lˣ ⧸ (powMonoidHom (n : ℕ) : Lˣ →* Lˣ).range)
        (separableClosureAutEquiv L σ) :
          DiscreteNthRootsSubgroup (SeparableClosure L) (n : ℕ)) :
          (SeparableClosure L)ˣ) := by
  have ha : a ∈ finiteKummerRadicalSubgroup (K := K) (L := SeparableClosure K) n := by
    rw [finiteKummerRadicalSubgroup_separableClosure_eq_top K n]
    exact Subgroup.mem_top a
  obtain ⟨β, hβ⟩ := ha
  let βL := Units.map (separableClosureLift f).toMonoidHom β
  have hβL : βL ^ (n : ℕ) =
      Units.map (algebraMap L (SeparableClosure L)).toMonoidHom
        (Units.map f.toMonoidHom a) := by
    apply Units.ext
    change (separableClosureLift f (β : SeparableClosure K)) ^ (n : ℕ) =
      algebraMap L (SeparableClosure L) (f (a : K))
    rw [← map_pow]
    have hb : (β : SeparableClosure K) ^ (n : ℕ) =
        algebraMap K (SeparableClosure K) (a : K) := congrArg Units.val hβ
    rw [hb, separableClosureLift_algebraMap]
  have hroot : Units.map (separableClosureLift f).toMonoidHom
      (rootQuotient (K := K) β (separableClosureAutEquiv K (map f σ))) =
      rootQuotient (K := L) βL (separableClosureAutEquiv L σ) := by
    apply Units.ext
    simp only [rootQuotient, AlgEquiv.smul_units_def, Units.val_div_eq_div_val, Units.coe_map]
    change separableClosureLift f
      (separableClosureAutEquiv K (map f σ) (β : SeparableClosure K) /
        (β : SeparableClosure K)) =
      separableClosureAutEquiv L σ (separableClosureLift f (β : SeparableClosure K)) /
        separableClosureLift f (β : SeparableClosure K)
    exact (map_div₀ (separableClosureLift f) _ _).trans
      (congrArg (fun z => z / separableClosureLift f (β : SeparableClosure K))
        (map_separableClosureLift f σ (β : SeparableClosure K)))
  exact (congrArg (Units.map (separableClosureLift f).toMonoidHom)
    (separableKummerContinuousNthRootsCharacterEquiv_apply_of_pow_eq K n hmuK a β hβ
      (separableClosureAutEquiv K (map f σ)))).trans (hroot.trans
        (separableKummerContinuousNthRootsCharacterEquiv_apply_of_pow_eq L n hmuL
          (Units.map f.toMonoidHom a) βL hβL (separableClosureAutEquiv L σ)).symm)

/-- Kummer characters are natural under the induced equivalence of root coefficients. -/
theorem separableKummerCharacter_fieldMap_equiv
    (f : K →+* L) (n : ℕ+) [NeZero ((n : ℕ) : K)] [NeZero ((n : ℕ) : L)]
    (hmuK : (primitiveRoots (n : ℕ) K).Nonempty)
    (hmuL : (primitiveRoots (n : ℕ) L).Nonempty)
    (a : Kˣ) (σ : Gal(AlgebraicClosure L/L)) :
    separableNthRootsFieldMapEquiv f n hmuK
      (separableKummerContinuousNthRootsCharacterEquiv K n hmuK
        (a : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range)
        (separableClosureAutEquiv K (map f σ))) =
      separableKummerContinuousNthRootsCharacterEquiv L n hmuL
        ((Units.map f.toMonoidHom a) : Lˣ ⧸ (powMonoidHom (n : ℕ) : Lˣ →* Lˣ).range)
        (separableClosureAutEquiv L σ) := by
  apply Subtype.ext
  exact (separableNthRootsFieldMapEquiv_coe f n hmuK _).trans
    (separableKummerCharacter_fieldMap f n hmuK hmuL a σ)

end ClassFieldTower.Martinet.Shafarevich

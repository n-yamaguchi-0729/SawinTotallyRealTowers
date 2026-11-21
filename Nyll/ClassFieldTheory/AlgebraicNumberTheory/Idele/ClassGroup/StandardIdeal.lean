/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.PrincipalFractionalIdeal
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.IdealMapCore
public import Mathlib.NumberTheory.NumberField.AdeleRing

/-!
# Principal ideals and ideal classes on the standard idele carrier

The standard diagonal has its actual principal fractional ideal. The ideal
class kernel and its quotient then follow from subgroup map/comap identities.
-/

@[expose] public section

open IsDedekindDomain
open scoped WithZero

noncomputable section

namespace NumberField.IdeleGroup

universe u v

variable {R : Type u} {K : Type v} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The standard diagonal maps to its principal fractional ideal. -/
theorem fractionalIdeal_unitEmbedding (x : Kˣ) :
    fractionalIdeal (unitEmbedding R K x) = toPrincipalIdeal R K x := by
  apply ClassFieldTheory.FractionalIdealFactorization.ext_count
  intro v
  rw [FractionalIdeal.count_toPrincipalIdeal]
  change FractionalIdeal.count K v
    (ClassFieldTheory.FractionalIdealFactorization.factorization (F := K)
      (FiniteAdeleRing.valuationVector (finitePart (unitEmbedding R K x)))).val =
      -WithZero.log (v.valuation K (x : K))
  rw [ClassFieldTheory.FractionalIdealFactorization.count_factorization,
    FiniteAdeleRing.valuationVector_apply]
  change -WithZero.log (Valued.v (algebraMap K (v.adicCompletion K) (x : K))) =
    -WithZero.log (v.valuation K (x : K))
  exact congrArg (fun z => -WithZero.log z) (v.valuedAdicCompletion_eq_valuation' (x : K))

/-- Principal standard ideles have trivial ordinary ideal class. -/
theorem idealClass_unitEmbedding (x : Kˣ) : idealClass (unitEmbedding R K x) = 1 := by
  change ClassGroup.mk K (fractionalIdeal (unitEmbedding R K x)) = 1
  rw [fractionalIdeal_unitEmbedding, ClassGroup.mk_eq_one_iff_mem_principal]
  exact ⟨x, rfl⟩

/-- The subgroup defining the ordinary ideal class quotient of standard ideles. -/
def ordinaryIdealClassSubgroup : Subgroup (IdeleGroup R K) :=
  integralAtFinitePlaces ⊔ principalSubgroup R K

/-- The ordinary ideal-class kernel is the supremum of integral and principal ideles. -/
theorem ordinaryIdealClassSubgroup_eq_ker :
    ordinaryIdealClassSubgroup (R := R) (K := K) = (idealClass (R := R) (K := K)).ker := by
  have hcomp : (fractionalIdeal (R := R) (K := K)).comp (unitEmbedding R K) =
      toPrincipalIdeal R K := by
    apply MonoidHom.ext
    intro x
    exact fractionalIdeal_unitEmbedding (R := R) (K := K) x
  have hmap : (principalSubgroup R K).map fractionalIdeal = (toPrincipalIdeal R K).range := by
    change (unitEmbedding R K).range.map fractionalIdeal = _
    rw [MonoidHom.map_range, hcomp]
  have hker : (idealClass (R := R) (K := K)).ker =
      (toPrincipalIdeal R K).range.comap fractionalIdeal := by
    ext a
    exact ClassGroup.mk_eq_one_iff_mem_principal (fractionalIdeal a)
  rw [hker, ← hmap, Subgroup.comap_map_eq, fractionalIdeal_ker]
  exact sup_comm (integralAtFinitePlaces (R := R) (K := K)) (principalSubgroup R K)

/-- The ordinary ideal class group as the standard integral-principal quotient. -/
def quotientIntegralSupPrincipalEquiv :
    IdeleGroup R K ⧸ (integralAtFinitePlaces ⊔ principalSubgroup R K) ≃* ClassGroup R :=
  (QuotientGroup.quotientMulEquivOfEq
    (ordinaryIdealClassSubgroup_eq_ker (R := R) (K := K))).trans
    (QuotientGroup.quotientKerEquivOfSurjective idealClass idealClass_surjective)

end NumberField.IdeleGroup

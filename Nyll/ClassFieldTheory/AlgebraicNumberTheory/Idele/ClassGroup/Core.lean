/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.PrincipalFractionalIdeal
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.StandardIdeal
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.IdealMap
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Principal
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.BaseChange

/-!
# The ordinary ideal class group as an idele quotient

This file proves that quotienting the idele group by the
ideles integral at every finite place and by the principal ideles gives the
ordinary ideal class group.
-/



@[expose] public section

open scoped NumberField RestrictedProduct WithZero
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace IdeleGroup

/-- The fractional ideal map sends a principal idele to the corresponding
principal fractional ideal. -/
@[simp]
theorem fractionalIdeal_principalIdele (x : Kˣ) :
    fractionalIdeal (principalIdele K x) =
      toPrincipalIdeal (𝓞 K) K x :=
  NumberField.IdeleGroup.fractionalIdeal_unitEmbedding x

@[simp]
theorem idealClass_principalIdele (x : Kˣ) :
    idealClass (principalIdele K x) = 1 := by
  change ClassGroup.mk K
      (fractionalIdeal (principalIdele K x)) = 1
  rw [fractionalIdeal_principalIdele,
    ClassGroup.mk_eq_one_iff_mem_principal]
  exact ⟨x, rfl⟩

/-- The subgroup `I_K^{S∞} Kˣ` defining the ordinary ideal class quotient. -/
def ordinaryIdealClassSubgroup : Subgroup (IdeleGroup K) :=
  integralAtFinitePlaces (K := K) ⊔ principalSubgroup K

/-- The kernel of the map from ideles to the ordinary ideal class group is
exactly `I_K^{S∞} Kˣ`. -/
theorem ordinaryIdealClassSubgroup_eq_ker :
    ordinaryIdealClassSubgroup (K := K) =
      (idealClass (K := K)).ker := by
  have hcomp : (fractionalIdeal (K := K)).comp (principalIdele K) =
      toPrincipalIdeal (𝓞 K) K := by
    apply MonoidHom.ext
    intro x
    exact fractionalIdeal_principalIdele x
  have hmap : (principalSubgroup K).map fractionalIdeal =
      (toPrincipalIdeal (𝓞 K) K).range := by
    change (principalIdele K).range.map fractionalIdeal = _
    rw [MonoidHom.map_range, hcomp]
  have hker : (idealClass (K := K)).ker =
      (toPrincipalIdeal (𝓞 K) K).range.comap fractionalIdeal := by
    ext a
    exact ClassGroup.mk_eq_one_iff_mem_principal (fractionalIdeal a)
  rw [hker, ← hmap, Subgroup.comap_map_eq, fractionalIdeal_ker]
  exact sup_comm (integralAtFinitePlaces (K := K)) (principalSubgroup K)

/-- The ordinary ideal class group is the quotient of
the ideles by the ideles integral at all finite places and the principal
ideles. -/
def quotientIntegralSupPrincipalEquiv :
    IdeleGroup K ⧸
        (integralAtFinitePlaces (K := K) ⊔ principalSubgroup K) ≃*
      ClassGroup (𝓞 K) :=
  (QuotientGroup.quotientMulEquivOfEq (ordinaryIdealClassSubgroup_eq_ker (K := K))).trans
    (quotientIdealClassKernelEquiv (K := K))

end IdeleGroup

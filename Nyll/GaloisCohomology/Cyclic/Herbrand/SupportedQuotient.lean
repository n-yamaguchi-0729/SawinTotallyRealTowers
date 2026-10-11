/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.EquivariantEquiv
import Nyll.GaloisCohomology.Cyclic.Herbrand.Permutation.Module
import Nyll.GaloisCohomology.GroupTheory.Quotient

/-!
# Cohomology of a class quotient represented by supported elements

Let `S` be a stable subgroup of a commutative `G`-group `A`, and let
`P` be another stable subgroup.  If `S ⊔ P = ⊤`, every class modulo `P`
has a representative in `S`.  This file upgrades the resulting second
isomorphism

`S / (S ∩ P) ≃ A / P`

to an equivariant equivalence and transports the two low-degree Tate groups
used in the Herbrand quotient calculation.
-/

noncomputable section

namespace CyclicCohomology

open CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uA

variable
    {G : Type uG} {A : Type uA}
    [Group G] [Fintype G]
    [CommGroup A] [MulDistribMulAction G A]

omit [Fintype G] in
/-- The intersection `S ∩ P`, expressed as `P.subgroupOf S`, is stable
for the restricted action on `S`. -/
theorem supportedPrincipalIntersection_stable
    (S P : Subgroup A)
    (hS : ∀ (g : G) (x : A), x ∈ S → g • x ∈ S)
    (hP : ∀ (g : G) (x : A), x ∈ P → g • x ∈ P)
    (g : G) (x : S)
    (hx : x ∈ P.subgroupOf S) :
    letI := stableSubgroupMulDistribMulAction S hS
    g • x ∈ P.subgroupOf S := by
  let := stableSubgroupMulDistribMulAction S hS
  change ((g • x : S) : A) ∈ P
  rw [stableSubgroup_smul_coe]
  exact hP g x hx

omit [Fintype G] in
/-- The second-isomorphism comparison between supported classes and all
classes is equivariant. -/
theorem subgroupQuotientEquivQuotientOfSupEqTop_smul
    (S P : Subgroup A)
    (hS : ∀ (g : G) (x : A), x ∈ S → g • x ∈ S)
    (hP : ∀ (g : G) (x : A), x ∈ P → g • x ∈ P)
    (hSP : S ⊔ P = ⊤)
    (g : G) (q : S ⧸ P.subgroupOf S) :
    letI := stableSubgroupMulDistribMulAction S hS
    letI := stableQuotientMulDistribMulAction
      (P.subgroupOf S)
      (supportedPrincipalIntersection_stable S P hS hP)
    letI := stableQuotientMulDistribMulAction P hP
    subgroupQuotientEquivQuotientOfSupEqTop S P hSP (g • q) =
      g • subgroupQuotientEquivQuotientOfSupEqTop S P hSP q := by
  let := stableSubgroupMulDistribMulAction S hS
  let := stableQuotientMulDistribMulAction
    (P.subgroupOf S)
    (supportedPrincipalIntersection_stable S P hS hP)
  let := stableQuotientMulDistribMulAction P hP
  refine QuotientGroup.induction_on q ?_
  intro s
  change
    QuotientGroup.mk' P ((g • s : S) : A) =
      QuotientGroup.mk' P (g • (s : A))
  rw [stableSubgroup_smul_coe]

/-- Degree-zero Tate cohomology of `A / P` can be computed using the
supported quotient `S / (S ∩ P)`. -/
noncomputable def supportedClassHerbrandH0Equiv
    (S P : Subgroup A)
    (hS : ∀ (g : G) (x : A), x ∈ S → g • x ∈ S)
    (hP : ∀ (g : G) (x : A), x ∈ P → g • x ∈ P)
    (hSP : S ⊔ P = ⊤) :
    letI := stableSubgroupMulDistribMulAction S hS
    letI := stableQuotientMulDistribMulAction
      (P.subgroupOf S)
      (supportedPrincipalIntersection_stable S P hS hP)
    letI := stableQuotientMulDistribMulAction P hP
    HerbrandH0 G (S ⧸ P.subgroupOf S) ≃*
      HerbrandH0 G (A ⧸ P) := by
  letI := stableSubgroupMulDistribMulAction S hS
  letI := stableQuotientMulDistribMulAction
    (P.subgroupOf S)
    (supportedPrincipalIntersection_stable S P hS hP)
  letI := stableQuotientMulDistribMulAction P hP
  exact
    herbrandH0EquivariantMulEquiv
      (subgroupQuotientEquivQuotientOfSupEqTop S P hSP)
      (subgroupQuotientEquivQuotientOfSupEqTop_smul
        S P hS hP hSP)

/-- Degree-minus-one Tate cohomology of `A / P` can be computed using
the supported quotient `S / (S ∩ P)`. -/
noncomputable def supportedClassHerbrandHMinusOneEquiv
    (S P : Subgroup A)
    (hS : ∀ (g : G) (x : A), x ∈ S → g • x ∈ S)
    (hP : ∀ (g : G) (x : A), x ∈ P → g • x ∈ P)
    (hSP : S ⊔ P = ⊤)
    (σ : G) :
    letI := stableSubgroupMulDistribMulAction S hS
    letI := stableQuotientMulDistribMulAction
      (P.subgroupOf S)
      (supportedPrincipalIntersection_stable S P hS hP)
    letI := stableQuotientMulDistribMulAction P hP
    HerbrandHMinusOne G (S ⧸ P.subgroupOf S) σ ≃*
      HerbrandHMinusOne G (A ⧸ P) σ := by
  letI := stableSubgroupMulDistribMulAction S hS
  letI := stableQuotientMulDistribMulAction
    (P.subgroupOf S)
    (supportedPrincipalIntersection_stable S P hS hP)
  letI := stableQuotientMulDistribMulAction P hP
  exact
    herbrandHMinusOneEquivariantMulEquiv
      (subgroupQuotientEquivQuotientOfSupEqTop S P hSP)
      (subgroupQuotientEquivQuotientOfSupEqTop_smul
        S P hS hP hSP) σ

end CyclicCohomology

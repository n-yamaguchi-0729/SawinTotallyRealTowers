/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.Comparison.DiscreteCompletion

/-!
# Fox differential: completed — comparison — quotient family

The principal declarations in this module are:

- `ZCFiniteStageQuotientBundle`
  A bundled finite-stage quotient family for source-stage comparison theorems. The purpose is to
  carry the topology and topological-group structure on the quotient target once, instead of
  repeating these hypotheses at every comparison theorem.
- `Target`
  The target quotient carried by a finite-stage quotient bundle.
- `targetFiniteInstance`
  The finiteness instance certified by a genuine finite-stage quotient bundle.
- `targetDiscreteTopology`
  The genuine finite quotient stage has discrete topology.
-/

namespace FoxDifferential

noncomputable section

universe u

section FiniteStageQuotientBundle

variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal]

/--
A bundled finite-stage quotient family for source-stage comparison theorems. The purpose is to
carry the topology and topological-group structure on the quotient target once, instead of
repeating these hypotheses at every comparison theorem.
-/
structure ZCFiniteStageQuotientBundle where
  /-- Finiteness of the algebraic Fox-stage target quotient. -/
  targetFinite : Finite (foxAlgebraicStageTargetQuotient (X := X) N)

namespace ZCFiniteStageQuotientBundle

variable {N}
variable (C : ProCGroups.FiniteGroupClass.{u})

/-- The target quotient carried by a finite-stage quotient bundle. -/
abbrev Target (_B : ZCFiniteStageQuotientBundle N) : Type u :=
  foxAlgebraicStageTargetQuotient (X := X) N

omit [DecidableEq X] [N.Normal] in
/-- The finiteness instance certified by a genuine finite-stage quotient bundle. -/
theorem targetFiniteInstance (B : ZCFiniteStageQuotientBundle N) :
    Finite (Target (N := N) B) :=
  B.targetFinite

/-- The canonical discrete topology on a genuine finite quotient stage.

This keeps the historical projection-style name while removing the former arbitrary-topology
field. -/
@[reducible]
def targetTopology (_B : ZCFiniteStageQuotientBundle N) :
    TopologicalSpace (Target (N := N) _B) :=
  ⊥

omit [DecidableEq X] [N.Normal] in
/-- The genuine finite quotient stage has discrete topology. -/
theorem targetDiscreteTopology (B : ZCFiniteStageQuotientBundle N) :
    @DiscreteTopology (Target (N := N) B) B.targetTopology := by
  change @DiscreteTopology (Target (N := N) B) ⊥
  exact discreteTopology_bot _

omit [DecidableEq X] in
/-- The canonical discrete topology makes the genuine finite quotient stage a topological group.

This keeps the historical projection-style name while deriving the structure rather than accepting
it as unrelated input data. -/
theorem targetIsTopologicalGroup (B : ZCFiniteStageQuotientBundle N) :
    @IsTopologicalGroup (Target (N := N) B) B.targetTopology inferInstance := by
  let : TopologicalSpace (Target (N := N) B) := B.targetTopology
  let : DiscreteTopology (Target (N := N) B) := B.targetDiscreteTopology
  infer_instance

/-- The canonical quotient morphism represented by a genuine finite-stage bundle. -/
def quotientMap (_B : ZCFiniteStageQuotientBundle N) :
    FreeGroup X →* Target (N := N) _B :=
  QuotientGroup.mk' N

omit [DecidableEq X] in
/-- The canonical quotient morphism of a genuine finite-stage bundle is surjective. -/
theorem quotientMap_surjective (B : ZCFiniteStageQuotientBundle N) :
    Function.Surjective B.quotientMap :=
  QuotientGroup.mk'_surjective N

omit [DecidableEq X] in
/-- Bundle an already known finite quotient using its canonical discrete topology. -/
theorem ofFinite
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [Finite (foxAlgebraicStageTargetQuotient (X := X) N)] :
    ZCFiniteStageQuotientBundle N :=
  ⟨inferInstance⟩

/-- The completed pro-\(C\) stage indices for the bundled target quotient. -/
abbrev Index (B : ZCFiniteStageQuotientBundle N) : Type u :=
  letI : TopologicalSpace (Target (N := N) B) := B.targetTopology
  ZCCompletedGroupAlgebraIndex C (Target (N := N) B)

/-- The completed group algebra of the bundled target quotient. -/
abbrev CompletedGroupAlgebra (B : ZCFiniteStageQuotientBundle N) : Type u :=
  letI : TopologicalSpace (Target (N := N) B) := B.targetTopology
  letI : IsTopologicalGroup (Target (N := N) B) := B.targetIsTopologicalGroup
  ZCCompletedGroupAlgebra C (Target (N := N) B)

/--
The scalar stage attached to the quotient bundle is evaluated at the corresponding finite
quotient and coefficient stage.
-/
theorem scalarStage_apply
    (B : ZCFiniteStageQuotientBundle N)
    (j : B.Index C) (w : FreeGroup X) :
    letI : TopologicalSpace (Target (N := N) B) := B.targetTopology
    letI : IsTopologicalGroup (Target (N := N) B) := B.targetIsTopologicalGroup
    zcCompletedGroupAlgebraScalarStage C N j w =
      (letI : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
       modNCompletedGroupAlgebraStageMapInClass j.1.modulus
        (zcFiniteStageTarget X N) C j.2
        (foxAlgebraicStageCoefficient (X := X) N j.1.modulus w)) := by
  let : TopologicalSpace (Target (N := N) B) := B.targetTopology
  let : IsTopologicalGroup (Target (N := N) B) := B.targetIsTopologicalGroup
  exact zcCompletedGroupAlgebraScalarStage_apply (C := C) (X := X) N j w

/-- Completed derivative projection theorem, using the bundled quotient-family hypotheses. -/
theorem derivative_finiteStageProjection
    (B : ZCFiniteStageQuotientBundle N)
    (j : B.Index C) (i : X) (w : FreeGroup X) :
    letI : TopologicalSpace (Target (N := N) B) := B.targetTopology
    letI : IsTopologicalGroup (Target (N := N) B) := B.targetIsTopologicalGroup
    zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j
        (zcFreeGroupFoxDerivative C (QuotientGroup.mk' N) i w) =
      (letI : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
       modNCompletedGroupAlgebraStageMapInClass j.1.modulus
        (zcFiniteStageTarget X N) C j.2
        (foxAlgebraicStageDerivative (X := X) N j.1.modulus i w)) := by
  let : TopologicalSpace (Target (N := N) B) := B.targetTopology
  let : IsTopologicalGroup (Target (N := N) B) := B.targetIsTopologicalGroup
  exact zcFreeGroupFoxDerivative_finiteStageProjection (C := C) (X := X) N j i w

/-- Completed derivative-vector projection theorem, using the bundled quotient-family hypotheses. -/
theorem derivativeVector_finiteStageProjection
    (B : ZCFiniteStageQuotientBundle N)
    (j : B.Index C) (w : FreeGroup X) :
    letI : TopologicalSpace (Target (N := N) B) := B.targetTopology
    letI : IsTopologicalGroup (Target (N := N) B) := B.targetIsTopologicalGroup
    (fun i : X =>
      zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j
        (zcFreeGroupFoxDerivativeVector C (QuotientGroup.mk' N) w i)) =
      fun i : X =>
        letI : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
        modNCompletedGroupAlgebraStageMapInClass j.1.modulus
          (zcFiniteStageTarget X N) C j.2
          (foxAlgebraicStageDerivative (X := X) N j.1.modulus i w) := by
  let : TopologicalSpace (Target (N := N) B) := B.targetTopology
  let : IsTopologicalGroup (Target (N := N) B) := B.targetIsTopologicalGroup
  exact zcFreeGroupFoxDerivativeVector_finiteStageProjection (C := C) (X := X) N j w

/--
Discrete-reduction derivative projection theorem, using the bundled quotient-family hypotheses.
-/
theorem derivative_finiteStageProjection_discreteReduction
    (B : ZCFiniteStageQuotientBundle N)
    (j : B.Index C) (i : X) (w : FreeGroup X) :
    letI : TopologicalSpace (Target (N := N) B) := B.targetTopology
    letI : IsTopologicalGroup (Target (N := N) B) := B.targetIsTopologicalGroup
    zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j
        (zcFreeGroupFoxDerivative C (QuotientGroup.mk' N) i w) =
      (letI : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
       modNCompletedGroupAlgebraStageMapInClass j.1.modulus
        (zcFiniteStageTarget X N) C j.2
        (foxAlgebraicStageGroupRingReduction (X := X) N j.1.modulus
          (FoxCalculus.relativeFreeGroupFoxDerivative
            (H := zcFiniteStageTarget X N) X (QuotientGroup.mk' N) w i))) := by
  let : TopologicalSpace (Target (N := N) B) := B.targetTopology
  let : IsTopologicalGroup (Target (N := N) B) := B.targetIsTopologicalGroup
  exact zcFreeGroupFoxDerivative_finiteStageProjection_discreteReduction
    (C := C) (X := X) N i w j

/--
Discrete-reduction derivative-vector projection theorem, using the bundled quotient-family
hypotheses.
-/
theorem derivativeVector_finiteStageProjection_discreteReduction
    (B : ZCFiniteStageQuotientBundle N)
    (j : B.Index C) (w : FreeGroup X) :
    letI : TopologicalSpace (Target (N := N) B) := B.targetTopology
    letI : IsTopologicalGroup (Target (N := N) B) := B.targetIsTopologicalGroup
    (fun i : X =>
      zcCompletedGroupAlgebraProjection C (zcFiniteStageTarget X N) j
        (zcFreeGroupFoxDerivativeVector C (QuotientGroup.mk' N) w i)) =
      fun i : X =>
        letI : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
        modNCompletedGroupAlgebraStageMapInClass j.1.modulus
          (zcFiniteStageTarget X N) C j.2
          (foxAlgebraicStageGroupRingReduction (X := X) N j.1.modulus
            (FoxCalculus.relativeFreeGroupFoxDerivative
              (H := zcFiniteStageTarget X N) X (QuotientGroup.mk' N) w i)) := by
  let : TopologicalSpace (Target (N := N) B) := B.targetTopology
  let : IsTopologicalGroup (Target (N := N) B) := B.targetIsTopologicalGroup
  exact zcFreeGroupFoxDerivativeVector_finiteStageProjection_discreteReduction
    (C := C) (X := X) N w j

end ZCFiniteStageQuotientBundle

end FiniteStageQuotientBundle

end

end FoxDifferential

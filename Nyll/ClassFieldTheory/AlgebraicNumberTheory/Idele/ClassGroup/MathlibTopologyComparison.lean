/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Topology
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Quotient topology on the standard idèle class group

The standard quotient topology is induced by raw idèle representatives and
supports descent of continuous homomorphisms.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace IdeleGroup

variable (K : Type*) [Field K] [NumberField K]

/-- The raw-to-standard class projection is an open quotient map. -/
theorem isOpenQuotientMap_toStandardClass : IsOpenQuotientMap (toStandardClass K) :=
  QuotientGroup.isOpenQuotientMap_mk (N := principalSubgroup K)

/-- The raw-to-standard class projection induces the standard quotient topology. -/
theorem isQuotientMap_toStandardClass : Topology.IsQuotientMap (toStandardClass K) :=
  (isOpenQuotientMap_toStandardClass K).isQuotientMap

/-- The image of an open set of raw ideles is open in the standard class group. -/
theorem isOpenMap_toStandardClass : IsOpenMap (toStandardClass K) :=
  (isOpenQuotientMap_toStandardClass K).isOpenMap

/-- The raw-to-standard class projection is continuous. -/
theorem continuous_toStandardClass : Continuous (toStandardClass K) :=
  (isQuotientMap_toStandardClass K).continuous

section Lift

variable {G : Type*} [Monoid G] [TopologicalSpace G]

/-- Descend a continuous homomorphism from raw ideles that kills principal ideles. -/
noncomputable def liftContinuousToStandardClass (f : IdeleGroup K →ₜ* G)
    (h : principalSubgroup K ≤ f.toMonoidHom.ker) : IdeleClassGroup K →ₜ* G where
  toMonoidHom := liftToStandardClass K f.toMonoidHom h
  continuous_toFun := (isQuotientMap_toStandardClass K).continuous_iff.mpr
    (f.continuous.congr fun a => (liftToStandardClass_toStandardClass K f.toMonoidHom h a).symm)

/-- The continuous lift agrees with the original homomorphism on every representative. -/
@[simp]
theorem liftContinuousToStandardClass_toStandardClass (f : IdeleGroup K →ₜ* G)
    (h : principalSubgroup K ≤ f.toMonoidHom.ker) (a : IdeleGroup K) :
    liftContinuousToStandardClass K f h (toStandardClass K a) = f a :=
  liftToStandardClass_toStandardClass K f.toMonoidHom h a

end Lift

end IdeleGroup

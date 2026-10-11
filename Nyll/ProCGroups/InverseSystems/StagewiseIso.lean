/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.InverseSystems.CompatibilityAndSurjectivity
import Nyll.ProCGroups.Topologies.ContinuousMulEquiv

/-!
# Stagewise isomorphisms and inverse-limit equivalences

A compatible family of continuous group isomorphisms defines morphisms in both directions
between two inverse systems.  The induced maps on their inverse limits are assembled into a
canonical continuous multiplicative equivalence.
-/

open scoped Topology

namespace ProCGroups
namespace InverseSystems

universe u v

namespace InverseSystem

variable {I : Type u} [Preorder I]
variable (S T : InverseSystem.{u, v} (I := I))
variable [∀ i, Group (S.X i)] [∀ i, Group (T.X i)]
variable [IsGroupSystem S] [IsGroupSystem T]
variable [∀ i, IsTopologicalGroup (S.X i)] [∀ i, IsTopologicalGroup (T.X i)]

/--
A compatible family of stagewise continuous group isomorphisms between two concrete inverse
systems.
-/
structure InverseSystemIso where
  /-- A continuous group isomorphism between the source and target objects at each index. -/
  stageEquiv : ∀ i, S.X i ≃ₜ* T.X i
  /-- The stagewise isomorphisms intertwine the transition maps of the two systems. -/
  comm : ∀ {i j : I} (hij : i ≤ j) (x : S.X j),
    stageEquiv i (S.map hij x) = T.map hij (stageEquiv j x)

namespace InverseSystemIso

variable {S T}

/-- A stagewise isomorphism determines the forward morphism of inverse systems. -/
def toMorphism (E : InverseSystemIso S T) : S.Morphism T where
  map i := E.stageEquiv i
  continuous_map i := (E.stageEquiv i).continuous_toFun
  comm := by
    intro i j hij
    funext x
    exact (E.comm hij x).symm

/-- A stagewise isomorphism determines the inverse morphism of inverse systems. -/
def invMorphism (E : InverseSystemIso S T) : T.Morphism S where
  map i := (E.stageEquiv i).symm
  continuous_map i := (E.stageEquiv i).continuous_invFun
  comm := by
    intro i j hij
    funext x
    apply (E.stageEquiv i).injective
    simpa using E.comm hij ((E.stageEquiv j).symm x)

/-- The forward continuous homomorphism on inverse limits induced by a stagewise isomorphism. -/
noncomputable def toContinuousMonoidHom (E : InverseSystemIso S T) :
    S.inverseLimit →ₜ* T.inverseLimit where
  toMonoidHom :=
    { toFun := S.limMap E.toMorphism
      map_one' := by
        apply T.ext
        intro i
        change T.projection i (S.limMap E.toMorphism 1) = T.projection i 1
        rw [S.π_limMap_apply (Θ := E.toMorphism)]
        change (E.stageEquiv i) (1 : S.X i) = (1 : T.X i)
        exact (E.stageEquiv i).toMulEquiv.map_one
      map_mul' := by
        intro x y
        apply T.ext
        intro i
        change T.projection i (S.limMap E.toMorphism (x * y)) =
          T.projection i (S.limMap E.toMorphism x * S.limMap E.toMorphism y)
        rw [S.π_limMap_apply (Θ := E.toMorphism)]
        rw [projection_mul (S := T), S.π_limMap_apply (Θ := E.toMorphism),
          S.π_limMap_apply (Θ := E.toMorphism)]
        change (E.stageEquiv i) (S.projection i x * S.projection i y) =
          (E.stageEquiv i) (S.projection i x) * (E.stageEquiv i) (S.projection i y)
        exact (E.stageEquiv i).toMulEquiv.map_mul (S.projection i x) (S.projection i y) }
  continuous_toFun := S.continuous_limMap E.toMorphism

/-- The inverse continuous homomorphism on inverse limits induced by a stagewise isomorphism. -/
noncomputable def invContinuousMonoidHom (E : InverseSystemIso S T) :
    T.inverseLimit →ₜ* S.inverseLimit where
  toMonoidHom :=
    { toFun := T.limMap E.invMorphism
      map_one' := by
        apply S.ext
        intro i
        change S.projection i (T.limMap E.invMorphism 1) = S.projection i 1
        rw [T.π_limMap_apply (Θ := E.invMorphism)]
        change (E.stageEquiv i).symm (1 : T.X i) = (1 : S.X i)
        exact (E.stageEquiv i).symm.toMulEquiv.map_one
      map_mul' := by
        intro x y
        apply S.ext
        intro i
        change S.projection i (T.limMap E.invMorphism (x * y)) =
          S.projection i (T.limMap E.invMorphism x * T.limMap E.invMorphism y)
        rw [T.π_limMap_apply (Θ := E.invMorphism)]
        rw [projection_mul (S := S), T.π_limMap_apply (Θ := E.invMorphism),
          T.π_limMap_apply (Θ := E.invMorphism)]
        change (E.stageEquiv i).symm (T.projection i x * T.projection i y) =
          (E.stageEquiv i).symm (T.projection i x) * (E.stageEquiv i).symm (T.projection i y)
        exact (E.stageEquiv i).symm.toMulEquiv.map_mul (T.projection i x) (T.projection i y) }
  continuous_toFun := T.continuous_limMap E.invMorphism

/--
Compatible stagewise continuous group isomorphisms induce a continuous multiplicative
equivalence on concrete inverse limits.
-/
noncomputable def inverseLimitContinuousMulEquiv (E : InverseSystemIso S T) :
    S.inverseLimit ≃ₜ* T.inverseLimit :=
  ContinuousMulEquiv.ofHomInv
    E.toContinuousMonoidHom
    E.invContinuousMonoidHom
    (by
      intro x
      apply S.ext
      intro i
      change S.projection i
          (T.limMap E.invMorphism (S.limMap E.toMorphism x)) = S.projection i x
      rw [T.π_limMap_apply (Θ := E.invMorphism),
        S.π_limMap_apply (Θ := E.toMorphism)]
      simp only [invMorphism, toMorphism, projection_apply, ContinuousMulEquiv.symm_apply_apply])
    (by
      intro x
      apply T.ext
      intro i
      change T.projection i
          (S.limMap E.toMorphism (T.limMap E.invMorphism x)) = T.projection i x
      rw [S.π_limMap_apply (Θ := E.toMorphism),
        T.π_limMap_apply (Θ := E.invMorphism)]
      simp only [toMorphism, invMorphism, projection_apply, ContinuousMulEquiv.apply_symm_apply])

omit [∀ i, IsTopologicalGroup (S.X i)] [∀ i, IsTopologicalGroup (T.X i)] in
/--
The projection inverse limit continuous multiplicative equivalence is compatible with the
profinite topology and gives the continuous map or equivalence determined by the finite-quotient
data.
-/
@[simp] theorem projection_inverseLimitContinuousMulEquiv
    (E : InverseSystemIso S T) (i : I) (x : S.inverseLimit) :
    T.projection i (E.inverseLimitContinuousMulEquiv x) =
      E.stageEquiv i (S.projection i x) := by
  change T.projection i (S.limMap E.toMorphism x) =
    E.stageEquiv i (S.projection i x)
  exact S.π_limMap_apply E.toMorphism i x

omit [∀ i, IsTopologicalGroup (S.X i)] [∀ i, IsTopologicalGroup (T.X i)] in
/--
The inverse of the projection-induced inverse-limit continuous multiplicative equivalence is
compatible with the profinite topology and gives the continuous map or equivalence determined by
the finite-quotient data.
-/
@[simp] theorem projection_inverseLimitContinuousMulEquiv_symm
    (E : InverseSystemIso S T) (i : I) (x : T.inverseLimit) :
    S.projection i (E.inverseLimitContinuousMulEquiv.symm x) =
      (E.stageEquiv i).symm (T.projection i x) := by
  change S.projection i (T.limMap E.invMorphism x) =
    (E.stageEquiv i).symm (T.projection i x)
  exact T.π_limMap_apply E.invMorphism i x

end InverseSystemIso

end InverseSystem

end InverseSystems
end ProCGroups

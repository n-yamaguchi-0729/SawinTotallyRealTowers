/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Algebra.ProperAction.Basic
import Nyll.ProCGroups.InverseSystems.CompatibilityAndSurjectivity
import Nyll.ProCGroups.Topologies.QuotientMaps

/-!
# Quotients of group-valued inverse systems

A compatible family of closed normal stage subgroups induces an inverse system of quotient
groups and a canonical map from the original limit.  This module identifies its kernel and,
under compact Hausdorff directed-surjective hypotheses, proves that quotienting the inverse
limit agrees topologically and algebraically with taking the inverse limit of the stage quotients.
-/

open scoped Topology

namespace ProCGroups
namespace InverseSystems

universe u v

namespace InverseSystem

variable {I : Type u} [Preorder I]
variable (S : InverseSystem.{u, v} (I := I))
variable [∀ i, Group (S.X i)] [IsGroupSystem S]
variable [∀ i, IsTopologicalGroup (S.X i)]

/-- The transition map of a group-valued inverse system is bundled as a homomorphism. -/
def transitionHom {i j : I} (hij : i ≤ j) : S.X j →* S.X i where
  toFun := S.map hij
  map_one' := IsGroupSystem.map_one (S := S) hij
  map_mul' := IsGroupSystem.map_mul (S := S) hij

omit [∀ i, IsTopologicalGroup (S.X i)] in
/-- The bundled transition homomorphism evaluates to the underlying transition map of `S`. -/
@[simp] theorem transitionHom_apply {i j : I} (hij : i ≤ j) (x : S.X j) :
    S.transitionHom hij x = S.map hij x := rfl

omit [∀ i, IsTopologicalGroup (S.X i)] in
/-- The bundled transition homomorphism of an inverse system is continuous. -/
theorem continuous_transitionHom {i j : I} (hij : i ≤ j) :
    Continuous (S.transitionHom hij) :=
  S.continuous_map hij

/-- Closed normal subgroups of the stages, compatible with transition maps. -/
structure CompatibleClosedNormalSubgroups where
  /-- The subgroup by which the stage at index `i` will be quotiented. -/
  N : ∀ i, Subgroup (S.X i)
  /-- Every selected stage subgroup is normal, so its group quotient is defined. -/
  normal : ∀ i, (N i).Normal
  /-- Every selected stage subgroup is closed in the topology of that stage. -/
  closed : ∀ i, IsClosed ((N i : Subgroup (S.X i)) : Set (S.X i))
  /--
  A transition homomorphism sends the subgroup at the later stage into the subgroup at the
  earlier stage, and hence descends to the corresponding quotients.
  -/
  map_le :
    ∀ {i j : I} (hij : i ≤ j), N j ≤ (N i).comap (S.transitionHom hij)

namespace CompatibleClosedNormalSubgroups

variable {S}
variable (Q : S.CompatibleClosedNormalSubgroups)

/-- The chosen subgroup is normal. -/
instance instNormalN (i : I) : (Q.N i).Normal := Q.normal i

/-- The transition map induced on stage quotients. -/
def quotientMap {i j : I} (hij : i ≤ j) :
    S.X j ⧸ Q.N j →* S.X i ⧸ Q.N i :=
  QuotientGroup.map (N := Q.N j) (M := Q.N i) (f := S.transitionHom hij) (Q.map_le hij)

omit [∀ i, IsTopologicalGroup (S.X i)] in
/--
The induced quotient transition sends the class of `x` modulo `N j` to the class of its
transition image modulo `N i`.
-/
@[simp] theorem quotientMap_mk {i j : I} (hij : i ≤ j) (x : S.X j) :
    Q.quotientMap hij (QuotientGroup.mk' (Q.N j) x) =
      QuotientGroup.mk' (Q.N i) (S.map hij x) := by
  exact QuotientGroup.map_mk' (N := Q.N j) (M := Q.N i)
    (f := S.transitionHom hij) (Q.map_le hij) x

omit [∀ i, IsTopologicalGroup (S.X i)] in
/-- The induced map on stage quotients is continuous. -/
theorem continuous_quotientMap {i j : I} (hij : i ≤ j) :
    Continuous (Q.quotientMap hij) := by
  refine (QuotientGroup.isQuotientMap_mk (N := Q.N j)).continuous_iff.2 ?_
  change Continuous fun x : S.X j => QuotientGroup.mk' (Q.N i) (S.map hij x)
  exact QuotientGroup.continuous_mk.comp (S.continuous_map hij)

/-- The inverse system obtained by quotienting each stage by a compatible closed normal subgroup. -/
def quotientInverseSystem : InverseSystem (I := I) where
  X := fun i => S.X i ⧸ Q.N i
  topologicalSpace := fun i => inferInstance
  map := fun {_i _j} hij => Q.quotientMap hij
  continuous_map := fun {_i _j} hij => Q.continuous_quotientMap hij
  map_id := by
    intro i
    funext x
    refine Quotient.inductionOn' x ?_
    intro a
    change QuotientGroup.mk' (Q.N i) (S.map (le_rfl : i ≤ i) a) =
      QuotientGroup.mk' (Q.N i) a
    exact congrArg (QuotientGroup.mk' (Q.N i)) (S.map_id_apply i a)
  map_comp := by
    intro i j k hij hjk
    funext x
    refine Quotient.inductionOn' x ?_
    intro a
    change QuotientGroup.mk' (Q.N i) (S.map hij (S.map hjk a)) =
      QuotientGroup.mk' (Q.N i) (S.map (hij.trans hjk) a)
    exact congrArg (QuotientGroup.mk' (Q.N i)) (S.map_comp_apply hij hjk a)

/-- The quotient inverse system has the expected finite-stage quotient groups. -/
instance quotientInverseSystem_stageGroup (i : I) :
    Group (Q.quotientInverseSystem.X i) := by
  change Group (S.X i ⧸ Q.N i)
  infer_instance

/-- Each stage quotient carries the quotient topology and its induced topological-group
structure. -/
instance quotientInverseSystem_stageTopologicalGroup (i : I) :
    IsTopologicalGroup (Q.quotientInverseSystem.X i) := by
  change IsTopologicalGroup (S.X i ⧸ Q.N i)
  infer_instance

/-- Fix the closed-subgroup boundary before using the quotient's canonical topology. -/
private theorem quotientInverseSystem_stageT2Space (i : I) :
    T2Space (Q.quotientInverseSystem.X i) := by
  change T2Space (S.X i ⧸ Q.N i)
  have : IsClosed (Q.N i : Set (S.X i)) := Q.closed i
  exact QuotientGroup.instT2Space (H := Q.N i)

/-- The induced quotient transitions preserve the group operations at every stage. -/
instance quotientInverseSystem_isGroupSystem :
    IsGroupSystem Q.quotientInverseSystem where
  map_one := by
    intro i j hij
    exact (Q.quotientMap hij).map_one
  map_mul := by
    intro i j hij x y
    exact (Q.quotientMap hij).map_mul x y
  map_inv := by
    intro i j hij x
    exact (Q.quotientMap hij).map_inv x

/-- The stagewise quotient maps form a morphism from the original system to the quotient system. -/
def toQuotientInverseSystem : S.Morphism Q.quotientInverseSystem where
  map := fun i => QuotientGroup.mk' (Q.N i)
  continuous_map := fun _ => QuotientGroup.continuous_mk
  comm := by
    intro i j hij
    funext x
    exact (Q.quotientMap_mk hij x).symm

/-- Kernel of the map from the inverse limit to the inverse limit of stage quotients. -/
def inverseLimitKernel : Subgroup S.inverseLimit :=
  ⨅ i, (Q.N i).comap (projectionHom (S := S) i)

/--
The intersection of the pullbacks of the normal subgroups `N i` along all limit projections is
a normal subgroup of the inverse limit.
-/
instance inverseLimitKernel_normal : Q.inverseLimitKernel.Normal where
  conj_mem x hx g := by
    rw [inverseLimitKernel] at hx ⊢
    simp only [projectionHom, Subgroup.mem_iInf, Subgroup.mem_comap, MonoidHom.coe_mk,
        OneHom.coe_mk,
  projection_apply] at hx ⊢
    intro i
    change
      S.projection i g * S.projection i x * (S.projection i g)⁻¹ ∈ Q.N i
    exact (Q.normal i).conj_mem (S.projection i x) (hx i) (S.projection i g)

variable {Q}

omit [∀ i, IsTopologicalGroup (S.X i)] in
/--
Membership in the named kernel is equivalent to vanishing under its defining quotient or
augmentation map.
-/
theorem mem_inverseLimitKernel_iff {x : S.inverseLimit} :
    x ∈ Q.inverseLimitKernel ↔ ∀ i, S.projection i x ∈ Q.N i := by
  simp only [inverseLimitKernel, projectionHom, Subgroup.mem_iInf, Subgroup.mem_comap,
      MonoidHom.coe_mk,
  OneHom.coe_mk, projection_apply]

variable (Q)

/--
The canonical comparison from the quotient of the inverse limit to the inverse limit of the
stage quotients.
-/
noncomputable def quotientInverseLimitComparison :
    S.inverseLimit ⧸ Q.inverseLimitKernel →ₜ* Q.quotientInverseSystem.inverseLimit := by
  let T : InverseSystem (I := I) := Q.quotientInverseSystem
  let φ : S.inverseLimit →ₜ* T.inverseLimit :=
    { toMonoidHom :=
        { toFun := S.limMap Q.toQuotientInverseSystem
          map_one' := by
            apply T.ext
            intro i
            calc
              T.projection i (S.limMap Q.toQuotientInverseSystem 1) =
                  Q.toQuotientInverseSystem.map i (S.projection i (1 : S.inverseLimit)) := by
                exact S.π_limMap_apply Q.toQuotientInverseSystem i 1
              _ = 1 := by
                change QuotientGroup.mk' (Q.N i) (S.projection i (1 : S.inverseLimit)) = 1
                rw [projection_one (S := S) i]
                simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_one]
          map_mul' := by
            intro x y
            apply T.ext
            intro i
            calc
              T.projection i (S.limMap Q.toQuotientInverseSystem (x * y)) =
                  Q.toQuotientInverseSystem.map i (S.projection i (x * y)) := by
                exact S.π_limMap_apply Q.toQuotientInverseSystem i (x * y)
              _ =
                  Q.toQuotientInverseSystem.map i (S.projection i x) *
                    Q.toQuotientInverseSystem.map i (S.projection i y) := by
                change QuotientGroup.mk' (Q.N i) (S.projection i (x * y)) =
                  QuotientGroup.mk' (Q.N i) (S.projection i x) *
                    QuotientGroup.mk' (Q.N i) (S.projection i y)
                rw [projection_mul (S := S) i x y]
                simp only [projection_apply, QuotientGroup.mk'_apply, QuotientGroup.mk_mul]
              _ =
                  T.projection i (S.limMap Q.toQuotientInverseSystem x) *
                    T.projection i (S.limMap Q.toQuotientInverseSystem y) := by
                rw [← S.π_limMap_apply Q.toQuotientInverseSystem i x,
                  ← S.π_limMap_apply Q.toQuotientInverseSystem i y] }
      continuous_toFun := S.continuous_limMap Q.toQuotientInverseSystem }
  refine QuotientGroup.liftₜ Q.inverseLimitKernel φ ?_
  intro x hx
  apply T.ext
  intro i
  have hxi : S.projection i x ∈ Q.N i := (Q.mem_inverseLimitKernel_iff (x := x)).1 hx i
  change QuotientGroup.mk' (Q.N i) (S.projection i x) = 1
  exact (QuotientGroup.eq_one_iff (N := Q.N i) (S.projection i x)).2 hxi

omit [∀ i, IsTopologicalGroup (S.X i)] in
/--
The quotient inverse-limit comparison sends a representative to its compatible family of
quotient coordinates.
-/
@[simp] theorem quotientInverseLimitComparison_mk (x : S.inverseLimit) :
    Q.quotientInverseLimitComparison (QuotientGroup.mk' Q.inverseLimitKernel x) =
      S.limMap Q.toQuotientInverseSystem x :=
  by
    unfold quotientInverseLimitComparison
    rfl

omit [∀ i, IsTopologicalGroup (S.X i)] in
/--
Projecting the quotient inverse-limit comparison gives the corresponding stage quotient
representative.
-/
@[simp] theorem projection_quotientInverseLimitComparison_mk
    (i : I) (x : S.inverseLimit) :
    Q.quotientInverseSystem.projection i
        (Q.quotientInverseLimitComparison (QuotientGroup.mk' Q.inverseLimitKernel x)) =
      QuotientGroup.mk' (Q.N i) (S.projection i x) := by
  rw [quotientInverseLimitComparison_mk]
  rfl

omit [∀ i, IsTopologicalGroup (S.X i)] in
/-- The comparison map has trivial kernel. -/
theorem ker_quotientInverseLimitComparison :
    Q.quotientInverseLimitComparison.toMonoidHom.ker = ⊥ := by
  ext a
  constructor
  · intro ha
    refine Quotient.inductionOn' a ?_ ha
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff (N := Q.inverseLimitKernel) x).2 <| by
      rw [Q.mem_inverseLimitKernel_iff]
      intro i
      have hcoord :=
        congrArg (fun y => Q.quotientInverseSystem.projection i y) hx
      change QuotientGroup.mk' (Q.N i) (S.projection i x) = 1 at hcoord
      exact (QuotientGroup.eq_one_iff (N := Q.N i) (S.projection i x)).1 hcoord
  · intro ha
    rw [Subgroup.mem_bot] at ha
    rw [MonoidHom.mem_ker, ha]
    exact map_one Q.quotientInverseLimitComparison

omit [∀ i, IsTopologicalGroup (S.X i)] in
/-- The comparison map is injective: its kernel is exactly the subgroup used in the quotient. -/
theorem injective_quotientInverseLimitComparison :
    Function.Injective Q.quotientInverseLimitComparison :=
  (MonoidHom.ker_eq_bot_iff (f := Q.quotientInverseLimitComparison.toMonoidHom)).mp
    Q.ker_quotientInverseLimitComparison

/-- The comparison map is surjective for compact Hausdorff systems over a directed index. -/
theorem surjective_quotientInverseLimitComparison
    [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I)) :
    Function.Surjective Q.quotientInverseLimitComparison := by
  let T : InverseSystem (I := I) := Q.quotientInverseSystem
  let : ∀ i, T2Space (T.X i) := Q.quotientInverseSystem_stageT2Space
  have hlimsurj : Function.Surjective (S.limMap Q.toQuotientInverseSystem) :=
    S.surjective_limMap (T := T) hdir Q.toQuotientInverseSystem
      (fun i => QuotientGroup.mk'_surjective (Q.N i))
  intro y
  rcases hlimsurj y with ⟨x, hx⟩
  refine ⟨QuotientGroup.mk' Q.inverseLimitKernel x, ?_⟩
  rw [Q.quotientInverseLimitComparison_mk]
  exact hx

/-- The comparison map is bijective for compact Hausdorff systems over a directed index. -/
theorem bijective_quotientInverseLimitComparison
    [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I)) :
    Function.Bijective Q.quotientInverseLimitComparison :=
  ⟨Q.injective_quotientInverseLimitComparison,
    Q.surjective_quotientInverseLimitComparison hdir⟩

/--
The quotient of an inverse limit by a compatible closed normal family is the inverse limit of
the stage quotients.
-/
noncomputable def quotientInverseLimitContinuousMulEquiv
    [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I)) :
    S.inverseLimit ⧸ Q.inverseLimitKernel ≃ₜ* Q.quotientInverseSystem.inverseLimit := by
  let T : InverseSystem (I := I) := Q.quotientInverseSystem
  let f : S.inverseLimit ⧸ Q.inverseLimitKernel →ₜ* T.inverseLimit :=
    Q.quotientInverseLimitComparison
  letI : ∀ i, T2Space (T.X i) := Q.quotientInverseSystem_stageT2Space
  exact ContinuousMulEquiv.ofBijectiveCompactToT2
    f.toMonoidHom f.continuous_toFun (Q.bijective_quotientInverseLimitComparison hdir)

end CompatibleClosedNormalSubgroups

end InverseSystem

end InverseSystems
end ProCGroups

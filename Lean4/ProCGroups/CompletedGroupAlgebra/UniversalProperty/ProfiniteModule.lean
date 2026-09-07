import ProCGroups.CompletedGroupAlgebra.UniversalProperty.OpenSubmoduleQuotient

set_option autoImplicit false

/-!
# Lifts to profinite modules

Compatible lifts to all open-submodule quotients are assembled by compactness into a continuous
linear map to a profinite module. This file proves existence and uniqueness and applies it to the
free profinite-module property of completed group algebras.
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems
open ProCGroups.Completion

universe u v w

variable (R : ProfiniteCommRing.{u})
variable (G : ProfiniteGrp.{v})

local instance (N : ProfiniteModule.{u, w} R.toProfiniteRing) : Module R N :=
  N.module

local instance (N : ProfiniteModule.{u, w} R.toProfiniteRing) :
    ContinuousSMul R N :=
  N.continuousSMul

/--
The closed fiber in a profinite target determined by the quotient-valued extension modulo one
open submodule.
-/
private def completedGroupAlgebraLiftFiberSet
    (N : ProfiniteModule.{u, w} R.toProfiniteRing)
    (f : G → N) (hf : Continuous f)
    (x : CompletedGroupAlgebraCarrier R G)
    (W : ProfiniteModuleOpenSubmodule (R := R) N) : Set N :=
  {y | Submodule.mkQ W.1 y =
    completedGroupAlgebraLiftToOpenSubmoduleQuotient
      (R := R) (G := G) N f hf W.1 W.2 x}

/-- The quotient fiber attached to an open submodule is closed. -/
private theorem completedGroupAlgebraLiftFiberSet_isClosed
    (N : ProfiniteModule.{u, w} R.toProfiniteRing)
    (f : G → N) (hf : Continuous f)
    (x : CompletedGroupAlgebraCarrier R G)
    (W : ProfiniteModuleOpenSubmodule (R := R) N) :
    IsClosed (completedGroupAlgebraLiftFiberSet
      (R := R) (G := G) N f hf x W) := by
  let hdisc : IsDiscreteModule R (N ⧸ W.1) :=
    quotient_openSubmodule_isDiscreteModule R N W.1 W.2
  let : DiscreteTopology (N ⧸ W.1) := hdisc.2
  have hqcont : Continuous (Submodule.mkQ W.1 : N → N ⧸ W.1) := by
    change Continuous (Submodule.Quotient.mk (p := W.1))
    exact continuous_quotient_mk'
  change IsClosed ((Submodule.mkQ W.1 : N → N ⧸ W.1) ⁻¹'
    ({completedGroupAlgebraLiftToOpenSubmoduleQuotient
      (R := R) (G := G) N f hf W.1 W.2 x} : Set (N ⧸ W.1)))
  exact (isClosed_discrete _).preimage hqcont

/-- Finite intersection property for the fibers used to assemble the profinite-target lift. -/
private theorem completedGroupAlgebraLiftFiberSet_finite_inter_nonempty
    (N : ProfiniteModule.{u, w} R.toProfiniteRing)
    (f : G → N) (hf : Continuous f)
    (x : CompletedGroupAlgebraCarrier R G)
    (s : Finset (ProfiniteModuleOpenSubmodule (R := R) N)) :
    (⋂ W ∈ s, completedGroupAlgebraLiftFiberSet
      (R := R) (G := G) N f hf x W).Nonempty := by
  classical
  rcases exists_openSubmodule_le_finset (R := R) N s with ⟨K, hK⟩
  rcases Submodule.mkQ_surjective K.1
      (completedGroupAlgebraLiftToOpenSubmoduleQuotient
        (R := R) (G := G) N f hf K.1 K.2 x) with
    ⟨z, hz⟩
  refine ⟨z, ?_⟩
  simp only [Set.mem_iInter]
  intro W hWs
  dsimp [completedGroupAlgebraLiftFiberSet]
  calc
    Submodule.mkQ W.1 z = Submodule.factor (hK W hWs) (Submodule.mkQ K.1 z) := by
      rw [Submodule.factor_mk]
    _ = Submodule.factor (hK W hWs)
        (completedGroupAlgebraLiftToOpenSubmoduleQuotient
          (R := R) (G := G) N f hf K.1 K.2 x) := by
      rw [hz]
    _ = completedGroupAlgebraLiftToOpenSubmoduleQuotient
        (R := R) (G := G) N f hf W.1 W.2 x := by
      exact completedGroupAlgebraLiftToOpenSubmoduleQuotient_factor
        (R := R) (G := G) N f hf (hK W hWs) K.2 W.2 x

/--
Compactness of the profinite target gives a simultaneous lift of the compatible quotient values.
-/
private theorem completedGroupAlgebraLiftFiberSet_iInter_nonempty
    (N : ProfiniteModule.{u, w} R.toProfiniteRing)
    (f : G → N) (hf : Continuous f)
    (x : CompletedGroupAlgebraCarrier R G) :
    (⋂ W : ProfiniteModuleOpenSubmodule (R := R) N,
      completedGroupAlgebraLiftFiberSet
        (R := R) (G := G) N f hf x W).Nonempty := by
  exact CompactSpace.iInter_nonempty
    (t := fun W : ProfiniteModuleOpenSubmodule (R := R) N =>
      completedGroupAlgebraLiftFiberSet
        (R := R) (G := G) N f hf x W)
    (fun W => completedGroupAlgebraLiftFiberSet_isClosed
      (R := R) (G := G) N f hf x W)
    (fun s => completedGroupAlgebraLiftFiberSet_finite_inter_nonempty
      (R := R) (G := G) N f hf x s)

/-- The assembled pointwise lift from \(\widehat{R[G]}\) to a profinite target module. -/
private def completedGroupAlgebraLiftToProfiniteModuleFun
    (N : ProfiniteModule.{u, w} R.toProfiniteRing)
    (f : G → N) (hf : Continuous f) :
    CompletedGroupAlgebraCarrier R G → N :=
  fun x => Classical.choose
    (completedGroupAlgebraLiftFiberSet_iInter_nonempty
      (R := R) (G := G) N f hf x)

/--
The assembled point maps to the prescribed quotient-valued extension modulo every open
submodule.
-/
private theorem completedGroupAlgebraLiftToProfiniteModuleFun_quotient
    (N : ProfiniteModule.{u, w} R.toProfiniteRing)
    (f : G → N) (hf : Continuous f)
    (W : ProfiniteModuleOpenSubmodule (R := R) N)
    (x : CompletedGroupAlgebraCarrier R G) :
    Submodule.mkQ W.1
        (completedGroupAlgebraLiftToProfiniteModuleFun
          (R := R) (G := G) N f hf x) =
      completedGroupAlgebraLiftToOpenSubmoduleQuotient
        (R := R) (G := G) N f hf W.1 W.2 x := by
  have hmem := Classical.choose_spec
    (completedGroupAlgebraLiftFiberSet_iInter_nonempty
      (R := R) (G := G) N f hf x)
  exact (Set.mem_iInter.1 hmem W : _)

/-- The assembled lift has the prescribed values on the completed group-like elements. -/
@[simp]
private theorem completedGroupAlgebraLiftToProfiniteModuleFun_apply_of
    (N : ProfiniteModule.{u, w} R.toProfiniteRing)
    (f : G → N) (hf : Continuous f)
    (g : G) :
    completedGroupAlgebraLiftToProfiniteModuleFun
        (R := R) (G := G) N f hf (completedGroupAlgebraOf R G g) = f g := by
  apply profiniteModule_ext_of_openSubmoduleQuotients (R := R) N
  intro W hW
  rw [completedGroupAlgebraLiftToProfiniteModuleFun_quotient
      (R := R) (G := G) N f hf ⟨W, hW⟩,
    completedGroupAlgebraLiftToOpenSubmoduleQuotient_apply_of]

/--
Additivity of the assembled profinite-target lift, checked after all open-submodule quotients.
-/
private theorem completedGroupAlgebraLiftToProfiniteModuleFun_add
    (N : ProfiniteModule.{u, w} R.toProfiniteRing)
    (f : G → N) (hf : Continuous f)
    (x y : CompletedGroupAlgebraCarrier R G) :
    completedGroupAlgebraLiftToProfiniteModuleFun
        (R := R) (G := G) N f hf (x + y) =
      completedGroupAlgebraLiftToProfiniteModuleFun
        (R := R) (G := G) N f hf x +
      completedGroupAlgebraLiftToProfiniteModuleFun
        (R := R) (G := G) N f hf y := by
  apply profiniteModule_ext_of_openSubmoduleQuotients (R := R) N
  intro W hW
  rw [completedGroupAlgebraLiftToProfiniteModuleFun_quotient
      (R := R) (G := G) N f hf ⟨W, hW⟩,
    map_add,
    ← completedGroupAlgebraLiftToProfiniteModuleFun_quotient
      (R := R) (G := G) N f hf ⟨W, hW⟩ x,
    ← completedGroupAlgebraLiftToProfiniteModuleFun_quotient
      (R := R) (G := G) N f hf ⟨W, hW⟩ y]
  rfl

/--
The assembled profinite-target lift is compatible with scalar multiplication after all
open-submodule quotients.
-/
private theorem completedGroupAlgebraLiftToProfiniteModuleFun_smul
    (N : ProfiniteModule.{u, w} R.toProfiniteRing)
    (f : G → N) (hf : Continuous f)
    (r : R) (x : CompletedGroupAlgebraCarrier R G) :
    completedGroupAlgebraLiftToProfiniteModuleFun
        (R := R) (G := G) N f hf (r • x) =
      r • completedGroupAlgebraLiftToProfiniteModuleFun
        (R := R) (G := G) N f hf x := by
  apply profiniteModule_ext_of_openSubmoduleQuotients (R := R) N
  intro W hW
  rw [completedGroupAlgebraLiftToProfiniteModuleFun_quotient
      (R := R) (G := G) N f hf ⟨W, hW⟩,
    map_smul,
    ← completedGroupAlgebraLiftToProfiniteModuleFun_quotient
      (R := R) (G := G) N f hf ⟨W, hW⟩ x]
  rfl

/--
Existence half of Lemma 5.3.5(d): a continuous map from the profinite group \(G\) to a profinite
\(R\)-module extends to a continuous \(R\)-linear map out of \(\widehat{R[G]}\).
-/
private def completedGroupAlgebraLiftToProfiniteModule
    (N : ProfiniteModule.{u, w} R.toProfiniteRing)
    (f : G → N) (hf : Continuous f) :
    CompletedGroupAlgebraCarrier R G →L[R] N where
  toFun := completedGroupAlgebraLiftToProfiniteModuleFun (R := R) (G := G) N f hf
  map_add' := completedGroupAlgebraLiftToProfiniteModuleFun_add
    (R := R) (G := G) N f hf
  map_smul' := completedGroupAlgebraLiftToProfiniteModuleFun_smul
    (R := R) (G := G) N f hf
  cont := by
    apply continuous_of_forall_openSubmodule_quotient_continuous (R := R) N
    intro W hW
    have hEq : (fun x : CompletedGroupAlgebraCarrier R G =>
        Submodule.mkQ W
          (completedGroupAlgebraLiftToProfiniteModuleFun
            (R := R) (G := G) N f hf x)) =
        completedGroupAlgebraLiftToOpenSubmoduleQuotient
          (R := R) (G := G) N f hf W hW := by
      funext x
      exact completedGroupAlgebraLiftToProfiniteModuleFun_quotient
        (R := R) (G := G) N f hf ⟨W, hW⟩ x
    rw [hEq]
    exact (completedGroupAlgebraLiftToOpenSubmoduleQuotient
      (R := R) (G := G) N f hf W hW).continuous

/-- The profinite-target lift has the prescribed value on completed group-like elements. -/
@[simp]
private theorem completedGroupAlgebraLiftToProfiniteModule_apply_of
    (N : ProfiniteModule.{u, w} R.toProfiniteRing)
    (f : G → N) (hf : Continuous f)
    (g : G) :
    completedGroupAlgebraLiftToProfiniteModule
        (R := R) (G := G) N f hf (completedGroupAlgebraOf R G g) = f g :=
  completedGroupAlgebraLiftToProfiniteModuleFun_apply_of
    (R := R) (G := G) N f hf g

/--
Lemma 5.3.5(d): the completed group algebra satisfies the full universal property for maps into
profinite modules.
-/
private theorem completedGroupAlgebra_existsUnique_lift_to_profiniteModule
    (N : ProfiniteModule.{u, w} R.toProfiniteRing)
    (f : G → N) (hf : Continuous f) :
    ∃! F : CompletedGroupAlgebraCarrier R G →L[R] N,
      ∀ g : G, F (completedGroupAlgebraOf R G g) = f g := by
  let F := completedGroupAlgebraLiftToProfiniteModule (R := R) (G := G) N f hf
  refine ⟨F, ?_, ?_⟩
  · intro g
    exact completedGroupAlgebraLiftToProfiniteModule_apply_of
      (R := R) (G := G) N f hf g
  · intro K hK
    apply completedGroupAlgebraContinuousLinearMap_ext_of_basis (R := R) (G := G)
    intro g
    rw [completedGroupAlgebraLiftToProfiniteModule_apply_of, hK]

/-- The completed group algebra as an object in profinite modules over a bundled profinite
coefficient ring. -/
def completedGroupAlgebraProfiniteModule
    (Λ : ProfiniteCommRing.{u}) (P : ProfiniteGrp.{v}) :
    ProfiniteModule Λ.toProfiniteRing := by
  letI : CompactSpace (CompletedGroupAlgebraCarrier Λ P) :=
    completedGroupAlgebra_compactSpace (R := Λ) (G := P)
  letI : T2Space (CompletedGroupAlgebraCarrier Λ P) :=
    completedGroupAlgebra_t2Space (R := Λ) (G := P)
  letI : TotallyDisconnectedSpace (CompletedGroupAlgebraCarrier Λ P) :=
    completedGroupAlgebra_totallyDisconnectedSpace (R := Λ) (G := P)
  letI : Module Λ.toProfiniteRing (CompletedGroupAlgebraCarrier Λ P) :=
    instModuleCoeffCompletedGroupAlgebra (R := Λ) (G := P)
  letI : ContinuousSMul Λ.toProfiniteRing (CompletedGroupAlgebraCarrier Λ P) :=
    instContinuousSMulCompletedGroupAlgebra (R := Λ) (G := P)
  exact
    { toProfinite := Profinite.of (CompletedGroupAlgebraCarrier Λ P)
      addCommGroup := inferInstance
      module := instModuleCoeffCompletedGroupAlgebra (R := Λ) (G := P)
      isTopologicalAddGroup := inferInstance
      continuousSMul := inferInstance }

/-- Cross-universe extension property for the bundled completed group algebra. -/
theorem completedGroupAlgebraOf_hasFreeLiftTo
    (Λ : ProfiniteCommRing.{u}) (P : ProfiniteGrp.{v})
    (N : ProfiniteModule.{u, w} Λ.toProfiniteRing) :
    ProfiniteModule.HasFreeLiftTo
      (completedGroupAlgebraProfiniteModule Λ P)
      P.toProfinite (fun g => by
        change CompletedGroupAlgebraCarrier Λ P
        exact completedGroupAlgebraOf Λ P g) N := by
  let : Module Λ N := N.module
  dsimp [ProfiniteModule.HasFreeLiftTo, completedGroupAlgebraProfiniteModule,
    ProfiniteCommRing.toProfiniteRing]
  exact completedGroupAlgebra_existsUnique_lift_to_profiniteModule
    (R := Λ) (G := P) N

/--
Ribes--Zalesskii Lemma 5.3.5(d): \(\widehat{R[G]}\) is the free profinite \(R\)-module on the
profinite space G, with basis map \(g\mapsto [g]\) inside the completed group algebra.
-/
theorem completedGroupAlgebraOf_freeProfiniteModule
    (Λ : ProfiniteCommRing.{u}) (P : ProfiniteGrp.{v}) :
    (completedGroupAlgebraProfiniteModule Λ P).IsFreeOn
      P.toProfinite (fun g => by
        change CompletedGroupAlgebraCarrier Λ P
        exact completedGroupAlgebraOf Λ P g) := by
  refine ⟨continuous_completedGroupAlgebraOf (R := Λ) (G := P), ?_, ?_⟩
  · dsimp [completedGroupAlgebraProfiniteModule, ProfiniteCommRing.toProfiniteRing]
    exact completedGroupAlgebraOf_dense_span (R := Λ) (G := P)
  · intro N
    exact completedGroupAlgebraOf_hasFreeLiftTo Λ P N

end

end CompletedGroupAlgebra

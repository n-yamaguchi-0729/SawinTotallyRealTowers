import ProCGroups.CompletedGroupAlgebra.ProfiniteModules.FiniteGroupAlgebra.Augmentation.Completed

set_option autoImplicit false

/-!
# Group-like unit representations

Groups embed as units in their algebraic and completed group algebras. This file relates that
representation to augmentation and shows how restriction of scalars gives continuous group
actions on modules.
-/

open scoped Topology
open ProCGroups

namespace CompletedGroupAlgebra

universe u v w z

/-- The canonical embedding of a group into the units of its abstract group algebra. -/
noncomputable def groupAlgebraUnitRepresentation
    (R : Type u) (G : Type v) [CommRing R] [Group G] :
    G →* (MonoidAlgebra R G)ˣ where
  toFun g :=
    { val := MonoidAlgebra.of R G g
      inv := MonoidAlgebra.of R G g⁻¹
      val_inv := by
        rw [← map_mul, mul_inv_cancel, map_one]
      inv_val := by
        rw [← map_mul, inv_mul_cancel, map_one]}
  map_one' := by
    apply Units.ext
    exact map_one (MonoidAlgebra.of R G)
  map_mul' := by
    intro g h
    apply Units.ext
    exact map_mul (MonoidAlgebra.of R G) g h

/-- The value of the abstract unit representation is the corresponding group-like basis element. -/
@[simp]
theorem groupAlgebraUnitRepresentation_val
    (R : Type u) (G : Type v) [CommRing R] [Group G] (g : G) :
    ((groupAlgebraUnitRepresentation R G g : (MonoidAlgebra R G)ˣ) :
      MonoidAlgebra R G) = MonoidAlgebra.of R G g :=
  rfl

/--
A completed group algebra model receives the canonical unit representation of \(G\) through the
dense abstract group-algebra map.
-/
noncomputable def completedGroupAlgebraUnitRepresentation
    (R : Type u) (G : Type v) (RG : Type w) [CommRing R] [Group G] [Ring RG]
    (dense : MonoidAlgebra R G →+* RG) : G →* RGˣ :=
  (Units.map dense.toMonoidHom).comp (groupAlgebraUnitRepresentation R G)

/--
The value of the completed unit representation is the dense image of the group-like basis
element.
-/
@[simp]
theorem completedGroupAlgebraUnitRepresentation_val
    (R : Type u) (G : Type v) (RG : Type w) [CommRing R] [Group G] [Ring RG]
    (dense : MonoidAlgebra R G →+* RG) (g : G) :
    ((completedGroupAlgebraUnitRepresentation R G RG dense g : RGˣ) : RG) =
      dense (MonoidAlgebra.of R G g) :=
  rfl

/-- The completed unit representation has augmentation 1. -/
theorem completedGroupAlgebraAugmentation_unitRepresentation_val
    (R : Type u) (G : Type v) (RG : Type w) [CommRing R] [TopologicalSpace R]
    [Group G] [Ring RG] [TopologicalSpace RG]
    {dense : RingHom (MonoidAlgebra R G) RG}
    (haug : hasCompletedGroupAlgebraAugmentation R G RG dense) (g : G) :
    completedGroupAlgebraAugmentation R G RG haug
      ((completedGroupAlgebraUnitRepresentation R G RG dense g : RGˣ) : RG) = 1 := by
  have h := congrArg (fun f : RingHom (MonoidAlgebra R G) R => f (MonoidAlgebra.of R G g))
    (completedGroupAlgebraAugmentation_comp_dense R G RG haug)
  simpa using h

/-- The completed group-like difference \(g-1\) lies in the completed augmentation ideal. -/
theorem completedGroupAlgebra_unit_sub_one_mem_augmentationIdeal
    (R : Type u) (G : Type v) (RG : Type w) [CommRing R] [TopologicalSpace R]
    [Group G] [Ring RG] [TopologicalSpace RG]
    {dense : RingHom (MonoidAlgebra R G) RG}
    (haug : hasCompletedGroupAlgebraAugmentation R G RG dense) (g : G) :
    ((completedGroupAlgebraUnitRepresentation R G RG dense g : RGˣ) : RG) - 1 ∈
      completedGroupAlgebraAugmentationIdeal R G RG haug := by
  change completedGroupAlgebraAugmentation R G RG haug
      (((completedGroupAlgebraUnitRepresentation R G RG dense g : RGˣ) : RG) - 1) = 0
  rw [map_sub, completedGroupAlgebraAugmentation_unitRepresentation_val R G RG haug g, map_one,
    sub_self]

/--
Pull back a ring-module structure along a unit representation of a group. This is the algebraic
core of Proposition 5.3.6(a).
-/
@[reducible]
noncomputable def unitRepresentationDistribMulAction
    (G : Type u) (S : Type v) (A : Type w) [Group G] [Ring S] [AddCommGroup A]
    [Module S A] (ρ : G →* Sˣ) : DistribMulAction G A where
  smul g a := ((ρ g : Sˣ) : S) • a
  one_smul := by
    intro a
    change (((ρ (1 : G) : Sˣ) : S) • a) = a
    rw [map_one]
    exact one_smul S a
  mul_smul := by
    intro g h a
    change (((ρ (g * h) : Sˣ) : S) • a) =
      (((ρ g : Sˣ) : S) • (((ρ h : Sˣ) : S) • a))
    rw [map_mul]
    exact mul_smul (((ρ g : Sˣ) : S)) (((ρ h : Sˣ) : S)) a
  smul_zero := by
    intro g
    change (((ρ g : Sˣ) : S) • (0 : A)) = 0
    exact smul_zero (((ρ g : Sˣ) : S))
  smul_add := by
    intro g a b
    change (((ρ g : Sˣ) : S) • (a + b)) =
      ((ρ g : Sˣ) : S) • a + ((ρ g : Sˣ) : S) • b
    exact smul_add (((ρ g : Sˣ) : S)) a b

/--
The pulled-back action is continuous whenever the unit representation is continuous after
forgetting to the coefficient ring.
-/
theorem unitRepresentation_continuousSMul
    (G : Type u) (S : Type v) (A : Type w) [Group G] [TopologicalSpace G] [Ring S]
    [TopologicalSpace S] [AddCommGroup A] [TopologicalSpace A] [Module S A]
    [ContinuousSMul S A] (ρ : G →* Sˣ)
    (hρ : Continuous fun g : G => ((ρ g : Sˣ) : S)) :
    letI : DistribMulAction G A := unitRepresentationDistribMulAction G S A ρ
    ContinuousSMul G A := by
  let : DistribMulAction G A := unitRepresentationDistribMulAction G S A ρ
  refine ⟨?_⟩
  change Continuous fun p : G × A => ((ρ p.1 : Sˣ) : S) • p.2
  have hpair : Continuous fun p : G × A => (((ρ p.1 : Sˣ) : S), p.2) :=
    (hρ.comp continuous_fst).prodMk continuous_snd
  exact (show Continuous (fun p : S × A => p.1 • p.2) from continuous_smul).comp hpair

/--
Finite-stage version of Proposition 5.3.6(a): a module over the finite group algebra inherits
the continuous \(G\)-module structure coming from the canonical group-like units.
-/
theorem finiteGroupAlgebra_module_induces_continuous_gmodule
    (R : Type u) (G : Type v) (A : Type w) [CommRing R] [TopologicalSpace R]
    [Group G] [TopologicalSpace G] [Finite G] [DiscreteTopology G]
    [AddCommGroup A] [TopologicalSpace A] [Module (MonoidAlgebra R G) A]
    (hsmul : letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
      ContinuousSMul (MonoidAlgebra R G) A) :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    letI : DistribMulAction G A :=
      unitRepresentationDistribMulAction G (MonoidAlgebra R G) A
        (groupAlgebraUnitRepresentation R G)
    ContinuousSMul G A := by
  let : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  let : DistribMulAction G A :=
    unitRepresentationDistribMulAction G (MonoidAlgebra R G) A
      (groupAlgebraUnitRepresentation R G)
  refine ⟨?_⟩
  change Continuous fun p : G × A =>
    ((groupAlgebraUnitRepresentation R G p.1 : (MonoidAlgebra R G)ˣ) : MonoidAlgebra R G) • p.2
  exact hsmul.continuous_smul.comp₂
    (e := fun p : G × A =>
      ((groupAlgebraUnitRepresentation R G p.1 : (MonoidAlgebra R G)ˣ) : MonoidAlgebra R G))
    ((continuous_of_discreteTopology
      (f := fun g : G =>
        ((groupAlgebraUnitRepresentation R G g : (MonoidAlgebra R G)ˣ) :
          MonoidAlgebra R G))).comp continuous_fst)
    continuous_snd

/--
Proposition 5.3.6(a), model-independent form: a module over a completed group algebra inherits
the natural algebraic \(G\)-module structure.
-/
theorem completedGroupAlgebra_module_induces_gmodule
    (R : Type u) (G : Type v) (RG A : Type w) [CommRing R] [Group G] [Ring RG]
    [AddCommGroup A] [Module RG A] (dense : MonoidAlgebra R G →+* RG) :
    Nonempty (DistribMulAction G A) := by
  exact ⟨unitRepresentationDistribMulAction G RG A
    (completedGroupAlgebraUnitRepresentation R G RG dense)⟩

/--
Topological version of the unit-representation construction, once the canonical unit
representation is known to be continuous after forgetting to the completed group algebra model.
-/
theorem completedGroupAlgebra_module_induces_continuous_gmodule
    (R : Type u) (G : Type v) (RG A : Type w) [CommRing R] [TopologicalSpace G]
    [Group G] [Ring RG] [TopologicalSpace RG] [AddCommGroup A] [TopologicalSpace A]
    [Module RG A] [ContinuousSMul RG A] (dense : MonoidAlgebra R G →+* RG)
    (hdenseG : Continuous fun g : G => dense (MonoidAlgebra.of R G g)) :
    letI : DistribMulAction G A :=
      unitRepresentationDistribMulAction G RG A
        (completedGroupAlgebraUnitRepresentation R G RG dense)
    ContinuousSMul G A := by
  let : DistribMulAction G A :=
    unitRepresentationDistribMulAction G RG A
      (completedGroupAlgebraUnitRepresentation R G RG dense)
  exact unitRepresentation_continuousSMul G RG A
    (completedGroupAlgebraUnitRepresentation R G RG dense) (by simpa using hdenseG)

end CompletedGroupAlgebra

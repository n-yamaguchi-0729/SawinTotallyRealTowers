import ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebra
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

/-!
# Fox differential: coefficient rings — mod-\(n\) completed group algebra — in class — basic

The principal declarations in this module are:

- `ModNCompletedCoeff`
  The coefficient ring \(\mathbb{Z}/n\mathbb{Z}\) used in one residue-coefficient stage.
- `ModNCompletedGroupRing`
  The group ring \((\mathbb{Z}/n\mathbb{Z})[H]\) used in the residue-coefficient tower.
- `finite_modNCompletedGroupAlgebraStageInClass`
  Each \(C\)-indexed finite stage of the mod-\(n\) completed group algebra is finite.
- `modNCompletedGroupAlgebraTransitionInClass_of`
  The transition map sends a group-like basis element to the basis element supported at its image in
  the coarser quotient in the Fox differential construction.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u


variable (n : ℕ) [Fact (0 < n)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [Fact (0 < n)] in
/-- The coefficient ring \(\mathbb{Z}/n\mathbb{Z}\) used in one residue-coefficient stage. -/
abbrev ModNCompletedCoeff : Type := ZMod n

omit [Fact (0 < n)] in
/-- The group ring \((\mathbb{Z}/n\mathbb{Z})[H]\) used in the residue-coefficient tower. -/
abbrev ModNCompletedGroupRing (H : Type*) : Type _ :=
  MonoidAlgebra (ModNCompletedCoeff n) H

omit [Fact (0 < n)] in
/-- The residue-coefficient stage over a class-restricted finite quotient \(G/U\). -/
abbrev ModNCompletedGroupAlgebraStageInClass
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C) : Type _ :=
  ModNCompletedGroupRing n (CompletedGroupAlgebraQuotientInClass G C U)

/-- Each \(C\)-indexed finite stage of the mod-\(n\) completed group algebra is finite. -/
theorem finite_modNCompletedGroupAlgebraStageInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (U : CompletedGroupAlgebraIndexInClass G C) :
    Finite (ModNCompletedGroupAlgebraStageInClass n G C U) := by
  classical
  let : Finite (CompletedGroupAlgebraQuotientInClass G C U) :=
    C.finite (OrderDual.ofDual U).2
  let : Fintype (CompletedGroupAlgebraQuotientInClass G C U) := Fintype.ofFinite _
  let : DecidableEq (CompletedGroupAlgebraQuotientInClass G C U) := Classical.decEq _
  let : NeZero n := ⟨Nat.ne_of_gt (show 0 < n from Fact.out)⟩
  let : Fintype (ModNCompletedCoeff n) := Fintype.ofEquiv (Fin n) (ZMod.finEquiv n)
  let :
      Finite (CompletedGroupAlgebraQuotientInClass G C U → ModNCompletedCoeff n) := by
    let :
        Fintype (CompletedGroupAlgebraQuotientInClass G C U → ModNCompletedCoeff n) :=
      inferInstance
    exact Finite.of_fintype _
  let f :
      ModNCompletedGroupAlgebraStageInClass n G C U →
        CompletedGroupAlgebraQuotientInClass G C U → ModNCompletedCoeff n :=
    fun x q => x.coeff q
  refine Finite.of_injective f ?_
  intro x y hxy
  ext q
  exact congrFun hxy q

omit [Fact (0 < n)] in
/-- The transition map between class-restricted residue-coefficient stages. -/
def modNCompletedGroupAlgebraTransitionInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V) :
    ModNCompletedGroupAlgebraStageInClass n G C V →+*
      ModNCompletedGroupAlgebraStageInClass n G C U :=
  MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff n)
    (OpenNormalSubgroupInClass.map
      (C := C) (G := G)
      (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)

omit [Fact (0 < n)] in
/--
The transition map sends a group-like basis element to the basis element supported at its image
in the coarser quotient in the Fox differential construction.
-/
@[simp]
theorem modNCompletedGroupAlgebraTransitionInClass_of
    (C : ProCGroups.FiniteGroupClass.{u})
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V)
    (g : CompletedGroupAlgebraQuotientInClass G C V) :
    modNCompletedGroupAlgebraTransitionInClass n G C hUV
        (MonoidAlgebra.of (ModNCompletedCoeff n) _ g) =
      MonoidAlgebra.single
        ((OpenNormalSubgroupInClass.map
          (C := C) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) g) 1 := by
  classical
  change
    MonoidAlgebra.mapDomain
        (OpenNormalSubgroupInClass.map
          (C := C) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)
        (MonoidAlgebra.single g 1) =
      MonoidAlgebra.single
        ((OpenNormalSubgroupInClass.map
          (C := C) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) g) 1
  exact MonoidAlgebra.mapDomain_single

omit [Fact (0 < n)] in
/--
The \(C\)-indexed transition map between finite stages sends a singleton supported at a class of
the finer quotient to the singleton supported at its image in the coarser quotient, preserving
the coefficient.
-/
@[simp]
theorem modNCompletedGroupAlgebraTransitionInClass_single
    (C : ProCGroups.FiniteGroupClass.{u})
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V)
    (q : CompletedGroupAlgebraQuotientInClass G C V)
    (a : ModNCompletedCoeff n) :
    modNCompletedGroupAlgebraTransitionInClass n G C hUV
        (MonoidAlgebra.single q a) =
      MonoidAlgebra.single
        ((OpenNormalSubgroupInClass.map
          (C := C) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) q) a := by
  classical
  change
    MonoidAlgebra.mapDomain
        (OpenNormalSubgroupInClass.map
          (C := C) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)
        (MonoidAlgebra.single q a) =
      MonoidAlgebra.single
        ((OpenNormalSubgroupInClass.map
          (C := C) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) q) a
  exact MonoidAlgebra.mapDomain_single

omit [Fact (0 < n)] in
/--
The transition map attached to the identity refinement is the identity homomorphism in the Fox
differential construction.
-/
@[simp]
theorem modNCompletedGroupAlgebraTransitionInClass_id
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C) :
    modNCompletedGroupAlgebraTransitionInClass n G C (le_rfl : U ≤ U) = RingHom.id _ := by
  rw [modNCompletedGroupAlgebraTransitionInClass, OpenNormalSubgroupInClass.map_id]
  exact MonoidAlgebra.mapDomainRingHom_id
    (R := ModNCompletedCoeff n) (M := CompletedGroupAlgebraQuotientInClass G C U)

omit [Fact (0 < n)] in
/--
Class-indexed mod-\(n\) completed group-algebra transitions compose along quotient refinements.
-/
@[simp]
theorem modNCompletedGroupAlgebraTransitionInClass_comp
    (C : ProCGroups.FiniteGroupClass.{u})
    {U V W : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V) (hVW : V ≤ W) :
    (modNCompletedGroupAlgebraTransitionInClass n G C hUV).comp
        (modNCompletedGroupAlgebraTransitionInClass n G C hVW) =
      modNCompletedGroupAlgebraTransitionInClass n G C (hUV.trans hVW) := by
  unfold modNCompletedGroupAlgebraTransitionInClass
  exact
    (MonoidAlgebra.mapDomainRingHom_comp (R := ModNCompletedCoeff n)
      (OpenNormalSubgroupInClass.map
        (C := C) (G := G)
        (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)
      (OpenNormalSubgroupInClass.map
        (C := C) (G := G)
        (U := OrderDual.ofDual V) (V := OrderDual.ofDual W) hVW)).symm.trans
      (congrArg (MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff n))
        (OpenNormalSubgroupInClass.map_comp
          (C := C) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) (W := OrderDual.ofDual W)
          hUV hVW))

omit [Fact (0 < n)] in
/-- The class-restricted inverse system \(U \mapsto (\mathbb{Z}/n\mathbb{Z})[G/U]\). -/
def modNCompletedGroupAlgebraSystemInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    InverseSystem (I := CompletedGroupAlgebraIndexInClass G C) where
  X := ModNCompletedGroupAlgebraStageInClass n G C
  topologicalSpace := fun _ => ⊥
  map := fun {U V} hUV => modNCompletedGroupAlgebraTransitionInClass n G C hUV
  continuous_map := by
    intro U V hUV
    let : TopologicalSpace (ModNCompletedGroupAlgebraStageInClass n G C U) := ⊥
    let : TopologicalSpace (ModNCompletedGroupAlgebraStageInClass n G C V) := ⊥
    let : DiscreteTopology (ModNCompletedGroupAlgebraStageInClass n G C V) := ⟨rfl⟩
    exact continuous_of_discreteTopology
  map_id := by
    intro U
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (modNCompletedGroupAlgebraTransitionInClass_id n G C U)) x
  map_comp := by
    intro U V W hUV hVW
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (modNCompletedGroupAlgebraTransitionInClass_comp n G C hUV hVW)) x

omit [Fact (0 < n)] in
/--
The finite-stage transition map is surjective, with preimages obtained by lifting quotient
representatives.
-/
theorem modNCompletedGroupAlgebraTransitionInClass_surjective
    (C : ProCGroups.FiniteGroupClass.{u})
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V) :
    Function.Surjective (modNCompletedGroupAlgebraTransitionInClass n G C hUV) := by
  intro x
  induction x using MonoidAlgebra.induction with
  | zero =>
      exact ⟨0, map_zero _⟩
  | single_add q a x _ _ ih =>
      rcases OpenNormalSubgroupInClass.map_surjective
          (C := C) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV q with
        ⟨q', hq'⟩
      rcases ih with ⟨y, hy⟩
      refine
        ⟨(MonoidAlgebra.single q' a : ModNCompletedGroupAlgebraStageInClass n G C V) + y,
          ?_⟩
      have hsingle :
          modNCompletedGroupAlgebraTransitionInClass n G C hUV
              (MonoidAlgebra.single q' a) =
            MonoidAlgebra.single (OpenNormalSubgroupInClass.map hUV q') a := by
        unfold modNCompletedGroupAlgebraTransitionInClass
        exact MonoidAlgebra.mapDomain_single
      have hsingleTarget :
          modNCompletedGroupAlgebraTransitionInClass n G C hUV
              (MonoidAlgebra.single q' a) =
            (MonoidAlgebra.single q a :
              ModNCompletedGroupAlgebraStageInClass n G C U) :=
        hsingle.trans
          (congrArg (fun q₀ => MonoidAlgebra.single q₀ a) hq')
      calc
        modNCompletedGroupAlgebraTransitionInClass n G C hUV
              ((MonoidAlgebra.single q' a :
                ModNCompletedGroupAlgebraStageInClass n G C V) + y) =
            modNCompletedGroupAlgebraTransitionInClass n G C hUV
                (MonoidAlgebra.single q' a) +
              modNCompletedGroupAlgebraTransitionInClass n G C hUV y :=
          map_add _ _ _
        _ = MonoidAlgebra.single q a + x :=
          congrArg₂
            (fun u v : ModNCompletedGroupAlgebraStageInClass n G C U => u + v)
            hsingleTarget hy

omit [Fact (0 < n)] in
/--
The quotient map \((\mathbb{Z}/n\mathbb{Z})[G] \to (\mathbb{Z}/n\mathbb{Z})[G/U]\) for a
class-restricted stage.
-/
def modNCompletedGroupAlgebraStageMapInClass
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C) :
    ModNCompletedGroupRing n G →+* ModNCompletedGroupAlgebraStageInClass n G C U :=
  MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff n)
    (openNormalSubgroupInClassProj (C := C) (G := G) U)

omit [Fact (0 < n)] in
/--
The finite-stage group-like map sends a group element to the corresponding singleton basis
element in the quotient group algebra in the Fox differential construction.
-/
@[simp]
theorem modNCompletedGroupAlgebraStageMapInClass_of
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C) (g : G) :
    modNCompletedGroupAlgebraStageMapInClass n G C U
        (MonoidAlgebra.of (ModNCompletedCoeff n) _ g) =
      MonoidAlgebra.single (openNormalSubgroupInClassProj (C := C) (G := G) U g) 1 := by
  classical
  change
    MonoidAlgebra.mapDomain
        (openNormalSubgroupInClassProj (C := C) (G := G) U)
        (MonoidAlgebra.single g 1) =
      MonoidAlgebra.single
        (openNormalSubgroupInClassProj (C := C) (G := G) U g) 1
  exact MonoidAlgebra.mapDomain_single

omit [Fact (0 < n)] in
/--
The class-restricted mod-\(n\) completed group-algebra stage maps are compatible with quotient
refinement.
-/
@[simp]
theorem modNCompletedGroupAlgebraStageMapInClass_compatible
    (C : ProCGroups.FiniteGroupClass.{u})
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V) :
    (modNCompletedGroupAlgebraTransitionInClass n G C hUV).comp
        (modNCompletedGroupAlgebraStageMapInClass n G C V) =
      modNCompletedGroupAlgebraStageMapInClass n G C U := by
  unfold modNCompletedGroupAlgebraTransitionInClass modNCompletedGroupAlgebraStageMapInClass
  have hproj :
      (OpenNormalSubgroupInClass.map
        (C := C) (G := G)
        (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV).comp
          (openNormalSubgroupInClassProj (C := C) (G := G) V) =
        openNormalSubgroupInClassProj (C := C) (G := G) U := by
    ext g
    exact congrFun
      (openNormalSubgroupInClassProj_compatible
        (C := C) (G := G) U V hUV) g
  exact
    (MonoidAlgebra.mapDomainRingHom_comp (R := ModNCompletedCoeff n)
      (OpenNormalSubgroupInClass.map
        (C := C) (G := G)
        (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)
      (openNormalSubgroupInClassProj (C := C) (G := G) V)).symm.trans
      (congrArg (MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff n)) hproj)

omit [Fact (0 < n)] in
/-- Compatibility for a class-restricted residue-coefficient completed group algebra family. -/
def ModNCompletedGroupAlgebraCompatibleInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (x : ∀ U : CompletedGroupAlgebraIndexInClass G C,
      ModNCompletedGroupAlgebraStageInClass n G C U) : Prop :=
  (modNCompletedGroupAlgebraSystemInClass n G C).Compatible x

omit [Fact (0 < n)] in
/-- The class-restricted residue-coefficient completed group algebra as an inverse-limit subtype. -/
abbrev ModNCompletedGroupAlgebraInClass (C : ProCGroups.FiniteGroupClass.{u}) : Type _ :=
  {x : ∀ U : CompletedGroupAlgebraIndexInClass G C,
      ModNCompletedGroupAlgebraStageInClass n G C U //
    ModNCompletedGroupAlgebraCompatibleInClass n G C x}

omit [Fact (0 < n)] in
/--
The projection from the class-restricted residue-coefficient completed group algebra to a stage.
-/
def modNCompletedGroupAlgebraProjectionInClass
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C) :
    ModNCompletedGroupAlgebraInClass n G C →
      ModNCompletedGroupAlgebraStageInClass n G C U :=
  (modNCompletedGroupAlgebraSystemInClass n G C).projection U
end

end FoxDifferential

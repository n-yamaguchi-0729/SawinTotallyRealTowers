import ProCGroups.CompletedGroupAlgebra.Basic.AllFinite.Index
import ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraModN.InClass.Augmentation

set_option autoImplicit false

/-!
# Fox differential: coefficient rings — mod-\(n\) completed group algebra — system — basic

The principal declarations in this module are:

- `ModNCompletedGroupAlgebraStage`
  The mod-\(N\) completed group-algebra stage combines the finite group quotient with the
  coefficient quotient modulo \(N\).
- `modNCompletedGroupAlgebraTransition`
  The mod-\(n\) group-algebra transition from a finer finite quotient stage to a coarser stage.
- `modNCompletedGroupAlgebraTransition_of`
  The transition map sends a group-like basis element to the basis element supported at its image in
  the coarser quotient in the Fox differential construction.
- `modNCompletedGroupAlgebraTransition_id`
  The transition map attached to the identity refinement is the identity homomorphism in the Fox
  differential construction.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u


variable (n : ℕ) [Fact (0 < n)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [Fact (0 < n)] in
/--
The mod-\(N\) completed group-algebra stage combines the finite group quotient with the
coefficient quotient modulo \(N\).
-/
abbrev ModNCompletedGroupAlgebraStage (U :
    _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) : Type _ :=
  ModNCompletedGroupRing n (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U)

/-- Each mod-\(n\) completed group-algebra stage is finite. -/
instance instFiniteModNCompletedGroupAlgebraStage (U :
    _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) :
    Finite (ModNCompletedGroupAlgebraStage n G U) := by
  classical
  let : Finite (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U) :=
      (OrderDual.ofDual U).2
  let : Fintype (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U) :=
      Fintype.ofFinite _
  let : DecidableEq (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U) :=
      Classical.decEq _
  let : NeZero n := ⟨Nat.ne_of_gt (show 0 < n from Fact.out)⟩
  let : Fintype (ModNCompletedCoeff n) := Fintype.ofEquiv (Fin n) (ZMod.finEquiv n)
  let : Finite (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U →
      ModNCompletedCoeff n) := by
    let : Fintype (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U →
        ModNCompletedCoeff n) := inferInstance
    exact Finite.of_fintype _
  let f :
      ModNCompletedGroupAlgebraStage n G U →
        _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U →
          ModNCompletedCoeff n := fun x q => x.coeff q
  refine Finite.of_injective f ?_
  intro x y hxy
  ext q
  exact congrFun hxy q

omit [Fact (0 < n)] in
/-- The mod-\(n\) group-algebra transition from a finer finite quotient stage to a coarser stage. -/
def modNCompletedGroupAlgebraTransition
    {U V : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G} (hUV : U ≤ V) :
    ModNCompletedGroupAlgebraStage n G V →+* ModNCompletedGroupAlgebraStage n G U :=
  MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff n)
    (OpenNormalSubgroupInClass.map
      (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
      (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)

omit [Fact (0 < n)] in
/--
The transition map sends a group-like basis element to the basis element supported at its image
in the coarser quotient in the Fox differential construction.
-/
@[simp]
theorem modNCompletedGroupAlgebraTransition_of
    {U V : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G} (hUV : U ≤ V)
    (g : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G V) :
    modNCompletedGroupAlgebraTransition n G hUV (MonoidAlgebra.of (ModNCompletedCoeff n) _ g) =
      MonoidAlgebra.single ((OpenNormalSubgroupInClass.map
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
        (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) g) 1 := by
  classical
  change
    MonoidAlgebra.mapDomain
        (OpenNormalSubgroupInClass.map
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)
        (MonoidAlgebra.single g 1) =
      MonoidAlgebra.single
        ((OpenNormalSubgroupInClass.map
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) g) 1
  exact MonoidAlgebra.mapDomain_single

omit [Fact (0 < n)] in
/--
The transition map attached to the identity refinement is the identity homomorphism in the Fox
differential construction.
-/
@[simp]
theorem modNCompletedGroupAlgebraTransition_id (U :
    _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) :
    modNCompletedGroupAlgebraTransition n G (le_rfl : U ≤ U) = RingHom.id _ := by
  rw [modNCompletedGroupAlgebraTransition, OpenNormalSubgroupInClass.map_id]
  exact MonoidAlgebra.mapDomainRingHom_id
    (R := ModNCompletedCoeff n) (M := _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient
        G U)

omit [Fact (0 < n)] in
/-- Mod-\(n\) completed group-algebra transitions compose along quotient refinements. -/
@[simp]
theorem modNCompletedGroupAlgebraTransition_comp
    {U V W : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G} (hUV : U ≤ V) (hVW : V ≤
        W) :
    (modNCompletedGroupAlgebraTransition n G hUV).comp
        (modNCompletedGroupAlgebraTransition n G hVW) =
      modNCompletedGroupAlgebraTransition n G (hUV.trans hVW) := by
  erw [modNCompletedGroupAlgebraTransition, modNCompletedGroupAlgebraTransition,
    modNCompletedGroupAlgebraTransition, ← MonoidAlgebra.mapDomainRingHom_comp]
  congr 1
  exact OpenNormalSubgroupInClass.map_comp
    (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
    (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) (W := OrderDual.ofDual W)
    hUV hVW

omit [Fact (0 < n)] in
/--
The \(n\)-modular completed group-algebra transition sends a singleton to the singleton
supported at the induced quotient class with the same coefficient.
-/
theorem modNCompletedGroupAlgebraTransition_single_apply
    {U V : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G} (hUV : U ≤ V)
    (q : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G V)
    (a : ModNCompletedCoeff n) :
    modNCompletedGroupAlgebraTransition n G hUV (MonoidAlgebra.single q a) =
      MonoidAlgebra.single
        ((OpenNormalSubgroupInClass.map
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) q) a := by
  change
    MonoidAlgebra.mapDomain
        (OpenNormalSubgroupInClass.map
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)
        (MonoidAlgebra.single q a) =
      MonoidAlgebra.single
        ((OpenNormalSubgroupInClass.map
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) q) a
  exact MonoidAlgebra.mapDomain_single

omit [Fact (0 < n)] in
/--
The finite-stage transition map is surjective, with preimages obtained by lifting quotient
representatives.
-/
theorem modNCompletedGroupAlgebraTransition_surjective
    {U V : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G} (hUV : U ≤ V) :
    Function.Surjective (modNCompletedGroupAlgebraTransition n G hUV) := by
  intro x
  induction x using MonoidAlgebra.induction with
  | zero =>
      exact ⟨0, map_zero _⟩
  | single_add q a x _ _ ih =>
      rcases OpenNormalSubgroupInClass.map_surjective
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV q with
        ⟨q', hq'⟩
      rcases ih with ⟨y, hy⟩
      refine ⟨(MonoidAlgebra.single q' a : ModNCompletedGroupAlgebraStage n G V) + y, ?_⟩
      have hsingle :
          modNCompletedGroupAlgebraTransition n G hUV
              (MonoidAlgebra.single q' a) =
            MonoidAlgebra.single (OpenNormalSubgroupInClass.map hUV q') a := by
        exact modNCompletedGroupAlgebraTransition_single_apply
          (n := n) (G := G) hUV q' a
      have hsingleTarget :
          modNCompletedGroupAlgebraTransition n G hUV
              (MonoidAlgebra.single q' a) =
            (MonoidAlgebra.single q a : ModNCompletedGroupAlgebraStage n G U) :=
        hsingle.trans (congrArg (fun q₀ => MonoidAlgebra.single q₀ a) hq')
      calc
        modNCompletedGroupAlgebraTransition n G hUV
              ((MonoidAlgebra.single q' a : ModNCompletedGroupAlgebraStage n G V) + y) =
            modNCompletedGroupAlgebraTransition n G hUV (MonoidAlgebra.single q' a) +
              modNCompletedGroupAlgebraTransition n G hUV y := map_add _ _ _
        _ = MonoidAlgebra.single q a + x :=
          congrArg₂ (fun u v : ModNCompletedGroupAlgebraStage n G U => u + v)
            hsingleTarget hy

omit [Fact (0 < n)] in
/-- The quotient map \((\mathbb{Z}/n\mathbb{Z})[G] \to (\mathbb{Z}/n\mathbb{Z})[G/U]\). -/
def modNCompletedGroupAlgebraStageMap (U :
    _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) :
    ModNCompletedGroupRing n G →+* ModNCompletedGroupAlgebraStage n G U :=
  MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff n)
    (openNormalSubgroupInClassProj
      (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U)

omit [Fact (0 < n)] in
/--
The finite-stage group-like map sends a group element to the corresponding singleton basis
element in the quotient group algebra in the Fox differential construction.
-/
@[simp]
theorem modNCompletedGroupAlgebraStageMap_of
    (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) (g : G) :
    modNCompletedGroupAlgebraStageMap n G U (MonoidAlgebra.of (ModNCompletedCoeff n) _ g) =
      MonoidAlgebra.single (openNormalSubgroupInClassProj
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g) 1 := by
  classical
  change
    MonoidAlgebra.mapDomain
        (openNormalSubgroupInClassProj
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U)
        (MonoidAlgebra.single g 1) =
      MonoidAlgebra.single
        (openNormalSubgroupInClassProj
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g) 1
  exact MonoidAlgebra.mapDomain_single

omit [Fact (0 < n)] in
/-- The mod-\(n\) completed group-algebra stage maps are compatible with quotient refinement. -/
@[simp]
theorem modNCompletedGroupAlgebraStageMap_compatible
    {U V : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G} (hUV : U ≤ V) :
    (modNCompletedGroupAlgebraTransition n G hUV).comp
        (modNCompletedGroupAlgebraStageMap n G V) =
      modNCompletedGroupAlgebraStageMap n G U := by
  erw [modNCompletedGroupAlgebraTransition, modNCompletedGroupAlgebraStageMap,
    modNCompletedGroupAlgebraStageMap, ← MonoidAlgebra.mapDomainRingHom_comp]
  congr 1

omit [Fact (0 < n)] in
/-- The inverse system \(U \mapsto (\mathbb{Z}/n\mathbb{Z})[G/U]\). -/
def modNCompletedGroupAlgebraSystem :
    InverseSystem (I := _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) where
  X := ModNCompletedGroupAlgebraStage n G
  topologicalSpace := fun _ => ⊥
  map := fun {U V} hUV => modNCompletedGroupAlgebraTransition n G hUV
  continuous_map := by
    intro U V hUV
    let : TopologicalSpace (ModNCompletedGroupAlgebraStage n G U) := ⊥
    let : TopologicalSpace (ModNCompletedGroupAlgebraStage n G V) := ⊥
    let : DiscreteTopology (ModNCompletedGroupAlgebraStage n G V) := ⟨rfl⟩
    exact continuous_of_discreteTopology
  map_id := by
    intro U
    funext x
    exact congrFun
      (congrArg DFunLike.coe (modNCompletedGroupAlgebraTransition_id (n := n) (G := G) U)) x
  map_comp := by
    intro U V W hUV hVW
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (modNCompletedGroupAlgebraTransition_comp (n := n) (G := G) hUV hVW)) x

omit [Fact (0 < n)] in
/-- The inverse-limit object of the residue-coefficient stage tower. -/
abbrev ModNCompletedGroupAlgebra :=
  (modNCompletedGroupAlgebraSystem n G).inverseLimit

omit [Fact (0 < n)] in
/-- The projection from the residue-coefficient inverse limit to one finite stage. -/
abbrev modNCompletedGroupAlgebraProjection (U :
    _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) :
    ModNCompletedGroupAlgebra n G → ModNCompletedGroupAlgebraStage n G U :=
  (modNCompletedGroupAlgebraSystem n G).projection U


end

end FoxDifferential

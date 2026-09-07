import ProCGroups.InverseSystems.ProfiniteSpace
import ProCGroups.InverseSystems.CompatibilityAndSurjectivity
import ProCGroups.ProC.OpenNormalSubgroups.ProCGroup
import ProCGroups.Topologies.ContinuousMulEquiv
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits

set_option autoImplicit false

/-!
# Presenting pro-\(C\) groups as inverse limits

The canonical map to the inverse limit of all finite open-normal quotients is identified stage by
stage and shown to be a multiplicative equivalence. An exact quotient-basis condition then yields
the Hausdorff, totally disconnected, and pro-\(C\) structures.
-/

namespace ProCGroups.ProC

universe u v

variable {C : FiniteGroupClass.{u}}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace HasOpenNormalBasisInClass

/-! ## Compatibility with mathlib's finite-quotient presentation -/

/-- On open normal subgroups whose quotient lies in \(C\), mathlib's finite-quotient
functor uses the same transition maps as `openNormalSubgroupInClassSystem`. -/
@[simp] theorem toFiniteQuotientFunctor_map_apply_openNormalSubgroupInClass
    [CompactSpace G] [TotallyDisconnectedSpace G]
    {U V : OpenNormalSubgroupInClass C G}
    (hUV : U.1 ≤ V.1) (x : G ⧸ (U.1 : Subgroup G)) :
    (ProfiniteGrp.toFiniteQuotientFunctor (ProfiniteGrp.of G)).map
        (CategoryTheory.homOfLE hUV) x =
      OpenNormalSubgroupInClass.map (C := C) (G := G) (U := V) (V := U)
        (show (U.1 : Subgroup G) ≤ (V.1 : Subgroup G) from hUV) x := by
  rfl

/-- The coordinate of mathlib's canonical `ProfiniteGrp.toLimit` map at an in-class open
normal subgroup is the quotient projection used by `openNormalSubgroupInClassSystem`.

We state this through the explicit `.val` coordinate of `ProfiniteGrp.limit`; this avoids choosing
a second, potentially non-definitionally-equal `HasLimit` instance merely to name the projection. -/
@[simp] theorem toLimit_val_openNormalSubgroupInClass
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (U : OpenNormalSubgroupInClass C G) (g : G) :
    (ProfiniteGrp.toLimit (ProfiniteGrp.of G) g).val U.1 =
      openNormalSubgroupInClassProj (C := C) (G := G) (OrderDual.toDual U) g := by
  rfl

/--
A pro-\(C\) group is canonically the inverse limit of its quotients by open normal subgroups
whose quotients lie in \(C\).
-/
noncomputable def openNormalSubgroupInClassMulEquivInverseLimit
    [CompactSpace G] [T2Space G]
    (hForm : FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) :
    G ≃ₜ* (openNormalSubgroupInClassSystem C G).inverseLimit := by
  let S : InverseSystems.InverseSystem (I := OrderDual (OpenNormalSubgroupInClass C G)) :=
    openNormalSubgroupInClassSystem C G
  letI : Nonempty (OpenNormalSubgroupInClass C G) := openNormalSubgroupInClass_nonempty hG
  letI : ∀ U : OrderDual (OpenNormalSubgroupInClass C G), Group (S.X U) := fun U =>
    instGroupOpenNormalSubgroupInClassSystemX (C := C) (G := G) U
  letI : InverseSystems.IsGroupSystem S :=
    instIsGroupSystemOpenNormalSubgroupInClassSystem (C := C) (G := G)
  letI : ∀ U : OrderDual (OpenNormalSubgroupInClass C G), T2Space (S.X U) := fun U => by
    have : DiscreteTopology (S.X U) := by
      dsimp [S, openNormalSubgroupInClassSystem]
      exact QuotientGroup.discreteTopology
        (openNormalSubgroup_isOpen (G := G) ((OrderDual.ofDual U).1 : OpenNormalSubgroup G))
    infer_instance
  let φ : G →* S.inverseLimit :=
    { toFun := S.inverseLimitLift
        (fun U : OrderDual (OpenNormalSubgroupInClass C G) =>
          openNormalSubgroupInClassProj (C := C) (G := G) U)
        (openNormalSubgroupInClassProj_compatible (C := C) (G := G))
      map_one' := by
        apply S.ext
        intro i
        rfl
      map_mul' := by
        intro x y
        apply S.ext
        intro i
        rfl }
  have hφcont : Continuous φ :=
    S.continuous_inverseLimitLift
      (fun U : OrderDual (OpenNormalSubgroupInClass C G) =>
        openNormalSubgroupInClassProj (C := C) (G := G) U)
      (fun _ => continuous_quotient_mk')
      (openNormalSubgroupInClassProj_compatible (C := C) (G := G))
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have hmem :
        x⁻¹ * y ∈ iInf (fun U : OpenNormalSubgroupInClass C G => (U.1 : Subgroup G)) := by
      rw [Subgroup.mem_iInf]
      intro U
      let i : OrderDual (OpenNormalSubgroupInClass C G) := OrderDual.toDual U
      have hi :
          openNormalSubgroupInClassProj (C := C) (G := G) i x =
            openNormalSubgroupInClassProj (C := C) (G := G) i y := by
        have hcoord :=
          congrArg (fun z : S.inverseLimit => S.projection i z) hxy
        change
          openNormalSubgroupInClassProj (C := C) (G := G) i x =
            openNormalSubgroupInClassProj (C := C) (G := G) i y at hcoord
        exact hcoord
      change
        QuotientGroup.mk' (U.1 : Subgroup G) x =
          QuotientGroup.mk' (U.1 : Subgroup G) y at hi
      exact QuotientGroup.eq.1 hi
    have hone : x⁻¹ * y = 1 := by
      have : x⁻¹ * y ∈ (⊥ : Subgroup G) := by
        simpa [hG.iInf_openNormalSubgroupInClass_eq_bot] using hmem
      simpa using this
    calc
      x = x * 1 := by simp only [mul_one]
      _ = x * (x⁻¹ * y) := by rw [hone]
      _ = y := by simp only [mul_inv_cancel_left]
  have hφsurj : Function.Surjective φ :=
    InverseSystems.InverseSystem.surjective_inverseLimitLift (S := S)
      (fun U : OrderDual (OpenNormalSubgroupInClass C G) =>
        openNormalSubgroupInClassProj (C := C) (G := G) U)
      (fun _ => continuous_quotient_mk')
      (openNormalSubgroupInClassProj_compatible (C := C) (G := G))
      (fun U => openNormalSubgroupInClassProj_surjective (C := C) (G := G) U)
      (directed_openNormalSubgroupInClass (C := C) (G := G) hForm)
  exact ContinuousMulEquiv.ofBijectiveCompactToT2 φ hφcont ⟨hφinj, hφsurj⟩

/--
Under the canonical equivalence from a pro-\(C\) group to the inverse limit of its open-normal
\(C\)-quotients, the \(U\)-coordinate of an element is its quotient class modulo \(U\).
-/
@[simp] theorem openNormalSubgroupInClassMulEquivInverseLimit_projection
    [CompactSpace G] [T2Space G]
    (hForm : FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G)
    (U : OrderDual (OpenNormalSubgroupInClass C G)) (g : G) :
    (openNormalSubgroupInClassSystem C G).projection U
        (openNormalSubgroupInClassMulEquivInverseLimit
          (C := C) (G := G) hForm hG g) =
      openNormalSubgroupInClassProj (C := C) (G := G) U g := by
  exact (openNormalSubgroupInClassSystem C G).projection_inverseLimitLift_apply
    (fun (V : OrderDual (OpenNormalSubgroupInClass C G)) (x : G) =>
      (show (openNormalSubgroupInClassSystem C G).X V from
        openNormalSubgroupInClassProj (C := C) (G := G) V x))
    (openNormalSubgroupInClassProj_compatible (C := C) (G := G)) U g

/-- The concrete pro-\(C\) presentation and mathlib's finite-quotient presentation have
identical canonical coordinates. The generic concrete/categorical-limit comparison is
`InverseSystems.InverseSystem.profiniteGrpConeIsLimit`. -/
theorem openNormalSubgroupInClassMulEquivInverseLimit_projection_eq_toLimit_val
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hForm : FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G)
    (U : OpenNormalSubgroupInClass C G) (g : G) :
    (openNormalSubgroupInClassSystem C G).projection (OrderDual.toDual U)
        (openNormalSubgroupInClassMulEquivInverseLimit
          (C := C) (G := G) hForm hG g) =
      (ProfiniteGrp.toLimit (ProfiniteGrp.of G) g).val U.1 := by
  rw [openNormalSubgroupInClassMulEquivInverseLimit_projection,
    toLimit_val_openNormalSubgroupInClass]

/--
A pro-\(C\) group is topologically isomorphic to an inverse limit of finite groups in \(C\),
realized using the quotient system indexed by the open normal subgroups whose quotients lie in
\(C\).
-/
theorem isomorphic_to_inverseLimit_finiteGroupsInClass
    [CompactSpace G] [T2Space G]
    (hForm : FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) :
    let S := openNormalSubgroupInClassSystem C G
    (∀ U : OrderDual (OpenNormalSubgroupInClass C G), C (S.X U) ∧ Finite (S.X U)) ∧
      Nonempty (G ≃ₜ* S.inverseLimit) := by
  let S := openNormalSubgroupInClassSystem C G
  refine ⟨?_, ⟨openNormalSubgroupInClassMulEquivInverseLimit (C := C) (G := G) hForm hG⟩⟩
  intro U
  dsimp [S, openNormalSubgroupInClassSystem]
  refine ⟨(OrderDual.ofDual U).2, ?_⟩
  exact C.finite (OrderDual.ofDual U).2

end HasOpenNormalBasisInClass

/--
Existence of an open-normal subgroup basis whose quotients lie in \(C\) and whose quotient
presentations are exact.
-/
def HasExactOpenNormalQuotientBasisInClass (C : FiniteGroupClass.{u})
    (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  CompactSpace G ∧
    ∃ ι : Type u, ∃ U : ι → OpenNormalSubgroup G,
      (∀ i, C (G ⧸ (U i : Subgroup G))) ∧
      (∀ W : Set G, IsOpen W → (1 : G) ∈ W →
        ∃ i, (((U i : Subgroup G) : Set G)) ⊆ W) ∧
      iInf (fun i => (U i : Subgroup G)) = (⊥ : Subgroup G)

/-- An open-normal family with trivial intersection makes the group Hausdorff. -/
theorem t2Space_of_exactOpenNormalQuotientBasisInClass
    (hC : HasExactOpenNormalQuotientBasisInClass C G) : T2Space G := by
  rcases hC with ⟨_, ι, U, _, _, hInf⟩
  refine ⟨?_⟩
  intro x y hxy
  have hxy' : x⁻¹ * y ≠ 1 := by
    intro h1
    apply hxy
    simpa using inv_mul_eq_one.mp h1
  have hsep : ∃ i : ι, x⁻¹ * y ∉ (U i : Subgroup G) := by
    by_contra hsep
    have hxall : ∀ i : ι, x⁻¹ * y ∈ (U i : Subgroup G) := by
      intro i
      by_contra hxyi
      exact hsep ⟨i, hxyi⟩
    have hxinf : x⁻¹ * y ∈ iInf (fun i => (U i : Subgroup G)) := by
      simpa [Subgroup.mem_iInf] using hxall
    have hxbot : x⁻¹ * y ∈ (⊥ : Subgroup G) := by
      simpa [hInf] using hxinf
    exact hxy' (by simpa using hxbot)
  rcases hsep with ⟨i, hxyi⟩
  have hclopenCoset :
      ∀ z : G, IsClopen {g : G | z⁻¹ * g ∈ (U i : Subgroup G)} := by
    intro z
    let f : G → G := fun g => z⁻¹ * g
    have hf : Continuous f := continuous_const.mul continuous_id
    refine ⟨?_, ?_⟩
    · change IsClosed (f ⁻¹' ((U i).toOpenSubgroup : Set G))
      exact (openSubgroup_isClosed (G := G) (U i).toOpenSubgroup).preimage hf
    · change IsOpen (f ⁻¹' ((U i).toOpenSubgroup : Set G))
      exact (openSubgroup_isOpen (G := G) (U i).toOpenSubgroup).preimage hf
  refine ⟨{g : G | x⁻¹ * g ∈ (U i : Subgroup G)},
    {g : G | y⁻¹ * g ∈ (U i : Subgroup G)}, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hclopenCoset x).2
  · exact (hclopenCoset y).2
  · simp only [OpenSubgroup.mem_toSubgroup, Set.mem_ofPred_eq, inv_mul_cancel, one_mem]
  · simp only [OpenSubgroup.mem_toSubgroup, Set.mem_ofPred_eq, inv_mul_cancel, one_mem]
  · refine Set.disjoint_left.2 ?_
    intro g hx hg
    apply hxyi
    have hmul :
        (x⁻¹ * g) * (y⁻¹ * g)⁻¹ ∈ (U i : Subgroup G) :=
      (U i).mul_mem hx ((U i).inv_mem hg)
    simpa [mul_assoc] using hmul

/-- An open-normal family yields a clopen basis and total disconnectedness. -/
theorem totallyDisconnectedSpace_of_exactOpenNormalQuotientBasisInClass
    (hC : HasExactOpenNormalQuotientBasisInClass C G) : TotallyDisconnectedSpace G := by
  have hC' := hC
  rcases hC' with ⟨_, ι, U, _, hbasis, _⟩
  have : T2Space G := t2Space_of_exactOpenNormalQuotientBasisInClass (C := C) hC
  have hclopenBasis : TopologicalSpace.IsTopologicalBasis {s : Set G | IsClopen s} := by
    refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · intro s hs
      exact hs.2
    · intro x W hxW hW
      let W₁ : Set G := (fun g : G => x * g) ⁻¹' W
      have hW₁ : IsOpen W₁ := hW.preimage (continuous_const.mul continuous_id)
      have h1W₁ : (1 : G) ∈ W₁ := by
        simpa [W₁] using hxW
      rcases hbasis W₁ hW₁ h1W₁ with ⟨i, hi⟩
      have hclopenCoset : IsClopen {g : G | x⁻¹ * g ∈ (U i : Subgroup G)} := by
        let f : G → G := fun g => x⁻¹ * g
        have hf : Continuous f := continuous_const.mul continuous_id
        refine ⟨?_, ?_⟩
        · change IsClosed (f ⁻¹' ((U i).toOpenSubgroup : Set G))
          exact (openSubgroup_isClosed (G := G) (U i).toOpenSubgroup).preimage hf
        · change IsOpen (f ⁻¹' ((U i).toOpenSubgroup : Set G))
          exact (openSubgroup_isOpen (G := G) (U i).toOpenSubgroup).preimage hf
      refine ⟨{g : G | x⁻¹ * g ∈ (U i : Subgroup G)}, ?_, by simp only
          [OpenSubgroup.mem_toSubgroup, Set.mem_ofPred_eq, inv_mul_cancel, one_mem], ?_⟩
      · exact hclopenCoset
      · intro g hg
        have hxgW₁ : x⁻¹ * g ∈ W₁ := hi hg
        simpa [W₁, mul_assoc] using hxgW₁
  exact InverseSystems.totallyDisconnectedSpace_of_t2_basis_clopen G hclopenBasis

omit [IsTopologicalGroup G] in
/-- An exact open-normal quotient basis in \(C\) implies `HasOpenNormalBasisInClass C G`. This
direction needs no formation closure because the chosen basis already supplies the required
open-normal quotients in \(C\). -/
theorem hasOpenNormalBasisInClass_of_hasExactOpenNormalQuotientBasisInClass
    (hC : HasExactOpenNormalQuotientBasisInClass C G) : HasOpenNormalBasisInClass C G := by
  rcases hC with ⟨_, ι, U, hCU, hbasis, _⟩
  intro W hW h1W
  rcases hbasis W hW h1W with ⟨i, hiW⟩
  exact ⟨U i, hiW, hCU i⟩

end ProCGroups.ProC

import ProCGroups.InverseSystems.FiniteStageFactorization
import ProCGroups.ProC.InverseLimits.FiniteQuotients
import ProCGroups.ProC.OpenNormalSubgroups.FilteredFamilies
import ProCGroups.Topologies.ContinuousMulEquiv

set_option autoImplicit false

/-!
# Inverse limits and closed-normal quotients

This file equips inverse limits of finite topological group systems with their canonical topology
and proves the pro-\(C\) basis property for the resulting limits and for quotients by closed
normal subgroups.
-/

open Set
open scoped Topology Pointwise

namespace ProCGroups.ProC

universe u v

open InverseSystems

section

variable {C : FiniteGroupClass.{u}}
variable {I : Type u} [Preorder I] [Nonempty I]
variable (S : InverseSystems.InverseSystem (I := I))
/--
The constructed object carries the topological space structure inherited from its construction.
-/
instance instTopologicalSpaceX (i : I) : TopologicalSpace (S.X i) := S.topologicalSpace i
variable [∀ i, Group (S.X i)]
variable [∀ i, IsTopologicalGroup (S.X i)]
variable [InverseSystems.IsGroupSystem S]

/-- A directed inverse limit of pro-\(C\) groups is pro-\(C\). -/
theorem inverseLimit
    [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    [∀ i, TotallyDisconnectedSpace (S.X i)]
    (hIso : FiniteGroupClass.IsomClosed C)
    (hQuot : FiniteGroupClass.QuotientClosed C)
    (hdir : Directed (· ≤ ·) (id : I → I))
    (hX : ∀ i, HasOpenNormalBasisInClass C (S.X i)) :
    HasOpenNormalBasisInClass C S.inverseLimit := by
  refine HasOpenNormalBasisInClass.of_allOpenNormalQuotients (C := C) ?_
  intro U
  let β : S.inverseLimit →* S.inverseLimit ⧸ (U : Subgroup S.inverseLimit) :=
    QuotientGroup.mk' (U : Subgroup S.inverseLimit)
  rcases InverseSystems.InverseSystem.factors_through_projection_finite_group_hom
      (S := S) hdir β continuous_quotient_mk' with ⟨k, βk, hβk_continuous, hβfac⟩
  have hβk_surj : Function.Surjective βk := by
    intro q
    rcases QuotientGroup.mk'_surjective (U : Subgroup S.inverseLimit) q with ⟨x, rfl⟩
    refine ⟨S.projection k x, ?_⟩
    change βk (S.projection k x) = β x
    exact
      (congrArg
        (fun f : S.inverseLimit → S.inverseLimit ⧸ (U : Subgroup S.inverseLimit) => f x)
        hβfac).symm
  have hker_closed : IsClosed ((βk.ker : Subgroup (S.X k)) : Set (S.X k)) := by
    change IsClosed {y : S.X k | βk y = 1}
    exact isClosed_eq hβk_continuous continuous_const
  have hker_finite : Finite (S.X k ⧸ βk.ker) := by
    exact Finite.of_injective (QuotientGroup.quotientKerEquivOfSurjective βk hβk_surj)
      (QuotientGroup.quotientKerEquivOfSurjective βk hβk_surj).injective
  have hker_open : IsOpen ((βk.ker : Subgroup (S.X k)) : Set (S.X k)) :=
    (subgroup_isOpen_iff_isClosed_finite_quotient (G := S.X k) (U := βk.ker)).2
      ⟨hker_closed, hker_finite⟩
  let V : OpenNormalSubgroup (S.X k) :=
    { toOpenSubgroup := ⟨βk.ker, hker_open⟩
      isNormal' := inferInstance }
  have hQV : C (S.X k ⧸ (V : Subgroup (S.X k))) :=
    HasOpenNormalBasisInClass.hasAllOpenNormalQuotientsInClass_of_basis_of_quotientClosed
      hIso hQuot (hX k) V
  exact hIso ⟨QuotientGroup.quotientKerEquivOfSurjective βk hβk_surj⟩ hQV

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/--
If \(G\) is pro-\(C\) and \(C\) is closed under quotients, then every quotient of \(G\) by a
closed normal subgroup is again pro-\(C\).
-/
theorem quotient_closedNormalSubgroup
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hIso : FiniteGroupClass.IsomClosed C)
    (hQuot : FiniteGroupClass.QuotientClosed C)
    (hG : HasOpenNormalBasisInClass C G)
    (K : Subgroup G) [K.Normal] (hK : IsClosed (K : Set G)) :
    HasOpenNormalBasisInClass C (G ⧸ K) := by
  classical
  let topU : OpenNormalSubgroup G :=
    { toOpenSubgroup := ⟨⊤, isOpen_univ⟩
      isNormal' := inferInstance }
  let : Nonempty (OrderDual {U : OpenNormalSubgroup G // K ≤ (U : Subgroup G)}) :=
    ⟨OrderDual.toDual ⟨topU, le_top⟩⟩
  let S : InverseSystems.InverseSystem
      (I := OrderDual {U : OpenNormalSubgroup G // K ≤ (U : Subgroup G)}) := {
    X := fun U => G ⧸ (((OrderDual.ofDual U).1 : OpenNormalSubgroup G) : Subgroup G)
    topologicalSpace := fun _ => inferInstance
    map := fun {U V} hUV =>
      QuotientGroup.map
        (((OrderDual.ofDual V).1 : OpenNormalSubgroup G) : Subgroup G)
        (((OrderDual.ofDual U).1 : OpenNormalSubgroup G) : Subgroup G)
        (MonoidHom.id G)
        hUV
    continuous_map := by
      intro U V hUV
      exact continuous_of_discreteTopology
    map_id := by
      intro U
      funext x
      exact QuotientGroup.map_id_apply ((OrderDual.ofDual U).1 : Subgroup G)
        (h := fun _ hx => hx) x
    map_comp := by
      intro U V W hUV hVW
      funext x
      simpa [Function.comp] using congrArg (fun f => f x)
        (QuotientGroup.map_comp_map
          (N := (((OrderDual.ofDual W).1 : OpenNormalSubgroup G) : Subgroup G))
          (M := (((OrderDual.ofDual V).1 : OpenNormalSubgroup G) : Subgroup G))
          (O := (((OrderDual.ofDual U).1 : OpenNormalSubgroup G) : Subgroup G))
          (f := MonoidHom.id G) (g := MonoidHom.id G) hVW hUV) }
  let : InverseSystems.IsGroupSystem S := {
    map_one := by
      intro i j hij
      rfl
    map_mul := by
      intro i j hij x y
      change
        QuotientGroup.map
            ((((OrderDual.ofDual j).1 : OpenNormalSubgroup G) : Subgroup G))
            ((((OrderDual.ofDual i).1 : OpenNormalSubgroup G) : Subgroup G))
            (MonoidHom.id G) hij (x * y) =
          QuotientGroup.map
              ((((OrderDual.ofDual j).1 : OpenNormalSubgroup G) : Subgroup G))
              ((((OrderDual.ofDual i).1 : OpenNormalSubgroup G) : Subgroup G))
              (MonoidHom.id G) hij x *
            QuotientGroup.map
              ((((OrderDual.ofDual j).1 : OpenNormalSubgroup G) : Subgroup G))
              ((((OrderDual.ofDual i).1 : OpenNormalSubgroup G) : Subgroup G))
              (MonoidHom.id G) hij y
      exact
        (QuotientGroup.map
          ((((OrderDual.ofDual j).1 : OpenNormalSubgroup G) : Subgroup G))
          ((((OrderDual.ofDual i).1 : OpenNormalSubgroup G) : Subgroup G))
          (MonoidHom.id G) hij).map_mul x y
    map_inv := by
      intro i j hij x
      change
        QuotientGroup.map
            ((((OrderDual.ofDual j).1 : OpenNormalSubgroup G) : Subgroup G))
            ((((OrderDual.ofDual i).1 : OpenNormalSubgroup G) : Subgroup G))
            (MonoidHom.id G) hij x⁻¹ =
          (QuotientGroup.map
            ((((OrderDual.ofDual j).1 : OpenNormalSubgroup G) : Subgroup G))
            ((((OrderDual.ofDual i).1 : OpenNormalSubgroup G) : Subgroup G))
            (MonoidHom.id G) hij x)⁻¹
      exact
        (QuotientGroup.map
          ((((OrderDual.ofDual j).1 : OpenNormalSubgroup G) : Subgroup G))
          ((((OrderDual.ofDual i).1 : OpenNormalSubgroup G) : Subgroup G))
          (MonoidHom.id G) hij).map_inv x }
  have hdir :
      Directed (· ≤ ·) (id : OrderDual {U : OpenNormalSubgroup G // K ≤ (U : Subgroup G)} →
        OrderDual {U : OpenNormalSubgroup G // K ≤ (U : Subgroup G)}) := by
    intro i j
    refine ⟨OrderDual.toDual ⟨(OrderDual.ofDual i).1 ⊓ (OrderDual.ofDual j).1, ?_⟩, ?_, ?_⟩
    · intro x hx
      exact ⟨(OrderDual.ofDual i).2 hx, (OrderDual.ofDual j).2 hx⟩
    · exact show
        (((OrderDual.ofDual i).1 ⊓ (OrderDual.ofDual j).1 : OpenNormalSubgroup G) : Subgroup G) ≤
          ((OrderDual.ofDual i).1 : Subgroup G) from inf_le_left
    · exact show
        (((OrderDual.ofDual i).1 ⊓ (OrderDual.ofDual j).1 : OpenNormalSubgroup G) : Subgroup G) ≤
          ((OrderDual.ofDual j).1 : Subgroup G) from inf_le_right
  have hX :
      ∀ i : OrderDual {U : OpenNormalSubgroup G // K ≤ (U : Subgroup G)},
          HasOpenNormalBasisInClass C (S.X i) :=
      by
    intro i
    let U : OpenNormalSubgroup G := (OrderDual.ofDual i).1
    exact HasOpenNormalBasisInClass.of_finite_discrete (C := C) (G := G ⧸ (U : Subgroup G))
      hQuot
      (HasOpenNormalBasisInClass.hasAllOpenNormalQuotientsInClass_of_basis_of_quotientClosed
        hIso hQuot hG U)
  let : ∀ i : OrderDual {U : OpenNormalSubgroup G // K ≤ (U : Subgroup G)},
      Finite (S.X i) := fun i => by
    dsimp [S]
    exact openNormalSubgroup_finiteQuotient (G := G) (OrderDual.ofDual i).1
  let : ∀ i : OrderDual {U : OpenNormalSubgroup G // K ≤ (U : Subgroup G)},
      DiscreteTopology (S.X i) := fun i => by
    dsimp [S]
    exact QuotientGroup.discreteTopology
      (openNormalSubgroup_isOpen (G := G) (OrderDual.ofDual i).1)
  have hSinv : HasOpenNormalBasisInClass C S.inverseLimit :=
    inverseLimit (C := C) (S := S) hIso hQuot hdir hX
  let ψ :
      ∀ i : OrderDual {U : OpenNormalSubgroup G // K ≤ (U : Subgroup G)},
        G ⧸ K → S.X i := fun i =>
          QuotientGroup.map
            K
            (((OrderDual.ofDual i).1 : OpenNormalSubgroup G) : Subgroup G)
            (MonoidHom.id G)
            (OrderDual.ofDual i).2
  have hψcont :
      ∀ i : OrderDual {U : OpenNormalSubgroup G // K ≤ (U : Subgroup G)}, Continuous (ψ i) := by
    intro i
    let U : Subgroup G := (((OrderDual.ofDual i).1 : OpenNormalSubgroup G) : Subgroup G)
    have hmk : Continuous (QuotientGroup.mk' U : G → G ⧸ U) := continuous_quotient_mk'
    have hconst :
        ∀ a b : G, QuotientGroup.leftRel K a b →
          (QuotientGroup.mk' U) a = (QuotientGroup.mk' U) b := by
      intro a b hab
      apply QuotientGroup.eq.2
      exact (OrderDual.ofDual i).2 (by simpa using (QuotientGroup.leftRel_apply.mp hab))
    refine (QuotientGroup.isQuotientMap_mk K).continuous_iff.2 ?_
    change Continuous fun g : G => QuotientGroup.mk' U g
    exact hmk
  have hψcompat : S.CompatibleMaps ψ := by
    intro i j hij
    funext x
    rcases QuotientGroup.mk'_surjective K x with ⟨g, rfl⟩
    rfl
  let φ : G ⧸ K →* S.inverseLimit := {
    toFun := S.inverseLimitLift ψ hψcompat
    map_one' := by
      apply S.ext
      intro i
      rfl
    map_mul' := by
      intro x y
      apply S.ext
      intro i
      rcases QuotientGroup.mk'_surjective K x with ⟨gx, rfl⟩
      rcases QuotientGroup.mk'_surjective K y with ⟨gy, rfl⟩
      rfl }
  have hφcont : Continuous φ := S.continuous_inverseLimitLift ψ hψcont hψcompat
  have hφsurj : Function.Surjective φ := by
    exact InverseSystems.InverseSystem.surjective_inverseLimitLift
      (S := S) ψ hψcont hψcompat
      (fun i => by
        intro x
        rcases QuotientGroup.mk'_surjective
            ((((OrderDual.ofDual i).1 : OpenNormalSubgroup G) : Subgroup G)) x with ⟨g, rfl⟩
        exact ⟨QuotientGroup.mk' K g, rfl⟩)
      hdir
  have hφinj : Function.Injective φ := by
    intro x y hxy
    rcases QuotientGroup.mk'_surjective K x with ⟨gx, rfl⟩
    rcases QuotientGroup.mk'_surjective K y with ⟨gy, rfl⟩
    apply QuotientGroup.eq.2
    have hmem :
        ∀ U : OpenNormalSubgroup G, K ≤ (U : Subgroup G) → gx⁻¹ * gy ∈ (U : Subgroup G) := by
      intro U hKU
      let i : OrderDual {U : OpenNormalSubgroup G // K ≤ (U : Subgroup G)} :=
        OrderDual.toDual ⟨U, hKU⟩
      have hi : ψ i (QuotientGroup.mk' K gx) = ψ i (QuotientGroup.mk' K gy) := by
        have hcoord := congrArg (fun z : S.inverseLimit => S.projection i z) hxy
        change ψ i (QuotientGroup.mk' K gx) = ψ i (QuotientGroup.mk' K gy) at hcoord
        exact hcoord
      exact QuotientGroup.eq.mp hi
    let HC : ClosedSubgroup G := { toSubgroup := K, isClosed' := hK }
    have hx :
        gx⁻¹ * gy ∈
          sInf {N : Subgroup G | IsOpen (N : Set G) ∧ K ≤ N ∧ N.Normal} := by
      simp only [Subgroup.mem_sInf, Set.mem_ofPred_eq]
      intro N hN
      let U : OpenNormalSubgroup G :=
        { toOpenSubgroup := ⟨N, hN.1⟩
          isNormal' := hN.2.2 }
      exact hmem U hN.2.1
    have hxK : gx⁻¹ * gy ∈ K := by
      have hEq :
          (K : Subgroup G) =
            sInf {N : Subgroup G | IsOpen (N : Set G) ∧ K ≤ N ∧ N.Normal} :=
        closedSubgroup_eq_sInf_openNormal (G := G) HC
      exact hEq.symm ▸ hx
    exact hxK
  let e : G ⧸ K ≃ₜ* S.inverseLimit :=
    ContinuousMulEquiv.ofBijectiveCompactToT2 φ hφcont ⟨hφinj, hφsurj⟩
  exact HasOpenNormalBasisInClass.ofContinuousMulEquiv (C := C) hSinv e.symm

end

end ProCGroups.ProC

import ProCGroups.ProC.MaximalQuotients.ResidualCore
import ProCGroups.ProC.Quotients.ClosedNormal
import ProCGroups.ProC.Subgroups.Products

set_option autoImplicit false

/-!
# The quotient by the pro-C residual core

For a formation `C`, the quotient by the intersection of all kernels with pro-`C` quotient is
itself pro-`C`.  The proof realizes the residual quotient as a subdirect product of all the
pro-`C` quotients occurring in the definition of the residual core.
-/

open Set

namespace ProCGroups.ProC

universe u

/-- The quotient by the pro-`C` residual core has an open-normal quotient basis in `C`. -/
theorem proCResidualCoreQuotient_hasOpenNormalBasisInClass
    {C : FiniteGroupClass.{u}}
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hForm : FiniteGroupClass.Formation C) :
    HasOpenNormalBasisInClass C (G ⧸ proCResidualCore C G) := by
  classical
  let R : Subgroup G := proCResidualCore C G
  let I : Type u := ProCQuotientKernel C G
  let Q : I → Type u := fun N => G ⧸ N.toSubgroup
  have hRclosed : IsClosed (R : Set G) := by
    simpa [R] using proCResidualCore_isClosed C G
  have : TotallyDisconnectedSpace (G ⧸ R) :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal R hRclosed
  have : ∀ N : I, IsClosed (N.toSubgroup : Set G) := fun N => N.isClosed'
  have : ∀ N : I, TotallyDisconnectedSpace (Q N) := fun N => by
    dsimp [Q]
    exact ProCGroups.totallyDisconnectedSpace_quotient_closedNormal N.toSubgroup N.isClosed'
  have hRle : ∀ N : I, R ≤ N.toSubgroup := by
    intro N
    change proCResidualCore C G ≤ N.toSubgroup
    rw [proCResidualCore]
    exact sInf_le (Set.mem_range_self N)
  let π : ∀ N : I, G ⧸ R →ₜ* Q N := fun N =>
    QuotientGroup.mapₜ R N.toSubgroup (ContinuousMonoidHom.id G) (by
      intro x hx
      exact hRle N hx)
  let φ : G ⧸ R →* ∀ N : I, Q N :=
    { toFun := fun x N => π N x
      map_one' := by
        funext N
        exact (π N).map_one
      map_mul' := by
        intro x y
        funext N
        exact (π N).map_mul x y }
  have hφcont : Continuous φ := by
    exact continuous_pi fun N => (π N).continuous_toFun
  have hφinj : Function.Injective φ := by
    intro x y hxy
    rcases QuotientGroup.mk'_surjective R x with ⟨a, rfl⟩
    rcases QuotientGroup.mk'_surjective R y with ⟨b, rfl⟩
    apply (QuotientGroup.eq_iff_div_mem (N := R)).2
    change a / b ∈ proCResidualCore C G
    rw [proCResidualCore, Subgroup.mem_sInf]
    intro K hK
    rcases hK with ⟨N, rfl⟩
    apply (QuotientGroup.eq_iff_div_mem (N := N.toSubgroup)).1
    have hN := congrFun hxy N
    exact hN
  have hφsurj : ∀ N : I, Function.Surjective (fun x : G ⧸ R => φ x N) := by
    intro N y
    rcases QuotientGroup.mk'_surjective N.toSubgroup y with ⟨g, rfl⟩
    exact ⟨QuotientGroup.mk' R g, rfl⟩
  have hQ : ∀ N : I, HasOpenNormalBasisInClass C (Q N) := by
    intro N
    exact N.quotient_hasOpenNormalBasisInClass
  simpa [R] using
    (HasOpenNormalBasisInClass.of_subdirectProduct
      (C := C) (Gs := Q) φ hφcont hφinj hφsurj hForm hQ)

end ProCGroups.ProC

import Mathlib.Topology.Algebra.Group.Quotient
import ProCGroups.ProC.OpenNormalSubgroups.ProCGroup

set_option autoImplicit false

/-!
# Closed kernels and the pro-\(C\) residual core

`ProCQuotientKernel C G` bundles a closed normal subgroup together with an open-normal
quotient-in-\(C\) basis on its quotient. The residual core is their intersection; closedness and
normality therefore follow directly from the stored kernel data, without reconstructing separation
axioms from the basis property.
-/

open Set

namespace ProCGroups.ProC

universe u

/-- Bundled closed normal kernels whose quotient has an open-normal quotient-in-\(C\) basis. -/
structure ProCQuotientKernel
    (C : FiniteGroupClass)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    extends ClosedSubgroup G where
  /-- The underlying closed subgroup is normal in \(G\). -/
  normal : toSubgroup.Normal
  /-- The quotient by the kernel has an open-normal basis of finite quotients in \(C\). -/
  quotient_hasOpenNormalBasisInClass : letI := normal; HasOpenNormalBasisInClass C (G ⧸ toSubgroup)

attribute [instance] ProCQuotientKernel.normal

/-- The residual core \(R_C(G)\), defined as the intersection of all closed normal kernels whose
quotient has an open-normal quotient-in-\(C\) basis. -/
noncomputable def proCResidualCore
    (C : FiniteGroupClass)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : Subgroup G :=
  sInf (Set.range fun N : ProCQuotientKernel C G => N.toSubgroup)

/-- The residual core is a normal subgroup. -/
@[instance]
theorem proCResidualCore_normal
    (C : FiniteGroupClass)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    (proCResidualCore C G).Normal := by
  change
    (sInf (Set.range fun N : ProCQuotientKernel C G => N.toSubgroup)).Normal
  simpa [proCResidualCore, sInf_range] using
    (Subgroup.normal_iInf_normal
      (a := fun N : ProCQuotientKernel C G => N.toSubgroup)
      (norm := fun N => N.normal))

/-- The residual core is closed. -/
theorem proCResidualCore_isClosed
    (C : FiniteGroupClass)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    IsClosed ((proCResidualCore C G : Subgroup G) : Set G) := by
  rw [proCResidualCore, sInf_range]
  simp only [Subgroup.coe_iInf]
  exact isClosed_iInter fun N => N.isClosed'
end ProCGroups.ProC

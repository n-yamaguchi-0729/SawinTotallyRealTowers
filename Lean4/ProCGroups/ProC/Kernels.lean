import Mathlib.GroupTheory.Abelianization.Defs
import ProCGroups.Abelian.TopologicalAbelianization
import ProCGroups.ProC.Subgroups.Closed

set_option autoImplicit false

/-!
# Profinite kernels and their abelianizations

This file equips kernels of continuous maps between profinite groups with their closed profinite
topology and constructs the corresponding topological abelianization. It also transfers
open-normal quotient bases in a finite-group class to these kernel constructions.
-/

namespace ProCGroups.ProC

noncomputable section

open scoped Pointwise

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The kernel subgroup of a continuous homomorphism. -/
abbrev ProfiniteKernelSubgroup (psi : ContinuousMonoidHom G H) : Subgroup G :=
  psi.toMonoidHom.ker

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- The kernel of a continuous homomorphism into a \(T_1\) topological group is closed. -/
theorem isClosed_profiniteKernelSubgroup [T1Space H] (psi : ContinuousMonoidHom G H) :
    IsClosed ((ProfiniteKernelSubgroup psi : Subgroup G) : Set G) := by
  change IsClosed (psi ⁻¹' ({1} : Set H))
  exact (isClosed_singleton (x := (1 : H))).preimage psi.continuous_toFun

/-- The topological kernel abelianization \(\ker \psi / \overline{[\ker \psi, \ker \psi]}\). -/
abbrev ProfiniteKernelAbelianization (psi : ContinuousMonoidHom G H) : Type u :=
  TopologicalAbelianization (ProfiniteKernelSubgroup psi)

/-- Additive notation for the topological kernel abelianization. -/
abbrev ProfiniteKernelAbelianizationAdd (psi : ContinuousMonoidHom G H) : Type u :=
  Additive (ProfiniteKernelAbelianization psi)

/--
The canonical quotient map from the algebraic kernel abelianization to the topological kernel
abelianization.
-/
def kernelAbelianizationToProfiniteKernelAbelianizationHom
    (psi : ContinuousMonoidHom G H) :
    Abelianization (ProfiniteKernelSubgroup psi) →*
      ProfiniteKernelAbelianization psi :=
  QuotientGroup.lift
    (commutator (ProfiniteKernelSubgroup psi))
    (QuotientGroup.mk'
      (Subgroup.closedCommutator (ProfiniteKernelSubgroup psi)))
    (by
      intro x hx
      exact
        (QuotientGroup.eq_one_iff
          (N := Subgroup.closedCommutator (ProfiniteKernelSubgroup psi)) x).2
          (Subgroup.commutator_le_closedCommutator (ProfiniteKernelSubgroup psi) hx))

/--
Additive form of the quotient from \((\ker \psi)^{ab}\) to the topological kernel
abelianization.
-/
def kernelAbelianizationToProfiniteKernelAbelianization
    (psi : ContinuousMonoidHom G H) :
    Additive (Abelianization (ProfiniteKernelSubgroup psi)) →+
      ProfiniteKernelAbelianizationAdd psi :=
  (kernelAbelianizationToProfiniteKernelAbelianizationHom
    (G := G) (H := H) psi).toAdditive

omit [IsTopologicalGroup H] in
/--
The canonical quotient map sends the class of a kernel element to its class modulo the
topological closure of the commutator subgroup.
-/
@[simp]
theorem kernelAbelianizationToProfiniteKernelAbelianization_of
    (psi : ContinuousMonoidHom G H) (n : ProfiniteKernelSubgroup psi) :
    kernelAbelianizationToProfiniteKernelAbelianization
        (G := G) (H := H) psi (Additive.ofMul (Abelianization.of n)) =
      Additive.ofMul
        (QuotientGroup.mk'
          (Subgroup.closedCommutator (ProfiniteKernelSubgroup psi)) n) := by
  rfl

omit [IsTopologicalGroup H] in
/--
The canonical map from the algebraic kernel abelianization to the topological one is surjective.
-/
theorem kernelAbelianizationToProfiniteKernelAbelianization_surjective
    (psi : ContinuousMonoidHom G H) :
    Function.Surjective
      (kernelAbelianizationToProfiniteKernelAbelianization
        (G := G) (H := H) psi) := by
  intro x
  change ∃ y : Additive (Abelianization (ProfiniteKernelSubgroup psi)),
    Additive.ofMul
      (kernelAbelianizationToProfiniteKernelAbelianizationHom
        (G := G) (H := H) psi (Additive.toMul y)) = x
  rcases QuotientGroup.mk'_surjective
      (Subgroup.closedCommutator (ProfiniteKernelSubgroup psi))
      (Additive.toMul x) with
    ⟨n, hn⟩
  refine ⟨Additive.ofMul (Abelianization.of n), ?_⟩
  apply Additive.toMul.injective
  change
    QuotientGroup.mk'
      (Subgroup.closedCommutator (ProfiniteKernelSubgroup psi)) n =
        Additive.toMul x
  exact hn

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- The closed kernel of a morphism out of a group with an open-normal \(C\)-basis again has such a
basis. -/
theorem HasOpenNormalBasisInClass.profiniteKernelSubgroup
    {C : FiniteGroupClass.{u}}
    (hHer : FiniteGroupClass.Hereditary C) (hG : HasOpenNormalBasisInClass C G)
    [T1Space H] (psi : ContinuousMonoidHom G H) :
    HasOpenNormalBasisInClass C (ProfiniteKernelSubgroup psi) :=
  HasOpenNormalBasisInClass.of_isClosed_subgroup
    C.isomClosed hHer.subgroupClosed hG (ProfiniteKernelSubgroup psi)
    (isClosed_profiniteKernelSubgroup psi)

omit [IsTopologicalGroup H] in
/-- The topological kernel abelianization of a morphism out of a group with an open-normal
\(C\)-basis again has such a basis. -/
theorem HasOpenNormalBasisInClass.profiniteKernelAbelianization
    {C : FiniteGroupClass.{u}}
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hC : FiniteGroupClass.FullFormation C) (hG : HasOpenNormalBasisInClass C G)
    [T1Space H] (psi : ContinuousMonoidHom G H) :
    HasOpenNormalBasisInClass C (ProfiniteKernelAbelianization psi) := by
  let N : Subgroup G := ProfiniteKernelSubgroup psi
  have : CompactSpace N :=
    (isClosed_profiniteKernelSubgroup psi).isClosedEmbedding_subtypeVal.compactSpace
  have hN : HasOpenNormalBasisInClass C N :=
    HasOpenNormalBasisInClass.profiniteKernelSubgroup hC.hereditary hG psi
  change HasOpenNormalBasisInClass C (N ⧸ Subgroup.closedCommutator N)
  exact quotient_closedNormalSubgroup
    hC.isomClosed hC.quotientClosed hN
    (Subgroup.closedCommutator N) (Subgroup.isClosed_closedCommutator N)

end

end ProCGroups.ProC

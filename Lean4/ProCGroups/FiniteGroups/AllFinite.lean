import Mathlib.GroupTheory.QuotientGroup.Finite
import ProCGroups.FiniteGroups.Classes

set_option autoImplicit false

/-!
# The class of all finite groups

This module defines `FiniteGroupClass.allFinite` and proves its standard closure properties:
formation, subgroup, normal-subgroup, quotient, finite-subdirect-product, extension, and
hereditary closure.  It also supplies the trivial-quotient instance used by pro-\(C\)
constructions when no restriction beyond finiteness is intended.
-/

namespace ProCGroups

universe u

namespace FiniteGroupClass

/-- The class of all finite groups. -/
def allFinite : FiniteGroupClass.{u} where
  pred := fun G [_] => Finite G
  finite_of_mem := fun hG => hG
  mem_of_mulEquiv := by
    intro G H _ _ e hG
    let : Finite G := hG
    exact Finite.of_equiv G e.toEquiv

/-- The class of all finite groups is an extension-closed formation. -/
theorem allFinite_formation : Formation allFinite := by
  refine ⟨?_, ?_⟩
  · intro G _ N _ hG
    let : Finite G := hG
    exact Finite.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  · intro ι _ G _ H _ f hf _ hH
    let : ∀ i, Finite (H i) := hH
    exact Finite.of_injective f hf

/-- The class of all finite groups contains the trivial quotients. -/
instance allFinite_containsTrivialQuotients :
    ContainsTrivialQuotients (allFinite : FiniteGroupClass.{u}) :=
  allFinite_formation.containsTrivialQuotients

/-- The class of all finite groups is closed under isomorphism. -/
theorem allFinite_isomClosed : IsomClosed allFinite := by
  exact allFinite.isomClosed

/-- The class of all finite groups is closed under subgroups. -/
theorem allFinite_subgroupClosed : SubgroupClosed allFinite := by
  intro G _ H hG
  let : Finite G := hG
  exact Finite.of_injective H.subtype Subtype.val_injective

/-- The class of all finite groups is closed under normal subgroups. -/
theorem allFinite_normalSubgroupClosed : NormalSubgroupClosed allFinite := by
  intro G _ N _ hG
  exact allFinite_subgroupClosed N hG

/-- The class of all finite groups is closed under quotients. -/
theorem allFinite_quotientClosed : QuotientClosed allFinite :=
  allFinite_formation.quotientClosed

/-- The class of all finite groups is closed under finite subdirect products. -/
theorem allFinite_finiteSubdirectProductClosed : FiniteSubdirectProductClosed allFinite :=
  allFinite_formation.finiteSubdirectProductClosed

/-- The class of all finite groups is extension closed. -/
theorem allFinite_extensionClosed : ExtensionClosed allFinite := by
  intro E _ N _ hN hQ
  let : Finite N := hN
  let : Finite (E ⧸ N) := hQ
  exact Finite.of_subgroup_quotient N

/-- The class of all finite groups is hereditary. -/
theorem allFinite_hereditary : Hereditary allFinite := by
  refine ⟨?_⟩
  intro G H _ _ hH f hf
  let : Finite H := hH
  exact Finite.of_injective f hf

end FiniteGroupClass

end ProCGroups

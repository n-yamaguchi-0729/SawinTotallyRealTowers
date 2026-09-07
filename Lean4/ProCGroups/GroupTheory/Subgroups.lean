import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Algebra.OpenSubgroup

set_option autoImplicit false

/-!
# Quotients by kernels

This module realizes the quotient by the kernel of a homomorphism as an injective homomorphism
into the target and records its value on quotient representatives.
-/

namespace ProCGroups.GroupTheory

universe u

variable {G : Type u} [Group G]

/-- The canonical embedding of a kernel quotient into the target range, viewed in the target. -/
noncomputable def quotientKerEmbedding
    {G T : Type u} [Group G] [Group T] (φ : G →* T) :
    G ⧸ φ.ker →* T :=
  φ.range.subtype.comp (QuotientGroup.quotientKerEquivRange φ).toMonoidHom

/-- The quotient-kernel embedding is injective. -/
theorem quotientKerEmbedding_injective
    {G T : Type u} [Group G] [Group T] (φ : G →* T) :
    Function.Injective (quotientKerEmbedding φ) := by
  exact
    φ.range.subtype_injective.comp
      (QuotientGroup.quotientKerEquivRange φ).injective

/-- The quotient-kernel embedding sends a representative to the corresponding kernel coset. -/
theorem quotientKerEmbedding_mk
    {G T : Type u} [Group G] [Group T] (φ : G →* T) (x : G) :
    quotientKerEmbedding φ (QuotientGroup.mk' φ.ker x) = φ x := by
  rfl

end ProCGroups.GroupTheory

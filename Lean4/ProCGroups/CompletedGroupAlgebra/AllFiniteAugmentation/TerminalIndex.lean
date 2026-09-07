import ProCGroups.CompletedGroupAlgebra.Separation

set_option autoImplicit false

/-!
# A base index for all-finite augmentation

This file constructs a canonical inhabitant of the open-quotient index used by the all-finite
completed group algebra, ensuring that its inverse system is nonempty.
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems
open ProCGroups.Completion

universe u v w

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/--
The finite quotient index type is nonempty, witnessed by the terminal quotient or canonical base
object.
-/
instance instNonemptyCompletedGroupAlgebraOpenQuotientIndex
    (R : Type u) [CommRing R] [TopologicalSpace R] :
    Nonempty (CompletedGroupAlgebraOpenQuotientIndex R G) :=
  inferInstance
end

end CompletedGroupAlgebra

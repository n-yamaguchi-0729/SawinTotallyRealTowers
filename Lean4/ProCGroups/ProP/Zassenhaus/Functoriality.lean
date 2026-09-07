import ProCGroups.ProP.Zassenhaus.Basic
import ProCGroups.CompletedGroupAlgebra.Augmentation.Functoriality

set_option autoImplicit false
/-!
# Functoriality of the Zassenhaus filtration

A continuous group homomorphism induces the existing functorial map on
class-indexed completed group algebras.  Naturality of augmentation and
continuity of that map show that every closed augmentation power, hence every
Zassenhaus subgroup, is preserved.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open CompletedGroupAlgebra

noncomputable section

universe u

variable (p : ℕ) [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The mod-`p` completed group-algebra map induced by a continuous group
homomorphism. -/
def modPCompletedGroupAlgebraMap (f : G →ₜ* H) :
    ModPCompletedGroupAlgebra p G →+* ModPCompletedGroupAlgebra p H :=
  completedGroupAlgebraMapInClass
    (G := G) (H := H)
    (ProCGroups.FiniteGroupClass.pGroup p)
    (ProCGroups.FiniteGroupClass.pGroup_hereditary p)
    (ZMod p) f.toMonoidHom f.continuous_toFun

/-- The induced completed map sends a group-like difference to the difference
of the image. -/
theorem modPCompletedGroupAlgebraMap_groupLikeDifference
    (f : G →ₜ* H) (g : G) :
    modPCompletedGroupAlgebraMap p f (groupLikeDifference p G g) =
      groupLikeDifference p H (f g) := by
  unfold modPCompletedGroupAlgebraMap groupLikeDifference
  rw [RingHom.map_sub, completedGroupAlgebraMapInClass_of, RingHom.map_one]
  rfl

/-- Functorial completed group-algebra maps preserve every closed power of the
augmentation ideal. -/
theorem modPCompletedGroupAlgebraMap_mem_closedAugmentationPower
    (f : G →ₜ* H) (n : ℕ) {x : ModPCompletedGroupAlgebra p G}
    (hx : x ∈ closedAugmentationPower p G n) :
    modPCompletedGroupAlgebraMap p f x ∈ closedAugmentationPower p H n := by
  unfold closedAugmentationPower at hx ⊢
  apply map_mem_closure
    (continuous_completedGroupAlgebraMapInClass
      (R := ZMod p) (G := G) (H := H)
      (ProCGroups.FiniteGroupClass.pGroup p)
      (ProCGroups.FiniteGroupClass.pGroup_hereditary p)
      f.toMonoidHom f.continuous_toFun)
    hx
  intro y hy
  apply ringHom_mem_ideal_pow (modPCompletedGroupAlgebraMap p f)
    (I := modPAugmentationIdeal p G) (J := modPAugmentationIdeal p H)
    (n := n) (x := y) ?_ hy
  intro z hz
  exact (completedGroupAlgebraMapInClass_mem_canonicalAugmentationIdeal_iff
    (R := ZMod p) (G := G) (H := H)
    (C := ProCGroups.FiniteGroupClass.pGroup p)
    (ProCGroups.FiniteGroupClass.pGroup_hereditary p)
    f.toMonoidHom f.continuous_toFun).2 hz

/-- Continuous homomorphisms preserve membership in each Zassenhaus
subgroup. -/
theorem map_mem_zassenhausSubgroup
    (f : G →ₜ* H) (n : ℕ) {g : G}
    (hg : g ∈ zassenhausSubgroup p G n) :
    f g ∈ zassenhausSubgroup p H n := by
  change groupLikeDifference p H (f g) ∈ closedAugmentationPower p H n
  rw [← modPCompletedGroupAlgebraMap_groupLikeDifference p f g]
  exact modPCompletedGroupAlgebraMap_mem_closedAugmentationPower p f n hg

/-- The subgroup image of `Dₙ(G)` is contained in `Dₙ(H)`. -/
theorem Subgroup.map_zassenhausSubgroup_le
    (f : G →ₜ* H) (n : ℕ) :
    (zassenhausSubgroup p G n).map f ≤ zassenhausSubgroup p H n := by
  rintro _ ⟨g, hg, rfl⟩
  exact map_mem_zassenhausSubgroup p f n hg

end

end ClassFieldTower.ProP

import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
import ProCGroups.ProC.Subgroups.Closed

set_option autoImplicit false

/-!
# The category of pro-\(C\) groups

`ProCGrp C` is the full subcategory of Mathlib's `ProfiniteGrp` cut out by
`HasOpenNormalBasisInClass C`. Thus the ambient object supplies the group, topological-group,
compact, Hausdorff, and totally disconnected structures; the class-restricted open-normal basis is
the only additional property.
-/

open CategoryTheory Topology

universe u

/-- The canonical object property underlying the category of pro-`C` groups. -/
def ProCGroups.proCObjectProperty (C : ProCGroups.FiniteGroupClass.{u}) :
    ObjectProperty ProfiniteGrp.{u} :=
  fun G => ProCGroups.ProC.HasOpenNormalBasisInClass C G

/-- Pro-\(C\) groups: profinite groups with an open-normal quotient basis in \(C\). -/
@[pp_with_univ]
abbrev ProCGrp (C : ProCGroups.FiniteGroupClass.{u}) :=
  (ProCGroups.proCObjectProperty C).FullSubcategory



namespace ProCGrp

variable {C : ProCGroups.FiniteGroupClass.{u}}

/-- A canonical pro-`C` object has exactly the carrier of its ambient `ProfiniteGrp` object.

This is the only carrier coercion installed here.  All algebraic and topological instances then
come definitionally from `G.obj`; redeclaring them on `ProCGrp` would create competing instance
paths with the ambient full-subcategory concrete structure. -/
instance : CoeSort (ProCGrp C) (Type u) where
  coe G := G.obj

/-- Construct a bundled pro-\(C\) group from a `ProfiniteGrp` and its open-normal basis property. -/
def of (C : ProCGroups.FiniteGroupClass.{u})
    (G : ProfiniteGrp.{u})
    (hBasis : ProCGroups.ProC.HasOpenNormalBasisInClass C G) : ProCGrp C :=
  ⟨G, hBasis⟩

/-- The continuous homomorphism carried by a full-subcategory morphism. -/
abbrev continuousHom {A B : ProCGrp C} (f : A ⟶ B) : A →ₜ* B :=
  ConcreteCategory.hom (C := ProCGrp C) f

/-- Morphisms in ProCGrp are equal when their underlying continuous homomorphisms are equal. -/
@[ext] theorem hom_ext {A B : ProCGrp C} {f g : A ⟶ B}
    (hf : continuousHom f = continuousHom g) :
    f = g :=
  ConcreteCategory.ext hf

/-- On profinite groups the all-finite object property imposes no additional condition. -/
@[simp] theorem allFinite_property (G : ProfiniteGrp.{u}) :
    ProCGroups.proCObjectProperty ProCGroups.FiniteGroupClass.allFinite G := by
  intro W hW h1W
  rcases ProCGroups.ProC.exists_openNormalSubgroup_sub_open_nhds_of_one
      (G := G) hW h1W with ⟨U, hUW⟩
  exact ⟨U, hUW, ProCGroups.openNormalSubgroup_finiteQuotient (G := G) U⟩

end ProCGrp

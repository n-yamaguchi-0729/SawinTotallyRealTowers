import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom

set_option autoImplicit false

/-!
# Pro C Groups / Topological Groups

This module formalizes basic topological-group constructions used by the pro-\(C\) library.
-/

open CategoryTheory
open scoped Topology

universe u

namespace ProCGroups

/-- Bundled topological groups with continuous homomorphisms. -/
@[pp_with_univ]
structure TopGrp where
  /-- The underlying type of the topological group. -/
  carrier : Type u
  /-- The group structure on the carrier. -/
  [group : Group carrier]
  /-- The topology on the carrier. -/
  [topologicalSpace : TopologicalSpace carrier]
  /-- Multiplication and inversion are continuous for the stored topology. -/
  [isTopologicalGroup : IsTopologicalGroup carrier]

attribute [instance] TopGrp.group TopGrp.topologicalSpace TopGrp.isTopologicalGroup

namespace TopGrp

/-- The category object coerces to its underlying type. -/
instance instCoeSort : CoeSort TopGrp (Type u) where
  coe G := G.carrier

/-- Bundle an unbundled topological group. -/
abbrev of (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : TopGrp where
  carrier := G

/-- Morphisms of topological groups are continuous homomorphisms. -/
@[ext]
structure Hom (G H : TopGrp.{u}) where
  /-- The continuous group homomorphism underlying the bundled morphism. -/
  hom' : G →ₜ* H

/-- Topological groups form a category. -/
instance instCategory : Category TopGrp where
  Hom G H := Hom G H
  id G := ⟨ContinuousMonoidHom.id G⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

/--
The category of topological groups has the concrete category structure inherited from its
underlying type.
-/
instance instConcreteCategory : ConcreteCategory TopGrp (fun G H => G →ₜ* H) where
  hom f := f.hom'
  ofHom f := ⟨f⟩

/-- The underlying continuous homomorphism of a morphism. -/
abbrev Hom.hom {G H : TopGrp.{u}} (f : G ⟶ H) : G →ₜ* H :=
  ConcreteCategory.hom (C := TopGrp) f

/-- A morphism coerces to its underlying continuous homomorphism. -/
instance instCoeFunHom {G H : TopGrp.{u}} : CoeFun (G ⟶ H) (fun _ => G → H) where
  coe f := f.hom

/-- The underlying homomorphism of the identity morphism is the identity continuous homomorphism. -/
@[simp] theorem hom_id {G : TopGrp.{u}} :
    (𝟙 G : G ⟶ G).hom = ContinuousMonoidHom.id G :=
  rfl

/-- The underlying homomorphism of a composite is the composite of underlying homomorphisms. -/
@[simp] theorem hom_comp {G H K : TopGrp.{u}} (f : G ⟶ H) (g : H ⟶ K) :
    (f ≫ g).hom = g.hom.comp f.hom :=
  rfl

/--
The composite map is computed pointwise by applying the constituent coordinate formulas in
succession.
-/
@[simp] theorem comp_apply {G H K : TopGrp.{u}} (f : G ⟶ H) (g : H ⟶ K) (x : G) :
    (f ≫ g) x = g (f x) :=
  rfl

/-- Morphisms in TopGrp are equal when their underlying continuous homomorphisms are equal. -/
@[ext] theorem hom_ext {G H : TopGrp.{u}} {f g : G ⟶ H} (h : f.hom = g.hom) :
    f = g :=
  Hom.ext h

/-- Bundle a continuous homomorphism as a topological-group morphism. -/
abbrev ofHom {G H : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (f : G →ₜ* H) : of G ⟶ of H :=
  ConcreteCategory.ofHom f

end TopGrp

/-- Bundled commutative topological groups with continuous homomorphisms. -/
@[pp_with_univ]
structure CommTopGrp where
  /-- The underlying type of the commutative topological group. -/
  carrier : Type u
  /-- The commutative group structure on the carrier. -/
  [commGroup : CommGroup carrier]
  /-- The topology on the carrier. -/
  [topologicalSpace : TopologicalSpace carrier]
  /-- Multiplication and inversion are continuous for the stored topology. -/
  [isTopologicalGroup : IsTopologicalGroup carrier]

attribute [instance] CommTopGrp.commGroup CommTopGrp.topologicalSpace
  CommTopGrp.isTopologicalGroup

namespace CommTopGrp

/-- The category object coerces to its underlying type. -/
instance instCoeSort : CoeSort CommTopGrp (Type u) where
  coe G := G.carrier

/-- Bundle an unbundled commutative topological group. -/
abbrev of (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] :
    CommTopGrp where
  carrier := G

/-- Morphisms of commutative topological groups are continuous homomorphisms. -/
@[ext]
structure Hom (G H : CommTopGrp.{u}) where
  /-- The continuous homomorphism underlying the bundled morphism. -/
  hom' : G →ₜ* H

/-- Commutative topological groups form a category. -/
instance instCategory : Category CommTopGrp where
  Hom G H := Hom G H
  id G := ⟨ContinuousMonoidHom.id G⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

/--
The category of commutative topological groups has the concrete category structure inherited
from its underlying type.
-/
instance instConcreteCategory : ConcreteCategory CommTopGrp (fun G H => G →ₜ* H) where
  hom f := f.hom'
  ofHom f := ⟨f⟩

/-- The underlying continuous homomorphism of a morphism. -/
abbrev Hom.hom {G H : CommTopGrp.{u}} (f : G ⟶ H) : G →ₜ* H :=
  ConcreteCategory.hom (C := CommTopGrp) f

/-- A morphism coerces to its underlying continuous homomorphism. -/
instance instCoeFunHom {G H : CommTopGrp.{u}} : CoeFun (G ⟶ H) (fun _ => G → H) where
  coe f := f.hom

/-- The underlying homomorphism of the identity morphism is the identity continuous homomorphism. -/
@[simp] theorem hom_id {G : CommTopGrp.{u}} :
    (𝟙 G : G ⟶ G).hom = ContinuousMonoidHom.id G :=
  rfl

/-- The underlying homomorphism of a composite is the composite of underlying homomorphisms. -/
@[simp] theorem hom_comp {G H K : CommTopGrp.{u}} (f : G ⟶ H) (g : H ⟶ K) :
    (f ≫ g).hom = g.hom.comp f.hom :=
  rfl

/--
The composite map is computed pointwise by applying the constituent coordinate formulas in
succession.
-/
@[simp] theorem comp_apply {G H K : CommTopGrp.{u}} (f : G ⟶ H) (g : H ⟶ K) (x : G) :
    (f ≫ g) x = g (f x) :=
  rfl

/-- Morphisms in CommTopGrp are equal when their underlying continuous homomorphisms are equal. -/
@[ext] theorem hom_ext {G H : CommTopGrp.{u}} {f g : G ⟶ H} (h : f.hom = g.hom) :
    f = g :=
  Hom.ext h

/-- Bundle a continuous homomorphism as a commutative topological-group morphism. -/
abbrev ofHom {G H : Type u}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
    (f : G →ₜ* H) : of G ⟶ of H :=
  ConcreteCategory.ofHom f

end CommTopGrp

/-- Forget the commutativity of a bundled commutative topological group. -/
def commTopGrpForgetToTopGrp : CommTopGrp.{u} ⥤ TopGrp.{u} where
  obj G := TopGrp.of G
  map f := TopGrp.ofHom f.hom
  map_id G := by
    apply TopGrp.hom_ext
    rfl
  map_comp f g := by
    apply TopGrp.hom_ext
    rfl
end ProCGroups

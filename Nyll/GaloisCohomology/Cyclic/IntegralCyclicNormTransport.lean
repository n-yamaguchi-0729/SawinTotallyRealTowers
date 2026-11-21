/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Homology
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.RepresentationTheory.Rep.Res
public import Nyll.GaloisCohomology.Cyclic.IntegralCyclicNormComplexes

/-!
# Transport of the original integer cyclic norm complexes

Reindexing a representation along a group equivalence retains its coefficient module and
reindexes the actual finite norm sum. An isomorphism of representations gives the same
underlying module isomorphism in all three positions. These comparisons use the original
norm and action-minus-identity maps, with independent group and coefficient universes.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory

namespace IntegralGroupCohomology.Universe

section GroupEquiv

variable {Q : Type u} {P : Type w} [Group Q] [Group P] [Fintype Q] [Fintype P]

/-- Reindexing along a group equivalence preserves the original integer norm map. -/
theorem res_norm_eq (e : Q ≃* P) (A : Rep.{v} ℤ P) :
    ModuleCat.ofHom (Rep.res e.toMonoidHom A).norm.asHom.hom.toLinearMap =
      ModuleCat.ofHom A.norm.asHom.hom.toLinearMap := by
  apply congrArg ModuleCat.ofHom
  change Representation.norm (Rep.res e.toMonoidHom A).ρ = Representation.norm A.ρ
  simp only [Representation.norm]
  exact Fintype.sum_equiv e.toEquiv
    (fun q : Q => (Rep.res e.toMonoidHom A).ρ q)
    (fun p : P => A.ρ p) (fun _ => rfl)

/-- Group reindexing identifies the original norm-then-action short complexes. -/
def normHomCompSubResEquivIso (e : Q ≃* P) (A : Rep.{v} ℤ P) (g : Q) :
    normHomCompSub (Rep.res e.toMonoidHom A) g ≅ normHomCompSub A (e g) := by
  let Ares : Rep.{v} ℤ Q := Rep.res e.toMonoidHom A
  let i : ModuleCat.of ℤ Ares.V ≅ ModuleCat.of ℤ A.V := Iso.refl _
  refine ShortComplex.isoMk i i i ?_ ?_
  · change 𝟙 (ModuleCat.of ℤ A.V) ≫ ModuleCat.ofHom A.norm.asHom.hom.toLinearMap =
      ModuleCat.ofHom Ares.norm.asHom.hom.toLinearMap ≫ 𝟙 (ModuleCat.of ℤ A.V)
    rw [Category.id_comp, Category.comp_id]
    exact (res_norm_eq e A).symm
  · rfl

/-- Group reindexing identifies the original action-then-norm short complexes. -/
def subCompNormHomResEquivIso (e : Q ≃* P) (A : Rep.{v} ℤ P) (g : Q) :
    subCompNormHom (Rep.res e.toMonoidHom A) g ≅ subCompNormHom A (e g) := by
  let Ares : Rep.{v} ℤ Q := Rep.res e.toMonoidHom A
  let i : ModuleCat.of ℤ Ares.V ≅ ModuleCat.of ℤ A.V := Iso.refl _
  refine ShortComplex.isoMk i i i ?_ ?_
  · rfl
  · change 𝟙 (ModuleCat.of ℤ A.V) ≫ ModuleCat.ofHom A.norm.asHom.hom.toLinearMap =
      ModuleCat.ofHom Ares.norm.asHom.hom.toLinearMap ≫ 𝟙 (ModuleCat.of ℤ A.V)
    rw [Category.id_comp, Category.comp_id]
    exact (res_norm_eq e A).symm

/-- The induced homology isomorphism for group reindexing in degree zero. -/
def normHomCompSubHomologyResEquivIso (e : Q ≃* P) (A : Rep.{v} ℤ P) (g : Q) :
    (normHomCompSub (Rep.res e.toMonoidHom A) g).homology ≅
      (normHomCompSub A (e g)).homology :=
  ShortComplex.homologyMapIso (normHomCompSubResEquivIso e A g)

/-- The induced homology isomorphism for group reindexing in degree minus one. -/
def subCompNormHomHomologyResEquivIso (e : Q ≃* P) (A : Rep.{v} ℤ P) (g : Q) :
    (subCompNormHom (Rep.res e.toMonoidHom A) g).homology ≅
      (subCompNormHom A (e g)).homology :=
  ShortComplex.homologyMapIso (subCompNormHomResEquivIso e A g)

end GroupEquiv

section RepresentationIso

variable {G : Type u} [Group G] [Fintype G]

/-- An isomorphism of representations identifies their original norm-then-action complexes. -/
def normHomCompSubIsoOfRepIso {M N : Rep.{v} ℤ G} (e : M ≅ N) (g : G) :
    normHomCompSub M g ≅ normHomCompSub N g := by
  let F := forget₂ (Rep.{v} ℤ G) (ModuleCat.{v} ℤ)
  let i : ModuleCat.of ℤ M.V ≅ ModuleCat.of ℤ N.V := F.mapIso e
  refine ShortComplex.isoMk i i i ?_ ?_
  · change F.map e.hom ≫ F.map N.norm.asHom = F.map M.norm.asHom ≫ F.map e.hom
    rw [← F.map_comp, ← F.map_comp, Rep.norm_comm]
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change M at x
    change N.ρ g (e.hom.hom x) - e.hom.hom x = e.hom.hom (M.ρ g x - x)
    rw [map_sub, Rep.hom_comm_apply]

/-- An isomorphism of representations identifies their original action-then-norm complexes. -/
def subCompNormHomIsoOfRepIso {M N : Rep.{v} ℤ G} (e : M ≅ N) (g : G) :
    subCompNormHom M g ≅ subCompNormHom N g := by
  let F := forget₂ (Rep.{v} ℤ G) (ModuleCat.{v} ℤ)
  let i : ModuleCat.of ℤ M.V ≅ ModuleCat.of ℤ N.V := F.mapIso e
  refine ShortComplex.isoMk i i i ?_ ?_
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change M at x
    change N.ρ g (e.hom.hom x) - e.hom.hom x = e.hom.hom (M.ρ g x - x)
    rw [map_sub, Rep.hom_comm_apply]
  · change F.map e.hom ≫ F.map N.norm.asHom = F.map M.norm.asHom ≫ F.map e.hom
    rw [← F.map_comp, ← F.map_comp, Rep.norm_comm]

/-- The induced homology isomorphism for a representation isomorphism in degree zero. -/
def normHomCompSubHomologyIsoOfRepIso {M N : Rep.{v} ℤ G} (e : M ≅ N) (g : G) :
    (normHomCompSub M g).homology ≅ (normHomCompSub N g).homology :=
  ShortComplex.homologyMapIso (normHomCompSubIsoOfRepIso e g)

/-- The induced homology isomorphism for a representation isomorphism in degree minus one. -/
def subCompNormHomHomologyIsoOfRepIso {M N : Rep.{v} ℤ G} (e : M ≅ N) (g : G) :
    (subCompNormHom M g).homology ≅ (subCompNormHom N g).homology :=
  ShortComplex.homologyMapIso (subCompNormHomIsoOfRepIso e g)

end RepresentationIso

end IntegralGroupCohomology.Universe

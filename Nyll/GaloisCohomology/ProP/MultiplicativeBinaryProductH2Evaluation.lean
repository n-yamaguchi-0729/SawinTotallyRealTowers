/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Product
public import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.TateComparison
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Coordinate evaluation of multiplicative H²

Constructs the two coordinate maps for a product of multiplicative
representations and proves their combined degree-two evaluation is bijective.
-/

@[expose] public section

namespace ClassFieldTower.Cohomology
open CategoryTheory groupCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable {G : Type} [Group G]
variable (M N : Type) [CommGroup M] [CommGroup N]
variable [MulDistribMulAction G M] [MulDistribMulAction G N]

/-- The first coordinate as an equivariant map of multiplicative representations. -/
def firstRepHom :
    Rep.ofMulDistribMulAction G (M × N) ⟶ Rep.ofMulDistribMulAction G M :=
  equivariantRepHom (MonoidHom.fst M N) (fun _ _ => rfl)

/-- The second coordinate as an equivariant map of multiplicative representations. -/
def secondRepHom :
    Rep.ofMulDistribMulAction G (M × N) ⟶ Rep.ofMulDistribMulAction G N :=
  equivariantRepHom (MonoidHom.snd M N) (fun _ _ => rfl)

/-- The pair of actual coordinate evaluations on degree-two cohomology. -/
noncomputable def prodMultiplicativeH2Evaluation :
    groupCohomology (Rep.ofMulDistribMulAction G (M × N)) 2 →+
      groupCohomology (Rep.ofMulDistribMulAction G M) 2 ×
        groupCohomology (Rep.ofMulDistribMulAction G N) 2 :=
  ((groupCohomology.map (A := Rep.ofMulDistribMulAction G (M × N))
    (B := Rep.ofMulDistribMulAction G M) (MonoidHom.id G)
    (firstRepHom M N) 2).hom.toAddMonoidHom).prod
      ((groupCohomology.map (A := Rep.ofMulDistribMulAction G (M × N))
        (B := Rep.ofMulDistribMulAction G N) (MonoidHom.id G)
        (secondRepHom M N) 2).hom.toAddMonoidHom)

/-- Two coordinate primitives assemble to a primitive in the product. -/
theorem prodMultiplicativeH2Evaluation_injective :
    Function.Injective (prodMultiplicativeH2Evaluation (G := G) M N) := by
  apply (AddMonoidHom.ker_eq_bot_iff (prodMultiplicativeH2Evaluation (G := G) M N)).mp
  apply bot_unique
  intro x hx
  change x = 0
  induction x using H2_induction_on with
  | h c =>
    have hM : H2π (Rep.ofMulDistribMulAction G M)
        (mapCocycles₂ (A := Rep.ofMulDistribMulAction G (M × N))
          (B := Rep.ofMulDistribMulAction G M) (MonoidHom.id G) (firstRepHom M N) c) = 0 := by
      rw [← H2π_comp_map_apply]
      exact congrArg Prod.fst hx
    have hN : H2π (Rep.ofMulDistribMulAction G N)
        (mapCocycles₂ (A := Rep.ofMulDistribMulAction G (M × N))
          (B := Rep.ofMulDistribMulAction G N) (MonoidHom.id G) (secondRepHom M N) c) = 0 := by
      rw [← H2π_comp_map_apply]
      exact congrArg Prod.snd hx
    obtain ⟨b, hb⟩ := (H2π_eq_zero_iff _).mp hM
    obtain ⟨d, hd⟩ := (H2π_eq_zero_iff _).mp hN
    apply (H2π_eq_zero_iff c).mpr
    refine ⟨fun g => Additive.ofMul ((b g).toMul, (d g).toMul), ?_⟩
    funext gh
    apply Additive.toMul.injective
    exact Prod.ext (congrArg Additive.toMul (congrFun hb gh))
      (congrArg Additive.toMul (congrFun hd gh))

/-- A pair of degree-two classes assembles to a class for the product representation. -/
theorem prodMultiplicativeH2Evaluation_surjective :
    Function.Surjective (prodMultiplicativeH2Evaluation (G := G) M N) := by
  rintro ⟨x, y⟩
  let B := Rep.ofMulDistribMulAction G M
  let C := Rep.ofMulDistribMulAction G N
  obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective (H2π B)).1 inferInstance x
  obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective (H2π C)).1 inferInstance y
  let A := Rep.ofMulDistribMulAction G (M × N)
  let a₀ (gh : G × G) : Additive M := a gh
  let b₀ (gh : G × G) : Additive N := b gh
  let c₀ (gh : G × G) : A := Additive.ofMul ((a₀ gh).toMul, (b₀ gh).toMul)
  let c : cocycles₂ A := ⟨c₀, by
    apply (mem_cocycles₂_iff c₀).mpr
    intro g h j
    apply Additive.toMul.injective
    exact Prod.ext
      (congrArg (fun u : B => (show Additive M from u).toMul)
        ((mem_cocycles₂_iff _).mp a.property g h j))
      (congrArg (fun u : C => (show Additive N from u).toMul)
        ((mem_cocycles₂_iff _).mp b.property g h j))⟩
  have ha : mapCocycles₂ (MonoidHom.id G) (firstRepHom M N) c = a := by
    apply cocycles₂_ext
    intro g h
    rfl
  have hb : mapCocycles₂ (MonoidHom.id G) (secondRepHom M N) c = b := by
    apply cocycles₂_ext
    intro g h
    rfl
  refine ⟨H2π A c, Prod.ext ?_ ?_⟩
  · change groupCohomology.map (MonoidHom.id G) (firstRepHom M N) 2 (H2π A c) = H2π B a
    rw [H2π_comp_map_apply, ha]
  · change groupCohomology.map (MonoidHom.id G) (secondRepHom M N) 2 (H2π A c) = H2π C b
    rw [H2π_comp_map_apply, hb]

end ClassFieldTower.Cohomology

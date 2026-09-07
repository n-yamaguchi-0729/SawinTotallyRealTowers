import GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Product
import GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.TateComparison
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.TypeTags.Basic

set_option autoImplicit false

namespace ClassFieldTower.Cohomology
open CategoryTheory groupCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable {G : Type} [Group G]
variable (M N : Type) [CommGroup M] [CommGroup N]
variable [MulDistribMulAction G M] [MulDistribMulAction G N]

private def firstRepHom :
    Rep.ofMulDistribMulAction G (M × N) ⟶ Rep.ofMulDistribMulAction G M :=
  equivariantRepHom (MonoidHom.fst M N) (fun _ _ => rfl)

private def secondRepHom :
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

end ClassFieldTower.Cohomology

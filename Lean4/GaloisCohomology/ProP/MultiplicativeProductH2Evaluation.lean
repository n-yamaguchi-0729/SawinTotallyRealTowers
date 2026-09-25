/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Product
import GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.TateComparison
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.TypeTags.Basic

set_option autoImplicit false

/-!
# Degree-two cohomology detected by product coordinates

An actual one-cochain primitive in each coordinate combines into a product
primitive.  Consequently evaluation detects degree-two classes, including
for an infinite product of multiplicative coefficient groups.
-/

namespace ClassFieldTower.Cohomology
open CategoryTheory groupCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable {G ι : Type} [Group G]
variable (M : ι → Type) [∀ i, CommGroup (M i)] [∀ i, MulDistribMulAction G (M i)]

local instance productEvaluationAction : MulDistribMulAction G (∀ i, M i) :=
  CyclicCohomology.piMulDistribMulAction G M

/-- Evaluation at one coordinate as a morphism of the actual representations. -/
def piMultiplicativeEvaluationRepHom (i : ι) :
    Rep.ofMulDistribMulAction G (∀ j, M j) ⟶ Rep.ofMulDistribMulAction G (M i) :=
  equivariantRepHom
    { toFun := fun x => x i
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    (fun _ _ => rfl)

/-- Simultaneous evaluation on degree-two cohomology. -/
noncomputable def piMultiplicativeH2Evaluation :
    groupCohomology (Rep.ofMulDistribMulAction G (∀ i, M i)) 2 →+
      ∀ i, groupCohomology (Rep.ofMulDistribMulAction G (M i)) 2 where
  toFun x i :=
    (groupCohomology.map (A := Rep.ofMulDistribMulAction G (∀ j, M j))
      (B := Rep.ofMulDistribMulAction G (M i))
      (MonoidHom.id G) (piMultiplicativeEvaluationRepHom M i) 2).hom x
  map_zero' := by
    funext i
    exact map_zero (groupCohomology.map
      (A := Rep.ofMulDistribMulAction G (∀ j, M j))
      (B := Rep.ofMulDistribMulAction G (M i))
      (MonoidHom.id G) (piMultiplicativeEvaluationRepHom M i) 2).hom
  map_add' x y := by
    funext i
    exact map_add (groupCohomology.map
      (A := Rep.ofMulDistribMulAction G (∀ j, M j))
      (B := Rep.ofMulDistribMulAction G (M i))
      (MonoidHom.id G) (piMultiplicativeEvaluationRepHom M i) 2).hom x y

/-- Product degree-two classes are determined by all their evaluations. -/
theorem piMultiplicativeH2Evaluation_injective :
    Function.Injective (piMultiplicativeH2Evaluation (G := G) M) := by
  apply (AddMonoidHom.ker_eq_bot_iff (piMultiplicativeH2Evaluation (G := G) M)).mp
  apply bot_unique
  intro x hx
  change x = 0
  induction x using H2_induction_on with
  | h c =>
    have hcoord (i : ι) :
        H2π (Rep.ofMulDistribMulAction G (M i))
          (mapCocycles₂ (A := Rep.ofMulDistribMulAction G (∀ j, M j))
            (B := Rep.ofMulDistribMulAction G (M i))
            (MonoidHom.id G) (piMultiplicativeEvaluationRepHom M i) c) = 0 := by
      rw [← H2π_comp_map_apply]
      exact congrFun hx i
    choose b hb using fun i => (H2π_eq_zero_iff
      (mapCocycles₂ (A := Rep.ofMulDistribMulAction G (∀ j, M j))
            (B := Rep.ofMulDistribMulAction G (M i))
            (MonoidHom.id G) (piMultiplicativeEvaluationRepHom M i) c)).mp
        (hcoord i)
    apply (H2π_eq_zero_iff c).mpr
    refine ⟨fun g => Additive.ofMul (fun i => (b i g).toMul), ?_⟩
    funext gh
    apply Additive.toMul.injective
    funext i
    exact congrArg Additive.toMul (congrFun (hb i) gh)

end ClassFieldTower.Cohomology

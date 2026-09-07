import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Order
import ProCGroups.Completion.UniversalProperty
import ProCGroups.ProC.Category.Basic
import ProCGroups.ProC.MaximalQuotients.ResidualCore
import ProCGroups.ProC.MaximalQuotients.ResidualQuotient
import ProCGroups.ProC.MaximalQuotients.UniversalProperty
import ProCGroups.ProC.Quotients.ClosedNormal

set_option autoImplicit false

/-!
# Constructing pro-C completions

The pro-C completion is the quotient of the profinite completion by its pro-C
residual core. Its universal property follows from the two actual quotient maps.
-/

namespace ProCGroups.Completion

open ProCGroups.ProC

universe u

/-- The pro-C residual quotient of the profinite completion of an abstract group. -/
noncomputable def proCCompletion
    (C : FiniteGroupClass.{u}) (hForm : FiniteGroupClass.Formation C)
    (G : Type u) [Group G] : ProCGrp C := by
  let P := ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)
  let R : Subgroup P := proCResidualCore C P
  letI : IsClosed (R : Set P) := proCResidualCore_isClosed C P
  letI : TotallyDisconnectedSpace (P ⧸ R) :=
    totallyDisconnectedSpace_quotient_closedNormal R (proCResidualCore_isClosed C P)
  exact ProCGrp.of C (ProfiniteGrp.of (P ⧸ R))
    (proCResidualCoreQuotient_hasOpenNormalBasisInClass hForm)

/-- The canonical map from a discrete group to its constructed pro-C completion. -/
noncomputable def proCCompletionMap
    (C : FiniteGroupClass.{u}) (hForm : FiniteGroupClass.Formation C)
    (G : Type u) [Group G] [TopologicalSpace G] [DiscreteTopology G] :
    G →ₜ* proCCompletion C hForm G where
  toMonoidHom :=
    (QuotientGroup.mk' (proCResidualCore C
      (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)))).comp
      (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of G)).hom
  continuous_toFun := continuous_of_discreteTopology

/-- The residual quotient of the profinite completion has the pro-C universal property. -/
theorem proCCompletion_isProCCompletion
    (C : FiniteGroupClass.{u}) (hForm : FiniteGroupClass.Formation C)
    (hHer : FiniteGroupClass.Hereditary C)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [DiscreteTopology G] :
    IsProCCompletion C G (proCCompletion C hForm G)
      (proCCompletionMap C hForm G) := by
  let P := ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G)
  let R : Subgroup P := proCResidualCore C P
  let q : P →ₜ* proCCompletion C hForm G :=
    { toMonoidHom := QuotientGroup.mk' R
      continuous_toFun := continuous_quotient_mk' }
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective R
  refine ⟨(proCCompletion C hForm G).property, ?_, ?_⟩
  · exact hqsurj.denseRange.comp
      (ProfiniteGrp.ProfiniteCompletion.denseRange (GrpCat.of G)) q.continuous
  · intro H _ _ _ _ _ _ hH φ
    let f : P →ₜ* H :=
      (ProfiniteGrp.ProfiniteCompletion.lift (P := ProfiniteGrp.of H)
        (GrpCat.ofHom φ.toMonoidHom)).hom
    have hf : ∀ x : G,
        f (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) x) = φ x := by
      intro x
      exact CategoryTheory.ConcreteCategory.congr_hom
        (ProfiniteGrp.ProfiniteCompletion.lift_eta (P := ProfiniteGrp.of H)
          (GrpCat.ofHom φ.toMonoidHom)) x
    let fbar : proCCompletion C hForm G →ₜ* H :=
      lift_proCResidualCoreQuotient hHer f hH
    have hfac : fbar.comp (proCCompletionMap C hForm G) = φ := by
      ext x
      exact (lift_proCResidualCoreQuotient_mk hHer f hH
        (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) x)).trans (hf x)
    refine ⟨fbar, hfac, ?_⟩
    intro ψ hψ
    apply DFunLike.ext
    exact congrFun ((show DenseRange (proCCompletionMap C hForm G) from
      hqsurj.denseRange.comp
        (ProfiniteGrp.ProfiniteCompletion.denseRange (GrpCat.of G)) q.continuous).equalizer
      ψ.continuous fbar.continuous (by
        funext x
        exact congrArg (fun h : G →ₜ* H => h x) (hψ.trans hfac.symm)))

end ProCGroups.Completion

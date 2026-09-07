import ProCGroups.GolodShafarevich.CountableRelators
import ProCGroups.Topologies.ContinuousMonoidHom
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false

/-!
# The countable GS quotient of the presented group

The quotient of the free source factors continuously through the original
presentation. Killing the images of the added relators therefore still
surjects onto the infinite source quotient.
-/

namespace ClassFieldTower.ProP.FiniteProPPresentation

open ProCGroups ProCGroups.Presentations

noncomputable section

universe u

variable {p d r : ℕ} [Fact p.Prime]
variable {sourceData :
  FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
    (FiniteGroupClass.pGroup p)}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The actual presented group remains infinite after killing the images
of a countable deep relator family within the displayed GS budget. -/
theorem infinite_target_quotient_of_countable_relator_budget
    (P : FiniteProPPresentation p d r sourceData G)
    (ν₀ : Fin r → ℕ)
    (hν₀ : ∀ i, P.RelatorZassenhausDepthAtLeast (ν₀ i) i)
    (f : ℕ → sourceData.carrier) (ν : ℕ → ℕ)
    (hν : ∀ n, ZassenhausDepthAtLeast p (ν n) (f n))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hbudget : ∀ N, 1 - (d : ℝ) * t +
      (∑ i : Fin r, t ^ ν₀ i) + (∑ i : Fin N, t ^ ν i) ≤ 0) :
    Infinite (G ⧸ closedNormalClosure (Set.range (P.quotient ∘ f))) := by
  classical
  let K := closedNormalClosure (Set.range P.relator ∪ Set.range f)
  let Q := sourceData.carrier ⧸ K
  let : IsClosed (K : Set sourceData.carrier) := closedNormalClosure_isClosed _
  let : Infinite Q :=
    P.infinite_quotient_of_countable_relator_budget ν₀ hν₀ f ν hν ht0 ht1 hbudget
  let q : sourceData.carrier →ₜ* Q := ContinuousMonoidHom.quotientMk K
  have hker : P.quotient.toMonoidHom.ker ≤ q.toMonoidHom.ker := by
    rw [P.kernel_eq_closedNormalClosure]
    change closedNormalClosure (Set.range P.relator) ≤ (QuotientGroup.mk' K).ker
    rw [QuotientGroup.ker_mk']
    apply closedNormalClosure_le_closed_normal (closedNormalClosure_isClosed _)
    intro x hx
    exact subset_closedNormalClosure _ (Or.inl hx)
  let φ : G →* Q :=
    P.quotient.toMonoidHom.liftOfSurjective P.quotient_surjective
      ⟨q.toMonoidHom, hker⟩
  have hφ : ∀ x, φ (P.quotient x) = q x := by
    intro x
    exact MonoidHom.liftOfRightInverse_comp_apply
      (f := P.quotient.toMonoidHom)
      (f_inv := Function.surjInv P.quotient_surjective)
      (Function.rightInverse_surjInv P.quotient_surjective)
      ⟨q.toMonoidHom, hker⟩ x
  have hφcontinuous : Continuous φ := by
    apply (Topology.IsQuotientMap.of_surjective_continuous
      P.quotient_surjective P.quotient.continuous_toFun).continuous_iff.2
    convert q.continuous_toFun using 1
    funext x
    exact hφ x
  let J := closedNormalClosure (Set.range (P.quotient ∘ f))
  have hJ : J ≤ φ.ker := by
    apply closedNormalClosure_le_closed_normal
      (ContinuousMonoidHom.isClosed_ker ⟨φ, hφcontinuous⟩)
    rintro x ⟨n, rfl⟩
    change φ (P.quotient (f n)) = 1
    rw [hφ]
    change QuotientGroup.mk' K (f n) = 1
    exact (QuotientGroup.eq_one_iff (f n)).2
      (subset_closedNormalClosure _ (Or.inr ⟨n, rfl⟩))
  let ψ : G ⧸ J →* Q := QuotientGroup.lift J φ hJ
  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective K x
    refine ⟨QuotientGroup.mk' J (P.quotient y), ?_⟩
    exact hφ y
  exact Infinite.of_surjective ψ hψ

end

end ClassFieldTower.ProP.FiniteProPPresentation

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteDiscreteKernelField
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteMuPTopRep
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfinitePlaceArtin
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.LocalBlocks
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

set_option autoImplicit false

/-!
# Killing real conjugation makes the kernel field totally real

The real local Artin value of negative one is complex conjugation whenever
an infinite place ramifies. If a discrete absolute representation kills
these actual elements over a totally real base, its finite Galois kernel
field has a real place above each base place. Galois conjugacy then gives
total reality, independently of the order of the target group.
-/

namespace ClassFieldTower.Sawin

open NumberField GlobalClassFieldTheory.Reciprocity
open ClassFieldTower.Martinet.Shafarevich

/-- The negative-one local Artin element in the standard absolute Galois
model. This fixes the algebraic-closure scalar structure before specialization. -/
noncomputable def absoluteInfinitePlaceArtinNegOne
    (F : Type) [Field F] [CharZero F] (v : InfinitePlace F) :
    Field.absoluteGaloisGroup F :=
  (absoluteGaloisGroupContinuousMulEquiv F).symm
    (chosenInfinitePlaceArtinMonoidHom (K := F) (L := AlgebraicClosure F)
      v (-1 : v.Completionˣ))

/-- Killing each actual real Artin generator makes the finite kernel field
over a totally real base totally real. No p-group or odd-order input is used. -/
theorem absoluteDiscreteKernelField_isTotallyReal_of_infiniteArtin
    (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (s : Field.absoluteGaloisGroup F →ₜ* Q)
    (hs : ∀ v : InfinitePlace F, s (absoluteInfinitePlaceArtinNegOne F v) = 1) :
    IsTotallyReal (absoluteDiscreteKernelField F s) := by
  let M : IntermediateField F (AlgebraicClosure F) := absoluteDiscreteKernelField F s
  let : IsGalois F M := absoluteDiscreteKernelField_isGalois F s
  refine ⟨fun u ↦ ?_⟩
  let v₀ : InfinitePlace F := u.comap (algebraMap F M)
  let c : Gal(AlgebraicClosure F/F) :=
    chosenInfinitePlaceArtinMonoidHom (K := F) (L := AlgebraicClosure F)
      v₀ (-1 : v₀.Completionˣ)
  have hKilled : s ((absoluteGaloisGroupContinuousMulEquiv F).symm c) = 1 := hs v₀
  have hRestrict : AlgEquiv.restrictNormalHom M c = 1 := by
    apply absoluteDiscreteKernelGaloisHom_injective F s
    rw [map_one]
    have h := absoluteDiscreteKernelGaloisHom_restrict F s
      ((absoluteGaloisGroupContinuousMulEquiv F).symm c)
    simpa only [ContinuousMulEquiv.apply_symm_apply] using h.trans hKilled
  let w : InfinitePlace (AlgebraicClosure F) :=
    chosenInfinitePlaceAbove (L := AlgebraicClosure F) v₀
  let v : InfinitePlace M := w.comap (algebraMap M (AlgebraicClosure F))
  have hvUnramified : v.IsUnramified F := by
    by_contra hRamified
    have hwRamified : w.IsRamified F := fun h ↦ hRamified (h.comap M)
    have hConj : ComplexEmbedding.IsConj w.embedding c :=
      chosenInfinitePlaceArtinMonoidHom_neg_one_isConj_of_ramified
        (K := F) (L := AlgebraicClosure F) v₀ hwRamified
    have hReal : ComplexEmbedding.IsReal
        (w.embedding.comp (algebraMap M (AlgebraicClosure F))) := by
      apply ComplexEmbedding.isReal_iff.mpr
      ext x
      change star (w.embedding (algebraMap M (AlgebraicClosure F) x)) =
        w.embedding (algebraMap M (AlgebraicClosure F) x)
      rw [← hConj.eq]
      have hFixed := AlgEquiv.restrictNormal_commutes c M x
      change algebraMap M (AlgebraicClosure F) ((AlgEquiv.restrictNormalHom M c) x) =
        c (algebraMap M (AlgebraicClosure F) x) at hFixed
      rw [hRestrict] at hFixed
      exact congrArg w.embedding hFixed.symm
    have hvReal : v.IsReal := by
      change (w.comap (algebraMap M (AlgebraicClosure F))).IsReal
      rw [← InfinitePlace.mk_embedding w, InfinitePlace.comap_mk,
        InfinitePlace.isReal_mk_iff]
      exact hReal
    exact hRamified (hvReal.isUnramified (k := F))
  have hvBase : (v.comap (algebraMap F M)).IsUnramifiedIn M :=
    InfinitePlace.isUnramifiedIn_comap.mpr hvUnramified
  have hBase : v.comap (algebraMap F M) = v₀ := by
    change (w.comap (algebraMap M (AlgebraicClosure F))).comap (algebraMap F M) = v₀
    rw [← InfinitePlace.comap_comp, ← IsScalarTower.algebraMap_eq F M (AlgebraicClosure F)]
    exact chosenInfinitePlaceAbove_comap (L := AlgebraicClosure F) v₀
  have hu : u.IsUnramified F := hvBase u hBase.symm
  exact (InfinitePlace.isUnramified_iff.mp hu).resolve_right
    (InfinitePlace.not_isComplex_iff_isReal.mpr (IsTotallyReal.isReal v₀))

end ClassFieldTower.Sawin

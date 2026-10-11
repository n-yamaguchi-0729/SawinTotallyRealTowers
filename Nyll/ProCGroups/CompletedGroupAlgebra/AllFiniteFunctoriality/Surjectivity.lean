/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.CompletedGroupAlgebra.AllFiniteFunctoriality.Map
import Nyll.ProCGroups.CompletedGroupAlgebra.OpenFiniteQuotientTopology.OpenFiniteComparison

/-!
# Surjectivity of completed group-algebra maps

A surjective continuous group homomorphism induces a surjective map of all-finite completed group
algebras. The proof combines finite-stage surjectivity with the inverse-limit lifting argument.
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC

universe u v w

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/--
A surjective continuous homomorphism of profinite groups induces a surjective map on completed
group algebras.
-/
theorem completedGroupAlgebraMap_surjective_of_surjective
    [CompactSpace R] [T2Space R] [TotallyDisconnectedSpace R]
    (φ : G →* H) (hφ : Continuous φ)
    (hφsurj : Function.Surjective φ) :
    Function.Surjective (completedGroupAlgebraMap (G := G) (H := H) R φ hφ) := by
  let f := completedGroupAlgebraMap (G := G) (H := H) R φ hφ
  let : CompactSpace (CompletedGroupAlgebraCarrier R G) :=
    completedGroupAlgebra_compactSpace (R := R) (G := G)
  let : T2Space (CompletedGroupAlgebraCarrier R H) :=
    completedGroupAlgebra_t2Space (R := R) (G := H)
  have hfcont : Continuous f :=
    continuous_completedGroupAlgebraMap (R := R) (G := G) (H := H) φ hφ
  have hclosed : IsClosed (Set.range f) := (isCompact_range hfcont).isClosed
  have hdense : DenseRange (toCompletedGroupAlgebraRingHom R H) :=
    denseRange_toCompletedGroupAlgebraRingHom (R := R) (G := H)
  have hcanonical_subset :
      Set.range (toCompletedGroupAlgebraRingHom R H) ⊆ Set.range f := by
    intro y hy
    rcases hy with ⟨a, rfl⟩
    obtain ⟨bCoeff, hbCoeff⟩ :=
      Finsupp.mapDomain_surjective (M := R) hφsurj a.coeff
    let b : MonoidAlgebra R G := MonoidAlgebra.ofCoeff bCoeff
    have hb : MonoidAlgebra.mapDomainRingHom R φ b = a := by
      apply MonoidAlgebra.coeff_injective
      exact hbCoeff
    refine ⟨toCompletedGroupAlgebraRingHom R G b, ?_⟩
    have hcomp := congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraMap_comp_toCompletedGroupAlgebra
          (R := R) (G := G) (H := H) φ hφ))
      b
    simpa [f, RingHom.comp_apply, hb] using hcomp
  intro y
  have hycanonical : y ∈ closure (Set.range (toCompletedGroupAlgebraRingHom R H)) := by
    rw [hdense.closure_range]
    exact Set.mem_univ y
  have hyf : y ∈ closure (Set.range f) :=
    closure_mono hcanonical_subset hycanonical
  exact hclosed.closure_subset_iff.2 (fun z hz => hz) hyf

end

end CompletedGroupAlgebra

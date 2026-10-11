/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.CompletedGroupAlgebra.Separation

/-!
# Completed Group Algebra / Functoriality Composition

This module records compatibility of completed group algebra functoriality with composition.
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems
open ProCGroups.Completion

universe u v w

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

variable {K : Type v} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

/-- Lemma 5.3.5(e), composition law for the completed-group-algebra functor. -/
theorem completedGroupAlgebraMap_comp
    [CompactSpace R] [T2Space R] [TotallyDisconnectedSpace R]
    (φ : G →* H) (hφ : Continuous φ) (ψ : H →* K) (hψ : Continuous ψ) :
    (completedGroupAlgebraMap (G := H) (H := K) R ψ hψ).comp
        (completedGroupAlgebraMap (G := G) (H := H) R φ hφ) =
      completedGroupAlgebraMap (G := G) (H := K) R (ψ.comp φ) (hψ.comp hφ) := by
  apply completedGroupAlgebraRingHom_ext_of_comp_toCompleted (R := R) (G := G) (H := K)
  · exact (continuous_completedGroupAlgebraMap (R := R) (G := H) (H := K) ψ hψ).comp
      (continuous_completedGroupAlgebraMap (R := R) (G := G) (H := H) φ hφ)
  · exact continuous_completedGroupAlgebraMap (R := R) (G := G) (H := K)
      (ψ.comp φ) (hψ.comp hφ)
  · apply RingHom.ext
    intro x
    have hφdense := congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraMap_comp_toCompletedGroupAlgebra (R := R) (G := G) (H := H)
          φ hφ))
      x
    have hψdense := congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraMap_comp_toCompletedGroupAlgebra (R := R) (G := H) (H := K)
          ψ hψ))
      (MonoidAlgebra.mapDomainRingHom R φ x)
    have hdomain := congrFun
      (congrArg DFunLike.coe
        (finiteGroupAlgebra_mapDomainRingHom_comp R G H K φ ψ))
      x
    have hcompdense := congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraMap_comp_toCompletedGroupAlgebra (R := R) (G := G) (H := K)
          (ψ.comp φ) (hψ.comp hφ)))
      x
    calc
      (((completedGroupAlgebraMap (G := H) (H := K) R ψ hψ).comp
          (completedGroupAlgebraMap (G := G) (H := H) R φ hφ)).comp
          (toCompletedGroupAlgebraRingHom R G)) x
          =
        completedGroupAlgebraMap (G := H) (H := K) R ψ hψ
          (completedGroupAlgebraMap (G := G) (H := H) R φ hφ
            (toCompletedGroupAlgebraRingHom R G x)) := rfl
      _ =
        completedGroupAlgebraMap (G := H) (H := K) R ψ hψ
          (toCompletedGroupAlgebraRingHom R H (MonoidAlgebra.mapDomainRingHom R φ x)) := by
          have hφdense' :
              completedGroupAlgebraMap (G := G) (H := H) R φ hφ
                  (toCompletedGroupAlgebraRingHom R G x) =
                toCompletedGroupAlgebraRingHom R H (MonoidAlgebra.mapDomainRingHom R φ x) := by
            simpa [RingHom.comp_apply] using hφdense
          exact congrArg (completedGroupAlgebraMap (G := H) (H := K) R ψ hψ) hφdense'
      _ =
        toCompletedGroupAlgebraRingHom R K
          (MonoidAlgebra.mapDomainRingHom R ψ (MonoidAlgebra.mapDomainRingHom R φ x)) := by
          simpa [RingHom.comp_apply] using hψdense
      _ =
        toCompletedGroupAlgebraRingHom R K
          (MonoidAlgebra.mapDomainRingHom R (ψ.comp φ) x) := by
          exact congrArg (toCompletedGroupAlgebraRingHom R K) (by
            change (MonoidAlgebra.mapDomainRingHom R ψ)
                ((MonoidAlgebra.mapDomainRingHom R φ) x) =
              (MonoidAlgebra.mapDomainRingHom R (ψ.comp φ)) x at hdomain
            exact hdomain)
      _ =
        ((completedGroupAlgebraMap (G := G) (H := K) R (ψ.comp φ) (hψ.comp hφ)).comp
          (toCompletedGroupAlgebraRingHom R G)) x := by
          simpa [RingHom.comp_apply] using hcompdense.symm

/--
Lemma 5.3.5(e), composition law for the completed-group-algebra functor, as an \(R\)-algebra
homomorphism.
-/
theorem completedGroupAlgebraMapAlgHom_comp
    [CompactSpace R] [T2Space R] [TotallyDisconnectedSpace R]
    (φ : G →* H) (hφ : Continuous φ) (ψ : H →* K) (hψ : Continuous ψ) :
    (completedGroupAlgebraMapAlgHom (G := H) (H := K) R ψ hψ).comp
        (completedGroupAlgebraMapAlgHom (G := G) (H := H) R φ hφ) =
      completedGroupAlgebraMapAlgHom (G := G) (H := K) R (ψ.comp φ) (hψ.comp hφ) := by
  apply AlgHom.ext
  intro x
  have h := congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraMap_comp (R := R) (G := G) (H := H) (K := K)
        φ hφ ψ hψ))
    x
  simpa [RingHom.comp_apply] using h
end

end CompletedGroupAlgebra

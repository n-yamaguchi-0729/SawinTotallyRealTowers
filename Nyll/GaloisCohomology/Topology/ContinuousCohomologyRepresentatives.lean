/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Representatives and boundaries in continuous cohomology

The cocycle projection is surjective as a function, and its kernel consists
of boundaries. These are statements about the actual topological homology
objects, with no exactness assumptions on a coefficient sequence.
-/

open CategoryTheory CategoryTheory.Limits

namespace ContinuousCohomology

universe u v

variable {R : Type u} [Ring R] [TopologicalSpace R]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Every continuous cohomology class has a homogeneous cocycle representative. -/
theorem π_surjective (A : TopRep.{v} R G) (n : ℕ) :
    Function.Surjective (π A n) := by
  let K := TopRep.homogeneousCochains A
  let S := K.sc n
  have hleft : Function.Surjective S.leftHomologyπ := by
    let c : CokernelCofork S.toCycles :=
      CokernelCofork.ofπ (TopModuleCat.cokerπ S.toCycles)
        (TopModuleCat.comp_cokerπ S.toCycles)
    let hc : IsColimit c := TopModuleCat.isColimitCoker S.toCycles
    let d : CokernelCofork S.toCycles :=
      CokernelCofork.ofπ S.leftHomologyπ S.leftHomologyData.wπ
    let hd : IsColimit d := S.leftHomologyData.hπ
    let e : c.pt ≅ d.pt := hc.coconePointUniqueUpToIso hd
    have he : TopModuleCat.cokerπ S.toCycles ≫ e.hom = S.leftHomologyπ := by
      exact hc.comp_coconePointUniqueUpToIso_hom hd WalkingParallelPair.one
    intro y
    obtain ⟨x, hx⟩ := TopModuleCat.cokerπ_surjective S.toCycles (e.inv y)
    refine ⟨x, ?_⟩
    rw [← he]
    change e.hom (TopModuleCat.cokerπ S.toCycles x) = y
    rw [hx]
    exact ConcreteCategory.congr_hom e.inv_hom_id y
  intro y
  obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso S.leftHomologyIso.hom).2 y
  obtain ⟨x, hx⟩ := hleft z
  refine ⟨x, ?_⟩
  change S.leftHomologyIso.hom (S.leftHomologyπ x) = y
  rw [hx, hz]

/-- A homogeneous cocycle whose cohomology class is zero is a boundary. -/
theorem exists_boundary_of_π_eq_zero (A : TopRep.{v} R G) (n : ℕ)
    (z : cocycles A (n + 1)) (hz : π A (n + 1) z = 0) :
    ∃ c : (TopRep.homogeneousCochains A).X n,
      ((TopRep.homogeneousCochains A).d n (n + 1)).hom c =
        ((TopRep.homogeneousCochains A).iCycles (n + 1)).hom z := by
  let K := TopRep.homogeneousCochains A
  let S : ShortComplex (TopModuleCat R) :=
    ShortComplex.mk (K.toCycles n (n + 1)) (K.homologyπ (n + 1))
      (K.toCycles_comp_homologyπ n (n + 1))
  have hS : S.Exact := ShortComplex.exact_of_g_is_cokernel S
    (K.homologyIsCokernel n (n + 1) (CochainComplex.prev_nat_succ n))
  let F := forget₂ (TopModuleCat R) (ModuleCat R)
  have hSM : (S.map F).Exact := hS.map F
  obtain ⟨c, hc⟩ := ((S.map F).exact_iff_of_hasForget.mp hSM) z hz
  refine ⟨c, ?_⟩
  rw [← K.toCycles_i n (n + 1)]
  have hc' : (K.toCycles n (n + 1)).hom c = z := hc
  exact congrArg (fun w => (K.iCycles (n + 1)).hom w) hc'

end ContinuousCohomology

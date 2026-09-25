/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.TrivialZModP
import ProCGroups.ProP.Presentation.Basic
import ProCGroups.Topologies.ContinuousMulEquiv

set_option autoImplicit false
/-!
# Cohomology across a presentation quotient

Continuous group equivalences induce linear equivalences on continuous cohomology.  A finite
pro-`p` presentation supplies the required topological first-isomorphism equivalence between the
quotient of its free source by the presentation kernel and its target.
-/

open CategoryTheory
open scoped Topology

namespace ClassFieldTower.Cohomology

noncomputable section

universe u

variable {p : ℕ}
variable {G H : Type u}
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- A continuous group equivalence induces a linear equivalence on continuous cohomology with
lifted trivial `ZMod p` coefficients. -/
noncomputable def continuousCohomologyZModPLiftedLinearEquiv
    (e : H ≃ₜ* G) (n : ℕ) :
    continuousCohomologyZModPLifted p G n ≃ₗ[ZMod p]
      continuousCohomologyZModPLifted p H n := by
  let f : H →ₜ* G := e
  let g : G →ₜ* H := e.symm
  let lf : continuousCohomologyZModPLifted p G n →ₗ[ZMod p]
      continuousCohomologyZModPLifted p H n :=
    (continuousCohomologyZModPMapLifted p f n).hom.toLinearMap
  let lg : continuousCohomologyZModPLifted p H n →ₗ[ZMod p]
      continuousCohomologyZModPLifted p G n :=
    (continuousCohomologyZModPMapLifted p g n).hom.toLinearMap
  refine LinearEquiv.ofLinearMap lf lg ?_ ?_
  · ext x
    change ConcreteCategory.hom
        (continuousCohomologyZModPMapLifted p f n)
          (ConcreteCategory.hom
            (continuousCohomologyZModPMapLifted p g n) x) = x
    have hcomp := continuousCohomologyZModPMapLifted_comp p g f n
    have hgf : g.comp f = ContinuousMonoidHom.id H := by
      ext y
      exact e.symm_apply_apply y
    rw [hgf, continuousCohomologyZModPMapLifted_id] at hcomp
    have hx := ConcreteCategory.congr_hom hcomp x
    rw [ConcreteCategory.comp_apply] at hx
    exact hx.symm.trans (ConcreteCategory.id_apply x)
  · ext x
    change ConcreteCategory.hom
        (continuousCohomologyZModPMapLifted p g n)
          (ConcreteCategory.hom
            (continuousCohomologyZModPMapLifted p f n) x) = x
    have hcomp := continuousCohomologyZModPMapLifted_comp p f g n
    have hfg : f.comp g = ContinuousMonoidHom.id G := by
      ext y
      exact e.apply_symm_apply y
    rw [hfg, continuousCohomologyZModPMapLifted_id] at hcomp
    have hx := ConcreteCategory.congr_hom hcomp x
    rw [ConcreteCategory.comp_apply] at hx
    exact hx.symm.trans (ConcreteCategory.id_apply x)

end

end ClassFieldTower.Cohomology

namespace ClassFieldTower.ProP

open ProCGroups

noncomputable section

universe u

variable {p d r : ℕ} [Fact p.Prime]
variable {sourceData :
  FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
    (FiniteGroupClass.pGroup p)}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The topological first-isomorphism equivalence supplied by a finite presentation. -/
noncomputable def FiniteProPPresentation.quotientKerContinuousMulEquiv
    (P : FiniteProPPresentation p d r sourceData G) :
    (sourceData.carrier ⧸
      (P.quotient.toMonoidHom.ker : Subgroup sourceData.carrier)) ≃ₜ* G := by
  let q := P.quotient
  letI : CompactSpace q.toMonoidHom.range :=
    isCompact_iff_compactSpace.mp <| by
      simpa [q] using isCompact_range P.quotient.continuous_toFun
  let er : q.toMonoidHom.range ≃ₜ* G :=
    ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2
      (Subgroup.subtype q.toMonoidHom.range) continuous_subtype_val
      ⟨Subtype.coe_injective, by
        intro g
        rcases P.quotient_surjective g with ⟨f, rfl⟩
        exact ⟨⟨P.quotient f, ⟨f, rfl⟩⟩, rfl⟩⟩
  exact
    (ProCGroups.ContinuousMonoidHom.quotientKerContinuousMulEquivRange q).trans er

end

end ClassFieldTower.ProP

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.Topology.Sober

/-!+# A neighborhood dominated by the actual local spectrum

When a scheme has finitely many irreducible components, deleting the
components which miss a given point gives an open neighborhood dominated
by its actual stalk spectrum. The generic point of each remaining component
is in the range of the stalk map.

This provides compatible shrinking in the local connectedness criteria
without imposing normality or Noetherianity on the local rings.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- Finite irreducible components suffice for the actual stalk spectrum to
dominate some open neighborhood of its center. -/
theorem exists_open_fromSpecStalkOfMem_isDominant
    (X : Scheme.{u}) (hfin : (irreducibleComponents X).Finite) (x : X) :
    ∃ (U : X.Opens) (hxU : x ∈ U), IsDominant (U.fromSpecStalkOfMem x hxU) := by
  let C : Set (Set X) := { Z | Z ∈ irreducibleComponents X ∧ x ∉ Z }
  have hCfin : C.Finite := hfin.subset (fun _ hZ => hZ.1)
  have hCclosed : IsClosed (⋃₀ C) :=
    hCfin.isClosed_sUnion (fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1)
  let U : X.Opens := ⟨(⋃₀ C)ᶜ, hCclosed.isOpen_compl⟩
  have hxU : x ∈ U := by
    rintro ⟨Z, hZ, hxZ⟩
    exact hZ.2 hxZ
  let l : Spec (X.presheaf.stalk x) ⟶ U.toScheme := U.fromSpecStalkOfMem x hxU
  have hcomp : l ≫ U.ι = X.fromSpecStalk x := U.fromSpecStalkOfMem_ι x hxU
  have hrange : U.ι '' Set.range l = Set.range (X.fromSpecStalk x) := by
    rw [← Set.range_comp]
    apply congrArg Set.range
    funext p
    exact congrArg (fun g : Spec (X.presheaf.stalk x) ⟶ X => g p) hcomp
  refine ⟨U, hxU, ⟨?_⟩⟩
  change Dense (Set.range l)
  apply U.ι.isOpenEmbedding.isEmbedding.isInducing.dense_iff.mpr
  intro y
  rw [hrange]
  let Z : Set X := irreducibleComponent y.1
  have hZ : Z ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents y.1
  have hyZ : y.1 ∈ Z := mem_irreducibleComponent
  have hxZ : x ∈ Z := by
    by_contra hxZ
    exact y.2 ⟨Z, ⟨hZ, hxZ⟩, hyZ⟩
  have hη : IsGenericPoint hZ.1.genericPoint Z :=
    hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents Z hZ)
  have hηrange : hZ.1.genericPoint ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact hη.specializes hxZ
  have hZrange : Z ⊆ closure (Set.range (X.fromSpecStalk x)) := by
    rw [← hη.def]
    exact closure_mono (Set.singleton_subset_iff.mpr hηrange)
  exact hZrange hyZ

end AlgebraicGeometry.Scheme

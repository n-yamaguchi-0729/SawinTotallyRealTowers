/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.ConnectedComplement
import Nyll.SchemeTheory.Divisors.ReducedIrreducibleComponentGeometry
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Finite étale reduced components

Domain stalks make irreducible components open on a locally Noetherian scheme.
For a reduced scheme, the reduced closed component then coincides with that open
subscheme. In particular its inclusion is both finite and étale.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

namespace Scheme

/-- Every component is open when all stalks of a locally Noetherian scheme
are domains. -/
theorem isOpen_irreducibleComponent_of_isDomain_stalk
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (hdom : ∀ x : X, IsDomain (X.presheaf.stalk x))
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X) : IsOpen Z := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  let : IsDomain (X.presheaf.stalk x) := hdom x
  obtain ⟨V, hV, hxV, hirred⟩ := exists_isIrreducible_open_of_isDomain_stalk x
  have hZV : Z ⊆ closure V :=
    (subset_closure_inter_of_isPreirreducible_of_isOpen hZ.1.2 hV
      ⟨x, hx, hxV⟩).trans (closure_mono Set.inter_subset_right)
  have hVZ : closure V ⊆ Z := hZ.2 hirred.closure hZV
  exact ⟨V, subset_closure.trans hVZ, hV, hxV⟩

/-- A closed immersion into a reduced scheme is open if its range is open. -/
theorem isOpenImmersion_of_isClosedImmersion_of_isOpen_range
    {X Y : Scheme.{u}} [IsReduced Y] (f : X ⟶ Y) [IsClosedImmersion f]
    (hopen : IsOpen (Set.range f)) : IsOpenImmersion f := by
  let U : Y.Opens := ⟨Set.range f, hopen⟩
  have hrange : Set.range f ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    exact Set.Subset.rfl
  let g : X ⟶ U := IsOpenImmersion.lift U.ι f hrange
  have hcomp : g ≫ U.ι = f := IsOpenImmersion.lift_fac U.ι f hrange
  let : IsClosedImmersion (g ≫ U.ι) := hcomp.symm ▸ inferInstance
  let : IsClosedImmersion g := IsClosedImmersion.of_comp g U.ι
  let : Surjective g := ⟨by
    intro y
    obtain ⟨x, hx⟩ := y.2
    refine ⟨x, Subtype.ext ?_⟩
    exact (congrArg (fun k : X ⟶ Y => k x) hcomp).trans hx⟩
  let : IsIso g := isIso_of_isClosedImmersion_of_surjective g
  rw [← hcomp]
  infer_instance

/-- On a reduced locally Noetherian scheme with domain stalks, the canonical
reduced component inclusion is finite étale. -/
theorem reducedIrreducibleComponentι_isFiniteEtale
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (hdom : ∀ x : X, IsDomain (X.presheaf.stalk x))
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    IsFiniteEtale (X.reducedIrreducibleComponentι Z hZ) := by
  let (x : X) : _root_.IsReduced (X.presheaf.stalk x) := by
    let : IsDomain (X.presheaf.stalk x) := hdom x
    infer_instance
  let : IsReduced X := isReduced_of_isReduced_stalk X
  let i : X.reducedIrreducibleComponent Z hZ ⟶ X :=
    X.reducedIrreducibleComponentι Z hZ
  have hopen : IsOpen (Set.range i) := by
    rw [show Set.range i = Z from range_reducedIrreducibleComponentι X Z hZ]
    exact isOpen_irreducibleComponent_of_isDomain_stalk X hdom Z hZ
  let : IsOpenImmersion i := isOpenImmersion_of_isClosedImmersion_of_isOpen_range i hopen
  change IsFiniteEtale i
  exact IsFiniteEtale.mk

end Scheme

end AlgebraicGeometry

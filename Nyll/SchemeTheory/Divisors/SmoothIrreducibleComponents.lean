/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.EtaleIrreducibleComponentMap
import Nyll.SchemeTheory.LocalGeometry.SmoothStalkNormality
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Components smooth over a normal affine base

The local normality theorem for smooth morphisms supplies the domain stalks
needed to identify reduced irreducible components as finite étale covers.
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

/-- A reduced irreducible component of a scheme smooth over a normal affine
Noetherian integral base is open and closed. -/
theorem reducedIrreducibleComponentι_isFiniteEtale_of_smooth
    {X S : Scheme.{u}} [IsAffine S] [IsLocallyNoetherian S]
    [IsDomain Γ(S, ⊤)] [IsIntegrallyClosed Γ(S, ⊤)]
    (p : X ⟶ S) [Smooth p]
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    IsFiniteEtale (X.reducedIrreducibleComponentι Z hZ) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  exact reducedIrreducibleComponentι_isFiniteEtale X
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk p x).1) Z hZ

/-- A finite étale morphism remains finite étale on reduced components above
a component that is smooth over a normal affine Noetherian integral base. -/
theorem reducedIrreducibleComponentMap_isFiniteEtale_of_smooth
    {X Y S : Scheme.{u}} [IsAffine S] [IsLocallyNoetherian S]
    [IsDomain Γ(S, ⊤)] [IsIntegrallyClosed Γ(S, ⊤)]
    (f : X ⟶ Y) [IsFiniteEtale f] (p : Y ⟶ S)
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X)
    (W : Set Y) (hW : W ∈ irreducibleComponents Y)
    (himage : f '' Z = W)
    [Smooth (Y.reducedIrreducibleComponentι W hW ≫ p)] :
    IsFiniteEtale (X.reducedIrreducibleComponentMap f Z hZ W hW himage) := by
  let i : Y.reducedIrreducibleComponent W hW ⟶ Y :=
    Y.reducedIrreducibleComponentι W hW
  let P : Scheme.{u} := pullback f i
  let q : P ⟶ S := pullback.snd f i ≫ i ≫ p
  let : Smooth q := inferInstance
  let : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian q
  exact reducedIrreducibleComponentMap_isFiniteEtale f Z hZ W hW himage
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk q x).1)

end AlgebraicGeometry.Scheme

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldAxiom
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteExtensionClassFieldAxiom
public import Nyll.GaloisCohomology.Cyclic.NormKernelVanishing
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TateTransport

/-!
# The local multiplicative group satisfies the class-field axiom

For a finite cyclic abstract tower `L / K / k`, the closed subgroups are
replaced by their concrete fixed fields.  The lower fixed field is finite
over the local ground field and the upper fixed field is finite Galois over
it.  The finite-tower form of the local class-field-axiom theorem therefore
applies.  The fixed unit representation and cyclic Tate-complex comparisons
then transport its two cardinality statements back to the abstract
class-field-axiom predicate.
-/

@[expose] public section

namespace LocalClassFieldTheory
open CyclicCohomology ClassFormation

open LocalFieldTheory



noncomputable section

open CategoryTheory

universe u v

/-- **The local class-field-axiom theorem, abstract class-field-axiom form.**

For any Galois ambient field over a nonarchimedean local field, its ambient
unit representation satisfies the abstract class-field-axiom predicate.
The predicate ranges only over towers whose lower field is finite over the
distinguished base, in the fixed-separable-closure model. -/
private theorem galoisAmbientUnits_satisfiesClassFieldAxiom
    (k : Type u) (Ω : Type v) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    SatisfiesClassFieldAxiom (galoisAmbientUnitsRep k Ω) := by
  intro B C
  let H := B.field
  let J := C.field
  let hJH := C.below
  let Q := H.toSubgroup ⧸ extensionSubgroup H J hJH
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Q)
  let F := abstractFixedField k Ω H
  let E := abstractRelativeFixedField k Ω hJH
  let : FiniteDimensional k F := abstractFixedField_finiteDimensional k Ω H B.finite
  let : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional k Ω H J hJH B.finite C.finite
  let : IsGalois F E := abstractRelativeFixedField_isGalois k Ω H J hJH C.normal
  let eQ : Q ≃* Gal(E/F) := abstractExtensionQuotientEquivGaloisGroup k Ω H J hJH C.normal
  have hg' : ∀ σ : Gal(E/F), σ ∈ Subgroup.zpowers (eQ g) :=
    map_cyclicGenerator eQ g hg
  let U := Rep.ofAlgebraAutOnUnits F E
  let eM : C.fixedRepresentation (galoisAmbientUnitsRep k Ω) ≅ Rep.res eQ.toMonoidHom U :=
    abstractExtensionFixedRepresentationIsoUnitsRes k Ω H J hJH C.normal
  have hUnits := finiteTowerUnits_tate_card_of_generator k F E (eQ g) hg'
  have hdegree : Module.finrank F E = Nat.card Gal(E/F) :=
    (IsGalois.card_aut_eq_finrank F E).symm
  exact ClassFieldAxiomCohomologyData.of_repIso (galoisAmbientUnitsRep k Ω) B C
    g hg eQ hg' U eM hUnits.finiteH0 (hUnits.cardH0.trans hdegree) hUnits.cardHminusOne

/-- The coefficient module A = (kˢᵉᵖ)ˣ satisfies the abstract
class-field axiom.  This is the separable-closure specialization used for local
reciprocity. -/
theorem separableClosureUnits_isClassFormation
    (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] :
    SatisfiesClassFieldAxiom
      (galoisAmbientUnitsRep k (SeparableClosure k)) :=
  galoisAmbientUnits_satisfiesClassFieldAxiom k (SeparableClosure k)

end
end LocalClassFieldTheory
